//! Private domain-separated physical record journal.

use super::{AppendReceipt, AppendStatus, JournalOptions, SyncPolicy, TornTailPolicy};
use std::fmt;
use std::fs::{File, OpenOptions, TryLockError};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

const MARKER_BYTES: usize = 8;
const U64_BYTES: usize = 8;
const HASH_BYTES: usize = 32;
const HEADER_BYTES: usize = MARKER_BYTES + U64_BYTES + U64_BYTES + HASH_BYTES;

#[derive(Debug, Clone, Copy)]
pub(crate) struct RecordSpec {
    pub marker: [u8; MARKER_BYTES],
    pub hash_domain: &'static [u8],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RawOpenReport {
    pub recovered_records: usize,
    pub truncated_bytes: u64,
    pub created: bool,
}

#[derive(Debug)]
pub(crate) enum RawJournalError {
    Io(io::Error),
    Locked,
    TornTail {
        offset: u64,
        bytes: u64,
    },
    Corrupt {
        sequence: u64,
        offset: u64,
        reason: &'static str,
    },
    RecordTooLarge {
        actual: u64,
        maximum: u64,
    },
    SequenceGap {
        expected: u64,
        requested: u64,
    },
    SequenceConflict {
        sequence: u64,
    },
    SequenceExhausted,
    Poisoned,
}

impl fmt::Display for RawJournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(source) => write!(f, "journal I/O failed: {source}"),
            Self::Locked => write!(f, "journal already has a live writer"),
            Self::TornTail { offset, bytes } => {
                write!(f, "journal has a {bytes}-byte torn tail at byte {offset}")
            }
            Self::Corrupt {
                sequence,
                offset,
                reason,
            } => write!(
                f,
                "journal record {sequence} is corrupt at byte {offset}: {reason}"
            ),
            Self::RecordTooLarge { actual, maximum } => write!(
                f,
                "journal record is {actual} bytes; configured maximum is {maximum}"
            ),
            Self::SequenceGap {
                expected,
                requested,
            } => write!(
                f,
                "journal sequence gap: expected {expected}, requested {requested}"
            ),
            Self::SequenceConflict { sequence } => write!(
                f,
                "journal sequence {sequence} already contains different bytes"
            ),
            Self::SequenceExhausted => write!(f, "journal sequence space is exhausted"),
            Self::Poisoned => write!(
                f,
                "journal append state is uncertain after an I/O failure; reopen it"
            ),
        }
    }
}

impl std::error::Error for RawJournalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(source) => Some(source),
            _ => None,
        }
    }
}

impl From<io::Error> for RawJournalError {
    fn from(source: io::Error) -> Self {
        Self::Io(source)
    }
}

#[derive(Debug)]
pub(crate) struct RawJournal {
    path: PathBuf,
    file: File,
    records: Vec<Vec<u8>>,
    spec: RecordSpec,
    options: JournalOptions,
    poisoned: bool,
    report: RawOpenReport,
}

impl RawJournal {
    pub(crate) fn open(
        path: impl AsRef<Path>,
        spec: RecordSpec,
        options: JournalOptions,
    ) -> Result<Self, RawJournalError> {
        if options.max_record_bytes == 0 {
            return Err(RawJournalError::RecordTooLarge {
                actual: 1,
                maximum: 0,
            });
        }
        let path = path.as_ref().to_path_buf();
        let (mut file, created) = match OpenOptions::new()
            .create_new(true)
            .read(true)
            .append(true)
            .open(&path)
        {
            Ok(file) => (file, true),
            Err(source) if source.kind() == io::ErrorKind::AlreadyExists => (
                OpenOptions::new().read(true).append(true).open(&path)?,
                false,
            ),
            Err(source) => return Err(RawJournalError::Io(source)),
        };
        match file.try_lock() {
            Ok(()) => {}
            Err(TryLockError::WouldBlock) => return Err(RawJournalError::Locked),
            Err(TryLockError::Error(source)) => return Err(RawJournalError::Io(source)),
        }
        if options.sync == SyncPolicy::SyncAll {
            sync_parent(&path)?;
        }

        let file_len = file.metadata()?.len();
        let (records, valid_bytes, torn_bytes) = scan(&mut file, file_len, spec, options)?;
        if torn_bytes != 0 {
            match options.torn_tail {
                TornTailPolicy::Refuse => {
                    return Err(RawJournalError::TornTail {
                        offset: valid_bytes,
                        bytes: torn_bytes,
                    });
                }
                TornTailPolicy::Truncate => {
                    file.set_len(valid_bytes)?;
                    apply_sync(&mut file, options.sync)?;
                }
            }
        }
        file.seek(SeekFrom::End(0))?;
        let report = RawOpenReport {
            recovered_records: records.len(),
            truncated_bytes: torn_bytes,
            created,
        };
        Ok(Self {
            path,
            file,
            records,
            spec,
            options,
            poisoned: false,
            report,
        })
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) fn report(&self) -> RawOpenReport {
        self.report
    }

    pub(crate) fn records(&self) -> &[Vec<u8>] {
        &self.records
    }

    pub(crate) fn next_sequence(&self) -> u64 {
        self.records.len() as u64
    }

    pub(crate) fn append_at(
        &mut self,
        requested: u64,
        body: &[u8],
    ) -> Result<AppendReceipt, RawJournalError> {
        if self.poisoned {
            return Err(RawJournalError::Poisoned);
        }
        let body_len = u64::try_from(body.len()).map_err(|_| RawJournalError::RecordTooLarge {
            actual: u64::MAX,
            maximum: self.options.max_record_bytes,
        })?;
        if body_len > self.options.max_record_bytes {
            return Err(RawJournalError::RecordTooLarge {
                actual: body_len,
                maximum: self.options.max_record_bytes,
            });
        }
        let next = self.next_sequence();
        if requested < next {
            let existing = &self.records[requested as usize];
            return if existing.as_slice() == body {
                // The original write may have completed before its requested
                // sync failed. Byte equality alone is therefore not a
                // successful retry: repeat the durability action too.
                if let Err(source) = apply_sync(&mut self.file, self.options.sync) {
                    self.poisoned = true;
                    return Err(RawJournalError::Io(source));
                }
                Ok(AppendReceipt {
                    sequence: requested,
                    status: AppendStatus::AlreadyPresent,
                })
            } else {
                Err(RawJournalError::SequenceConflict {
                    sequence: requested,
                })
            };
        }
        if requested > next {
            return Err(RawJournalError::SequenceGap {
                expected: next,
                requested,
            });
        }
        if requested == u64::MAX {
            return Err(RawJournalError::SequenceExhausted);
        }

        let header = encode_header(self.spec, requested, body_len);
        let checksum = body_hash(self.spec, requested, body_len, body);
        let write_result = (|| -> io::Result<()> {
            self.file.write_all(&header)?;
            self.file.write_all(body)?;
            self.file.write_all(checksum.as_bytes())?;
            apply_sync(&mut self.file, self.options.sync)
        })();
        if let Err(source) = write_result {
            self.poisoned = true;
            return Err(RawJournalError::Io(source));
        }
        self.records.push(body.to_vec());
        Ok(AppendReceipt {
            sequence: requested,
            status: AppendStatus::Appended,
        })
    }

    pub(crate) fn sync(&mut self, policy: SyncPolicy) -> Result<(), RawJournalError> {
        if self.poisoned {
            return Err(RawJournalError::Poisoned);
        }
        if let Err(source) = apply_sync(&mut self.file, policy) {
            self.poisoned = true;
            return Err(RawJournalError::Io(source));
        }
        Ok(())
    }
}

fn scan(
    file: &mut File,
    file_len: u64,
    spec: RecordSpec,
    options: JournalOptions,
) -> Result<(Vec<Vec<u8>>, u64, u64), RawJournalError> {
    file.seek(SeekFrom::Start(0))?;
    let mut records = Vec::new();
    let mut offset = 0u64;
    while offset < file_len {
        let expected = records.len() as u64;
        let remaining = file_len - offset;
        if remaining < HEADER_BYTES as u64 {
            let mut partial = vec![0; remaining as usize];
            file.read_exact(&mut partial)?;
            validate_partial_header(&partial, spec, expected, options.max_record_bytes).map_err(
                |reason| RawJournalError::Corrupt {
                    sequence: expected,
                    offset,
                    reason,
                },
            )?;
            return Ok((records, offset, remaining));
        }

        let mut header = [0u8; HEADER_BYTES];
        file.read_exact(&mut header)?;
        if header[..MARKER_BYTES] != spec.marker {
            return Err(RawJournalError::Corrupt {
                sequence: expected,
                offset,
                reason: "wrong physical record marker",
            });
        }
        let sequence = u64::from_le_bytes(header[8..16].try_into().expect("fixed slice"));
        if sequence != expected {
            return Err(RawJournalError::Corrupt {
                sequence: expected,
                offset,
                reason: "non-contiguous physical record sequence",
            });
        }
        let body_len = u64::from_le_bytes(header[16..24].try_into().expect("fixed slice"));
        if body_len > options.max_record_bytes {
            return Err(RawJournalError::RecordTooLarge {
                actual: body_len,
                maximum: options.max_record_bytes,
            });
        }
        let expected_header = header_hash(spec, sequence, body_len);
        if header[24..HEADER_BYTES] != *expected_header.as_bytes() {
            return Err(RawJournalError::Corrupt {
                sequence,
                offset,
                reason: "physical record header checksum mismatch",
            });
        }
        let total = (HEADER_BYTES as u64)
            .checked_add(body_len)
            .and_then(|n| n.checked_add(HASH_BYTES as u64))
            .ok_or(RawJournalError::RecordTooLarge {
                actual: body_len,
                maximum: options.max_record_bytes,
            })?;
        let bytes_after_header = remaining - HEADER_BYTES as u64;
        if bytes_after_header < body_len {
            return Ok((records, offset, remaining));
        }

        let body_size = usize::try_from(body_len).map_err(|_| RawJournalError::RecordTooLarge {
            actual: body_len,
            maximum: options.max_record_bytes,
        })?;
        let mut body = vec![0; body_size];
        file.read_exact(&mut body)?;
        let checksum_bytes = bytes_after_header - body_len;
        if checksum_bytes < HASH_BYTES as u64 {
            let mut checksum_prefix = vec![0; checksum_bytes as usize];
            file.read_exact(&mut checksum_prefix)?;
            let expected_checksum = body_hash(spec, sequence, body_len, &body);
            if checksum_prefix != expected_checksum.as_bytes()[..checksum_prefix.len()] {
                return Err(RawJournalError::Corrupt {
                    sequence,
                    offset,
                    reason: "partial physical record body checksum mismatch",
                });
            }
            return Ok((records, offset, remaining));
        }
        let mut checksum = [0u8; HASH_BYTES];
        file.read_exact(&mut checksum)?;
        let expected_checksum = body_hash(spec, sequence, body_len, &body);
        if checksum != *expected_checksum.as_bytes() {
            return Err(RawJournalError::Corrupt {
                sequence,
                offset,
                reason: "physical record body checksum mismatch",
            });
        }
        records.push(body);
        offset += total;
    }
    Ok((records, offset, 0))
}

fn validate_partial_header(
    bytes: &[u8],
    spec: RecordSpec,
    expected_sequence: u64,
    max_record_bytes: u64,
) -> Result<(), &'static str> {
    let marker_len = bytes.len().min(MARKER_BYTES);
    if bytes[..marker_len] != spec.marker[..marker_len] {
        return Err("final short suffix is not a physical record prefix");
    }
    if bytes.len() > MARKER_BYTES {
        let sequence = expected_sequence.to_le_bytes();
        let seq_len = (bytes.len() - MARKER_BYTES).min(U64_BYTES);
        if bytes[MARKER_BYTES..MARKER_BYTES + seq_len] != sequence[..seq_len] {
            return Err("final short suffix has the wrong record sequence");
        }
    }
    if bytes.len() > MARKER_BYTES + U64_BYTES {
        let length_start = MARKER_BYTES + U64_BYTES;
        let length_bytes = (bytes.len() - length_start).min(U64_BYTES);
        let mut minimum_length = [0u8; U64_BYTES];
        minimum_length[..length_bytes]
            .copy_from_slice(&bytes[length_start..length_start + length_bytes]);
        let minimum_length = u64::from_le_bytes(minimum_length);
        if minimum_length > max_record_bytes {
            return Err("partial physical record length exceeds configured maximum");
        }
        if length_bytes == U64_BYTES && bytes.len() > length_start + U64_BYTES {
            let expected = header_hash(spec, expected_sequence, minimum_length);
            let checksum = &bytes[length_start + U64_BYTES..];
            if checksum != &expected.as_bytes()[..checksum.len()] {
                return Err("partial physical record header checksum mismatch");
            }
        }
    }
    Ok(())
}

fn encode_header(spec: RecordSpec, sequence: u64, body_len: u64) -> [u8; HEADER_BYTES] {
    let mut header = [0u8; HEADER_BYTES];
    header[..8].copy_from_slice(&spec.marker);
    header[8..16].copy_from_slice(&sequence.to_le_bytes());
    header[16..24].copy_from_slice(&body_len.to_le_bytes());
    header[24..].copy_from_slice(header_hash(spec, sequence, body_len).as_bytes());
    header
}

fn header_hash(spec: RecordSpec, sequence: u64, body_len: u64) -> blake3::Hash {
    let mut hasher = blake3::Hasher::new();
    hasher.update(spec.hash_domain);
    hasher.update(b".header\0");
    hasher.update(&spec.marker);
    hasher.update(&sequence.to_le_bytes());
    hasher.update(&body_len.to_le_bytes());
    hasher.finalize()
}

fn body_hash(spec: RecordSpec, sequence: u64, body_len: u64, body: &[u8]) -> blake3::Hash {
    let mut hasher = blake3::Hasher::new();
    hasher.update(spec.hash_domain);
    hasher.update(b".body\0");
    hasher.update(&spec.marker);
    hasher.update(&sequence.to_le_bytes());
    hasher.update(&body_len.to_le_bytes());
    hasher.update(body);
    hasher.finalize()
}

pub(crate) fn apply_sync(file: &mut File, policy: SyncPolicy) -> io::Result<()> {
    match policy {
        SyncPolicy::Buffered => Ok(()),
        SyncPolicy::Flush => file.flush(),
        SyncPolicy::SyncData => {
            file.flush()?;
            file.sync_data()
        }
        SyncPolicy::SyncAll => {
            file.flush()?;
            file.sync_all()
        }
    }
}

fn sync_parent(path: &Path) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        let parent = if parent.as_os_str().is_empty() {
            Path::new(".")
        } else {
            parent
        };
        File::open(parent)?.sync_all()?;
    }
    Ok(())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::fd::OwnedFd;
    use std::os::unix::net::UnixStream;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

    fn test_spec() -> RecordSpec {
        RecordSpec {
            marker: *b"UWTEST01",
            hash_domain: b"uwueave.test.retry-sync.v1",
        }
    }

    #[test]
    fn sync_all_accepts_a_bare_relative_new_journal_path() {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = PathBuf::from(format!(
            ".uwueave-relative-syncall-{}-{nonce}.journal",
            std::process::id()
        ));
        let _ = std::fs::remove_file(&path);
        let journal = RawJournal::open(
            &path,
            test_spec(),
            JournalOptions {
                torn_tail: TornTailPolicy::Refuse,
                sync: SyncPolicy::SyncAll,
                max_record_bytes: 1024,
            },
        )
        .unwrap();
        assert!(journal.report().created);
        drop(journal);
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn idempotent_retry_repeats_sync_and_poisons_on_sync_failure() {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-raw-retry-sync-{}-{nonce}.journal",
            std::process::id()
        ));
        let _ = std::fs::remove_file(&path);
        let mut journal = RawJournal::open(
            &path,
            test_spec(),
            JournalOptions {
                torn_tail: TornTailPolicy::Refuse,
                sync: SyncPolicy::Buffered,
                max_record_bytes: 1024,
            },
        )
        .unwrap();
        journal.append_at(0, b"accepted").unwrap();

        // A socket is a valid owned File descriptor but `sync_data` refuses
        // it. Replacing only the private test handle makes the sync attempt
        // observable without relying on a particular filesystem failure.
        let (socket, _peer) = UnixStream::pair().unwrap();
        let socket_fd: OwnedFd = socket.into();
        journal.file = File::from(socket_fd);
        journal.options.sync = SyncPolicy::SyncData;
        assert!(matches!(
            journal.append_at(0, b"accepted"),
            Err(RawJournalError::Io(_))
        ));
        assert!(matches!(
            journal.append_at(0, b"accepted"),
            Err(RawJournalError::Poisoned)
        ));
        let _ = std::fs::remove_file(path);
    }
}
