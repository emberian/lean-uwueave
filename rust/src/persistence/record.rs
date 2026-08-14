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

/// Result of parsing one immutable physical journal image.
///
/// This is a byte-codec result, not evidence that a filesystem or storage
/// device can produce only prefix-shaped crash images.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RawScan {
    pub records: Vec<Vec<u8>>,
    pub valid_bytes: u64,
    pub torn_bytes: u64,
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
        let RawScan {
            records,
            valid_bytes,
            torn_bytes,
        } = scan_image(&mut file, file_len, spec, options.max_record_bytes)?;
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

        let record = encode_record(self.spec, requested, body, self.options.max_record_bytes)?;
        let write_result = (|| -> io::Result<()> {
            self.file.write_all(&record)?;
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

/// Encode one complete physical record while preserving `body` byte-for-byte.
/// The returned image is the exact production image passed to `write_all`.
/// No filesystem, synchronization, or power-loss behavior is implied.
pub(crate) fn encode_record(
    spec: RecordSpec,
    sequence: u64,
    body: &[u8],
    max_record_bytes: u64,
) -> Result<Vec<u8>, RawJournalError> {
    let body_len = u64::try_from(body.len()).map_err(|_| RawJournalError::RecordTooLarge {
        actual: u64::MAX,
        maximum: max_record_bytes,
    })?;
    if body_len > max_record_bytes {
        return Err(RawJournalError::RecordTooLarge {
            actual: body_len,
            maximum: max_record_bytes,
        });
    }

    let capacity = HEADER_BYTES
        .checked_add(body.len())
        .and_then(|length| length.checked_add(HASH_BYTES))
        .ok_or_else(|| {
            RawJournalError::Io(io::Error::new(
                io::ErrorKind::InvalidInput,
                "physical record framing length overflows the address space",
            ))
        })?;
    let header = encode_header(spec, sequence, body_len);
    let checksum = body_hash(spec, sequence, body_len, body);
    let mut record = Vec::new();
    record.try_reserve_exact(capacity).map_err(|_| {
        RawJournalError::Io(io::Error::other(
            "physical record framing allocation failed",
        ))
    })?;
    record.extend_from_slice(&header);
    record.extend_from_slice(body);
    record.extend_from_slice(checksum.as_bytes());
    Ok(record)
}

/// Parse one supplied physical journal image into exact complete record bodies
/// plus at most one syntactically matching final-record prefix.
///
/// The production path supplies its locked file and measured length; pure
/// codec tests supply a `Cursor<&[u8]>`. Acceptance proves only a property of
/// those supplied bytes, not that a real crash, flush, filesystem, or storage
/// device must yield such an image.
///
/// No individual allocation or read request is based on the full image length:
/// each body read is bounded by `max_record_bytes`. Complete bodies are retained
/// in the result, as they were by the original streaming scanner.
pub(crate) fn scan_image<R: Read + Seek>(
    reader: &mut R,
    image_len: u64,
    spec: RecordSpec,
    max_record_bytes: u64,
) -> Result<RawScan, RawJournalError> {
    reader.seek(SeekFrom::Start(0))?;
    let mut records = Vec::new();
    let mut offset = 0u64;
    while offset < image_len {
        let expected = records.len() as u64;
        let remaining = image_len - offset;
        if remaining < HEADER_BYTES as u64 {
            let mut partial = vec![0; remaining as usize];
            reader.read_exact(&mut partial)?;
            validate_partial_header(&partial, spec, expected, max_record_bytes).map_err(
                |reason| RawJournalError::Corrupt {
                    sequence: expected,
                    offset,
                    reason,
                },
            )?;
            return Ok(RawScan {
                records,
                valid_bytes: offset,
                torn_bytes: remaining,
            });
        }

        let mut header = [0u8; HEADER_BYTES];
        reader.read_exact(&mut header)?;
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
        if body_len > max_record_bytes {
            return Err(RawJournalError::RecordTooLarge {
                actual: body_len,
                maximum: max_record_bytes,
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
                maximum: max_record_bytes,
            })?;
        let bytes_after_header = remaining - HEADER_BYTES as u64;
        if bytes_after_header < body_len {
            return Ok(RawScan {
                records,
                valid_bytes: offset,
                torn_bytes: remaining,
            });
        }

        let body_size = usize::try_from(body_len).map_err(|_| RawJournalError::RecordTooLarge {
            actual: body_len,
            maximum: max_record_bytes,
        })?;
        let mut body = vec![0; body_size];
        reader.read_exact(&mut body)?;
        let checksum_bytes = bytes_after_header - body_len;
        if checksum_bytes < HASH_BYTES as u64 {
            let mut checksum_prefix = vec![0; checksum_bytes as usize];
            reader.read_exact(&mut checksum_prefix)?;
            let expected_checksum = body_hash(spec, sequence, body_len, &body);
            if checksum_prefix != expected_checksum.as_bytes()[..checksum_prefix.len()] {
                return Err(RawJournalError::Corrupt {
                    sequence,
                    offset,
                    reason: "partial physical record body checksum mismatch",
                });
            }
            return Ok(RawScan {
                records,
                valid_bytes: offset,
                torn_bytes: remaining,
            });
        }
        let mut checksum = [0u8; HASH_BYTES];
        reader.read_exact(&mut checksum)?;
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
    Ok(RawScan {
        records,
        valid_bytes: offset,
        torn_bytes: 0,
    })
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

#[cfg(test)]
#[path = "debt_u_0170.rs"]
mod debt_u_0170;

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

#[cfg(test)]
mod codec_tests {
    use super::*;
    use std::io::Cursor;

    const TEST_MAX: u64 = 257;

    fn test_spec() -> RecordSpec {
        RecordSpec {
            marker: *b"UWCODEC1",
            hash_domain: b"uwueave.test.physical-codec.v1",
        }
    }

    fn scan_bytes(bytes: &[u8], maximum: u64) -> Result<RawScan, RawJournalError> {
        scan_image(
            &mut Cursor::new(bytes),
            bytes.len() as u64,
            test_spec(),
            maximum,
        )
    }

    #[test]
    fn physical_codec_preserves_exact_bodies_order_and_length_boundaries() {
        let lengths = [0usize, 1, 31, 32, 55, 56, 57, TEST_MAX as usize];
        let bodies: Vec<Vec<u8>> = lengths
            .into_iter()
            .enumerate()
            .map(|(seed, length)| {
                (0..length)
                    .map(|offset| (seed as u8).wrapping_mul(37).wrapping_add(offset as u8))
                    .collect()
            })
            .collect();
        let mut image = Vec::new();
        for (sequence, body) in bodies.iter().enumerate() {
            let record = encode_record(test_spec(), sequence as u64, body, TEST_MAX).unwrap();
            assert_eq!(record.len(), HEADER_BYTES + body.len() + HASH_BYTES);
            assert_eq!(&record[HEADER_BYTES..HEADER_BYTES + body.len()], body);
            image.extend_from_slice(&record);
        }

        let scan = scan_bytes(&image, TEST_MAX).unwrap();
        assert_eq!(scan.records, bodies);
        assert_eq!(scan.valid_bytes, image.len() as u64);
        assert_eq!(scan.torn_bytes, 0);

        let oversized = vec![0; TEST_MAX as usize + 1];
        assert!(matches!(
            encode_record(test_spec(), 0, &oversized, TEST_MAX),
            Err(RawJournalError::RecordTooLarge {
                actual,
                maximum: TEST_MAX
            }) if actual == TEST_MAX + 1
        ));
        let oversized_image = encode_record(test_spec(), 0, &oversized, TEST_MAX + 1).unwrap();
        assert!(matches!(
            scan_bytes(&oversized_image, TEST_MAX),
            Err(RawJournalError::RecordTooLarge {
                actual,
                maximum: TEST_MAX
            }) if actual == TEST_MAX + 1
        ));
    }

    #[test]
    fn every_strict_final_record_cut_recovers_only_complete_bodies() {
        let first = b"first exact body".to_vec();
        let second = Vec::new();
        let third: Vec<u8> = (0..TEST_MAX).map(|byte| byte as u8).collect();
        let mut prefix = encode_record(test_spec(), 0, &first, TEST_MAX).unwrap();
        prefix.extend_from_slice(&encode_record(test_spec(), 1, &second, TEST_MAX).unwrap());
        let third_record = encode_record(test_spec(), 2, &third, TEST_MAX).unwrap();

        for cut in 0..third_record.len() {
            let mut image = prefix.clone();
            image.extend_from_slice(&third_record[..cut]);
            let scan = scan_bytes(&image, TEST_MAX).unwrap();
            assert_eq!(scan.records, [first.clone(), second.clone()], "cut {cut}");
            assert_eq!(scan.valid_bytes, prefix.len() as u64, "cut {cut}");
            assert_eq!(scan.torn_bytes, cut as u64, "cut {cut}");
        }
    }

    #[test]
    fn physical_corruption_is_never_reclassified_as_a_torn_prefix() {
        let body = b"body whose exact bytes are checksummed";
        let complete = encode_record(test_spec(), 0, body, TEST_MAX).unwrap();
        let body_start = HEADER_BYTES;
        let checksum_start = body_start + body.len();

        for index in [0, 8, 24, body_start, complete.len() - 1] {
            let mut corrupt = complete.clone();
            corrupt[index] ^= 0x80;
            assert!(matches!(
                scan_bytes(&corrupt, TEST_MAX),
                Err(RawJournalError::Corrupt { sequence: 0, .. })
            ));
        }

        for checksum_start in [MARKER_BYTES + U64_BYTES + U64_BYTES, checksum_start] {
            for checksum_prefix in 1..HASH_BYTES {
                let mut corrupt = complete[..checksum_start + checksum_prefix].to_vec();
                *corrupt.last_mut().unwrap() ^= 0x80;
                assert!(matches!(
                    scan_bytes(&corrupt, TEST_MAX),
                    Err(RawJournalError::Corrupt { sequence: 0, .. })
                ));
            }
        }

        let first = encode_record(test_spec(), 0, b"first", TEST_MAX).unwrap();
        let mut middle = encode_record(test_spec(), 1, b"middle", TEST_MAX).unwrap();
        middle[HEADER_BYTES] ^= 0x40;
        let third = encode_record(test_spec(), 2, b"third", TEST_MAX).unwrap();
        let mut image = first.clone();
        image.extend_from_slice(&middle);
        image.extend_from_slice(&third);
        assert!(matches!(
            scan_bytes(&image, TEST_MAX),
            Err(RawJournalError::Corrupt {
                sequence: 1,
                offset,
                ..
            }) if offset == first.len() as u64
        ));
    }

    struct BoundedRead<R> {
        inner: R,
        largest_request: usize,
    }

    impl<R: Read> Read for BoundedRead<R> {
        fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
            self.largest_request = self.largest_request.max(buffer.len());
            self.inner.read(buffer)
        }
    }

    impl<R: Seek> Seek for BoundedRead<R> {
        fn seek(&mut self, position: SeekFrom) -> io::Result<u64> {
            self.inner.seek(position)
        }
    }

    #[test]
    fn production_scanner_never_requests_the_whole_large_image() {
        let body = vec![0x5a; TEST_MAX as usize];
        let mut image = Vec::new();
        for sequence in 0..1024 {
            image
                .extend_from_slice(&encode_record(test_spec(), sequence, &body, TEST_MAX).unwrap());
        }
        let mut reader = BoundedRead {
            inner: Cursor::new(&image),
            largest_request: 0,
        };
        let scan = scan_image(&mut reader, image.len() as u64, test_spec(), TEST_MAX).unwrap();
        assert_eq!(scan.records.len(), 1024);
        assert_eq!(scan.valid_bytes, image.len() as u64);
        assert_eq!(scan.torn_bytes, 0);
        assert!(reader.largest_request <= TEST_MAX as usize);
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
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
}
