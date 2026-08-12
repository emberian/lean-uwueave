//! Exact-byte persistence for Preoscript `ArtifactDurable` format v2.
//!
//! The logical import/export stream is exactly a concatenation of Lean-owned
//! artifact frames:
//!
//! ```text
//! d5 4a 02 a1 (00 payload-byte)* 01
//! ```
//!
//! The physical file wraps each unchanged frame in a `UWARJ001` record with an
//! internal sequence, checked length, header checksum, and body checksum. This
//! lets the host detect stored-record corruption without changing the exported
//! frame. BLAKE3 is an integrity control here, not authentication or a
//! Lean-proved cryptographic claim.
//!
//! There is deliberately no Rust implementation of the artifact payload
//! codec. [`ArtifactFrame`] first classifies the outer envelope, then calls a
//! narrow Lean validator for exact canonical payload acceptance. A mutation
//! from one canonical payload to another cannot be identified as a mutation by
//! a logical stream alone, but the physical checksum detects it unless an
//! adversary can also rewrite the checksum.

use super::record::{RawJournal, RawJournalError, RecordSpec};
use super::{AppendReceipt, JournalOptions, SyncPolicy};
use crate::ffi;
use std::fmt;
use std::io;
use std::path::Path;

const MAGIC_0: u8 = 213;
const MAGIC_1: u8 = 74;
const DATA_TAG: u8 = 0;
const END_TAG: u8 = 1;

/// The only artifact format version this implementation accepts.
pub const ARTIFACT_FORMAT_VERSION: u8 = 2;
/// The `preoscript-artifact` domain byte from `Preo.ArtifactDurable`.
pub const ARTIFACT_DOMAIN: u8 = 161;
/// Largest exact artifact frame admitted to Lean for canonical validation.
///
/// The Lean adapter converts its `ByteArray` to the list-based durable codec,
/// so its transient allocation is substantially larger than the wire bytes.
/// This bound is deliberately separate from the physical journal record bound
/// and is checked before crossing the FFI boundary.
pub const MAX_ARTIFACT_FRAME_BYTES: usize = 1024 * 1024;

const RECORD_SPEC: RecordSpec = RecordSpec {
    marker: *b"UWARJ001",
    hash_domain: b"uwueave.artifact-journal.v1",
};

/// Why bytes are not exactly one format-v2 artifact frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArtifactFrameError {
    /// The frame exceeds the host-side ceiling for Lean validation.
    TooLarge { actual: usize, maximum: usize },
    /// The bytes end at a syntactically valid pre-terminator stopping point.
    Torn,
    /// The first magic byte differs from `Durable.magic₀`.
    WrongMagic0 { actual: u8 },
    /// The second magic byte differs from `Durable.magic₁`.
    WrongMagic1 { actual: u8 },
    /// A complete header names a different semantic version.
    WrongVersion { actual: u8 },
    /// A complete header names a different domain.
    WrongDomain { actual: u8 },
    /// A body tag is neither `dataTag` nor `endTag`.
    UnknownBodyTag { offset: usize, actual: u8 },
    /// A complete frame is followed by bytes that belong to another frame.
    TrailingBytes { offset: usize },
    /// The v2 envelope is exact but Lean's canonical `ArtifactEncoding`
    /// decoder refuses its opaque payload.
    NonCanonicalPayload,
}

impl fmt::Display for ArtifactFrameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLarge { actual, maximum } => write!(
                f,
                "artifact frame is {actual} bytes; Lean-validation maximum is {maximum}"
            ),
            Self::Torn => write!(f, "artifact frame is torn before its terminator"),
            Self::WrongMagic0 { actual } => {
                write!(f, "wrong first artifact magic byte: {actual:#04x}")
            }
            Self::WrongMagic1 { actual } => {
                write!(f, "wrong second artifact magic byte: {actual:#04x}")
            }
            Self::WrongVersion { actual } => write!(
                f,
                "wrong artifact format version: expected {ARTIFACT_FORMAT_VERSION}, got {actual}"
            ),
            Self::WrongDomain { actual } => write!(
                f,
                "wrong artifact domain: expected {ARTIFACT_DOMAIN}, got {actual}"
            ),
            Self::UnknownBodyTag { offset, actual } => write!(
                f,
                "unknown artifact body tag {actual:#04x} at frame byte {offset}"
            ),
            Self::TrailingBytes { offset } => {
                write!(
                    f,
                    "artifact frame has trailing bytes beginning at byte {offset}"
                )
            }
            Self::NonCanonicalPayload => {
                write!(f, "artifact payload is not a canonical ArtifactEncoding")
            }
        }
    }
}

impl std::error::Error for ArtifactFrameError {}

/// One exact, Lean-validated canonical `ArtifactDurable` v2 frame.
///
/// Rust classifies the outer frame for useful diagnostics, then asks the
/// narrow Lean validator to interpret canonical first-order payload bytes.
/// Rust contains no `ArtifactEncoding` semantic decoder.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactFrame {
    bytes: Vec<u8>,
}

impl ArtifactFrame {
    /// Validate and retain exactly one complete frame.
    pub fn new(bytes: Vec<u8>) -> Result<Self, ArtifactFrameError> {
        if bytes.len() > MAX_ARTIFACT_FRAME_BYTES {
            return Err(ArtifactFrameError::TooLarge {
                actual: bytes.len(),
                maximum: MAX_ARTIFACT_FRAME_BYTES,
            });
        }
        let end = parse_frame_prefix(&bytes)?;
        if end != bytes.len() {
            return Err(ArtifactFrameError::TrailingBytes { offset: end });
        }
        if !ffi::preo_artifact_v2_validate_one(&bytes) {
            return Err(ArtifactFrameError::NonCanonicalPayload);
        }
        Ok(Self { bytes })
    }

    /// Borrow the exact bytes supplied at construction.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Consume the wrapper without changing the bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

impl TryFrom<Vec<u8>> for ArtifactFrame {
    type Error = ArtifactFrameError;

    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        Self::new(bytes)
    }
}

/// Failure while importing an exact concatenation of logical artifact frames.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactStreamError {
    /// Byte offset where the next frame refused.
    pub offset: usize,
    /// Why the next frame refused.
    pub source: ArtifactFrameError,
}

impl fmt::Display for ArtifactStreamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "artifact frame stream refused at byte {}: {}",
            self.offset, self.source
        )
    }
}

impl std::error::Error for ArtifactStreamError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

/// Parse a complete logical frame stream without accepting a torn suffix.
///
/// This is the direct Rust framing counterpart of Lean's concatenated-frame
/// scanner. It does not parse `ArtifactEncoding` payloads.
pub fn decode_artifact_frame_stream(
    bytes: &[u8],
) -> Result<Vec<ArtifactFrame>, ArtifactStreamError> {
    let scan =
        scan_artifacts(bytes).map_err(|(offset, source)| ArtifactStreamError { offset, source })?;
    if scan.torn_bytes != 0 {
        return Err(ArtifactStreamError {
            offset: scan.valid_bytes,
            source: ArtifactFrameError::Torn,
        });
    }
    Ok(scan.frames)
}

/// Concatenate exact logical artifact frames without changing any byte.
pub fn encode_artifact_frame_stream<'a>(
    frames: impl IntoIterator<Item = &'a ArtifactFrame>,
) -> Vec<u8> {
    let mut bytes = Vec::new();
    for frame in frames {
        bytes.extend_from_slice(frame.as_bytes());
    }
    bytes
}

/// Result metadata from opening an artifact journal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArtifactOpenReport {
    /// Number of complete frames recovered.
    pub recovered_frames: usize,
    /// Number of physical-record suffix bytes discarded under the configured
    /// torn-tail policy.
    pub truncated_bytes: u64,
    /// Whether opening created the file. With [`SyncPolicy::SyncAll`], the
    /// parent directory is synced after creation; weaker policies do not make
    /// the directory entry durable.
    pub created: bool,
}

/// Artifact filesystem/open/scan failure.
#[derive(Debug)]
pub enum ArtifactJournalError {
    /// An operating-system I/O operation failed.
    Io(io::Error),
    /// A frame supplied to append was not exactly one v2 artifact frame.
    InvalidAppend(ArtifactFrameError),
    /// A checksummed physical record contains bytes that are not exactly one
    /// format-v2 artifact frame.
    CorruptFrame {
        /// Internal physical-record sequence.
        sequence: u64,
        /// The artifact framing refusal.
        source: ArtifactFrameError,
    },
    /// The physical file already has a live writer holding its exclusive
    /// advisory lock.
    Locked,
    /// The physical file ends in one syntactically torn final record.
    TornTail { offset: u64, bytes: u64 },
    /// A complete physical record is corrupt. This is never treated as a torn
    /// tail, even when it is last.
    CorruptPhysical {
        sequence: u64,
        offset: u64,
        reason: &'static str,
    },
    /// A body exceeds the configured pre-allocation bound.
    RecordTooLarge { actual: u64, maximum: u64 },
    /// An append skipped the next internally allocated sequence.
    SequenceGap { expected: u64, requested: u64 },
    /// An idempotent retry named an existing sequence with different content.
    SequenceConflict { sequence: u64 },
    /// No further contiguous sequence can be allocated.
    SequenceExhausted,
    /// A prior append/sync failed; reopen to resolve the uncertain suffix.
    Poisoned,
}

impl fmt::Display for ArtifactJournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(source) => write!(f, "artifact journal I/O failed: {source}"),
            Self::InvalidAppend(source) => write!(f, "invalid artifact append: {source}"),
            Self::CorruptFrame { sequence, source } => {
                write!(
                    f,
                    "artifact journal record {sequence} is not a v2 frame: {source}"
                )
            }
            Self::Locked => write!(f, "artifact journal already has a live writer"),
            Self::TornTail { offset, bytes } => write!(
                f,
                "artifact journal has a {bytes}-byte torn tail at byte {offset}"
            ),
            Self::Poisoned => write!(
                f,
                "artifact journal append state is uncertain after an I/O failure; reopen it"
            ),
            Self::CorruptPhysical {
                sequence,
                offset,
                reason,
            } => write!(
                f,
                "artifact physical record {sequence} is corrupt at byte {offset}: {reason}"
            ),
            Self::RecordTooLarge { actual, maximum } => write!(
                f,
                "artifact physical record is {actual} bytes; configured maximum is {maximum}"
            ),
            Self::SequenceGap {
                expected,
                requested,
            } => write!(
                f,
                "artifact sequence gap: expected {expected}, requested {requested}"
            ),
            Self::SequenceConflict { sequence } => {
                write!(
                    f,
                    "artifact sequence {sequence} already contains different bytes"
                )
            }
            Self::SequenceExhausted => write!(f, "artifact sequence space is exhausted"),
        }
    }
}

impl std::error::Error for ArtifactJournalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(source) => Some(source),
            Self::InvalidAppend(source) | Self::CorruptFrame { source, .. } => Some(source),
            _ => None,
        }
    }
}

impl From<io::Error> for ArtifactJournalError {
    fn from(source: io::Error) -> Self {
        Self::Io(source)
    }
}

impl From<RawJournalError> for ArtifactJournalError {
    fn from(source: RawJournalError) -> Self {
        match source {
            RawJournalError::Io(source) => Self::Io(source),
            RawJournalError::Locked => Self::Locked,
            RawJournalError::TornTail { offset, bytes } => Self::TornTail { offset, bytes },
            RawJournalError::Corrupt {
                sequence,
                offset,
                reason,
            } => Self::CorruptPhysical {
                sequence,
                offset,
                reason,
            },
            RawJournalError::RecordTooLarge { actual, maximum } => {
                Self::RecordTooLarge { actual, maximum }
            }
            RawJournalError::SequenceGap {
                expected,
                requested,
            } => Self::SequenceGap {
                expected,
                requested,
            },
            RawJournalError::SequenceConflict { sequence } => Self::SequenceConflict { sequence },
            RawJournalError::SequenceExhausted => Self::SequenceExhausted,
            RawJournalError::Poisoned => Self::Poisoned,
        }
    }
}

#[derive(Debug)]
struct ArtifactScan {
    frames: Vec<ArtifactFrame>,
    valid_bytes: usize,
    torn_bytes: usize,
}

/// An append-only physical journal whose checksummed record bodies are exact
/// `ArtifactDurable` format-v2 frames.
#[derive(Debug)]
pub struct ArtifactJournal {
    raw: RawJournal,
    frames: Vec<ArtifactFrame>,
    open_report: ArtifactOpenReport,
}

impl ArtifactJournal {
    /// Open or create a journal, scan its complete prefix, and apply the
    /// requested torn-final-frame policy.
    pub fn open(
        path: impl AsRef<Path>,
        options: JournalOptions,
    ) -> Result<Self, ArtifactJournalError> {
        let raw = RawJournal::open(path, RECORD_SPEC, options)?;
        let mut frames = Vec::with_capacity(raw.records().len());
        for (sequence, bytes) in raw.records().iter().enumerate() {
            let frame = ArtifactFrame::new(bytes.clone()).map_err(|source| {
                ArtifactJournalError::CorruptFrame {
                    sequence: sequence as u64,
                    source,
                }
            })?;
            frames.push(frame);
        }
        let report = raw.report();
        let open_report = ArtifactOpenReport {
            recovered_frames: frames.len(),
            truncated_bytes: report.truncated_bytes,
            created: report.created,
        };
        Ok(Self {
            raw,
            frames,
            open_report,
        })
    }

    /// Path backing this journal.
    pub fn path(&self) -> &Path {
        self.raw.path()
    }

    /// What the opening scan recovered or truncated.
    pub fn open_report(&self) -> ArtifactOpenReport {
        self.open_report
    }

    /// Complete exact frames recovered from the file prefix.
    pub fn frames(&self) -> &[ArtifactFrame] {
        &self.frames
    }

    /// Next contiguous physical record sequence.
    pub fn next_sequence(&self) -> u64 {
        self.raw.next_sequence()
    }

    /// Append one already-validated exact frame.
    ///
    /// If writing or synchronization fails, the handle is poisoned because a
    /// complete or torn suffix may now exist. Reopen under an explicit tail
    /// policy before any further append.
    pub fn append_at(
        &mut self,
        sequence: u64,
        frame: ArtifactFrame,
    ) -> Result<AppendReceipt, ArtifactJournalError> {
        let receipt = self.raw.append_at(sequence, frame.as_bytes())?;
        if receipt.status == super::AppendStatus::Appended {
            self.frames.push(frame);
        }
        Ok(receipt)
    }

    /// Append at the next sequence. For retry after an uncertain I/O result,
    /// retain the returned/requested sequence and use [`Self::append_at`]
    /// after reopening; identical content is recognized idempotently.
    pub fn append(&mut self, frame: ArtifactFrame) -> Result<AppendReceipt, ArtifactJournalError> {
        self.append_at(self.next_sequence(), frame)
    }

    /// Validate exact v2 bytes and append at a caller-retained sequence.
    pub fn append_bytes_at(
        &mut self,
        sequence: u64,
        bytes: Vec<u8>,
    ) -> Result<AppendReceipt, ArtifactJournalError> {
        let frame = ArtifactFrame::new(bytes).map_err(ArtifactJournalError::InvalidAppend)?;
        self.append_at(sequence, frame)
    }

    /// Explicitly strengthen durability independently of the append policy.
    pub fn sync(&mut self, policy: SyncPolicy) -> Result<(), ArtifactJournalError> {
        self.raw.sync(policy).map_err(Into::into)
    }
}

/// Parse one v2 envelope at the beginning of `bytes`, returning its exclusive
/// end. EOF at any legal pre-terminator point is [`ArtifactFrameError::Torn`].
fn parse_frame_prefix(bytes: &[u8]) -> Result<usize, ArtifactFrameError> {
    if bytes.is_empty() {
        return Err(ArtifactFrameError::Torn);
    }
    if bytes[0] != MAGIC_0 {
        return Err(ArtifactFrameError::WrongMagic0 { actual: bytes[0] });
    }
    if bytes.len() == 1 {
        return Err(ArtifactFrameError::Torn);
    }
    if bytes[1] != MAGIC_1 {
        return Err(ArtifactFrameError::WrongMagic1 { actual: bytes[1] });
    }
    if bytes.len() == 2 {
        return Err(ArtifactFrameError::Torn);
    }
    if bytes[2] != ARTIFACT_FORMAT_VERSION {
        return Err(ArtifactFrameError::WrongVersion { actual: bytes[2] });
    }
    if bytes.len() == 3 {
        return Err(ArtifactFrameError::Torn);
    }
    if bytes[3] != ARTIFACT_DOMAIN {
        return Err(ArtifactFrameError::WrongDomain { actual: bytes[3] });
    }

    let mut cursor = 4;
    while cursor < bytes.len() {
        match bytes[cursor] {
            END_TAG => return Ok(cursor + 1),
            DATA_TAG => {
                if cursor + 1 == bytes.len() {
                    return Err(ArtifactFrameError::Torn);
                }
                cursor += 2;
            }
            actual => {
                return Err(ArtifactFrameError::UnknownBodyTag {
                    offset: cursor,
                    actual,
                });
            }
        }
    }
    Err(ArtifactFrameError::Torn)
}

fn scan_artifacts(bytes: &[u8]) -> Result<ArtifactScan, (usize, ArtifactFrameError)> {
    let mut frames = Vec::new();
    let mut cursor = 0;
    while cursor < bytes.len() {
        match parse_frame_prefix(&bytes[cursor..]) {
            Ok(length) => {
                let frame = ArtifactFrame::new(bytes[cursor..cursor + length].to_vec())
                    .map_err(|source| (cursor, source))?;
                frames.push(frame);
                cursor += length;
            }
            Err(ArtifactFrameError::Torn) => {
                return Ok(ArtifactScan {
                    frames,
                    valid_bytes: cursor,
                    torn_bytes: bytes.len() - cursor,
                });
            }
            Err(source) => {
                return Err((cursor, source));
            }
        }
    }
    Ok(ArtifactScan {
        frames,
        valid_bytes: cursor,
        torn_bytes: 0,
    })
}
