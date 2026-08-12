//! Checksummed persistence for the replicated document's authoritative move
//! substrate.
//!
//! This first runtime vertical slice persists [`MoveLog`] inputs: move
//! operations, grants, revocations, and proof-oblivious checkpoints of those
//! three grow-only sets. It reconstructs by calling the existing public
//! [`MoveLog::record`], [`MoveLog::issue`], and [`MoveLog::revoke`] APIs.
//! Derived replay views and per-op outcomes are never records.
//!
//! Causal nodes, sequence edits, ERA events, and whole-`Weave` seam changes do
//! not yet have record variants here. Treating arbitrary bytes as those typed
//! operations would weaken the boundary, so expansion requires new explicit
//! variants and codecs.
//!
//! These records are also deliberately unauthenticated legacy/runtime inputs:
//! a stored actor/replica id is not a signature. A future RuntimeAuth/FORMAT-v4
//! admission layer must authenticate records before calling these append APIs;
//! persistence does not upgrade authorization into identity.

use super::record::{RawJournal, RawJournalError, RecordSpec};
use super::{AppendReceipt, AppendStatus, JournalOptions, SyncPolicy};
use crate::{Grant, MoveLog, MoveOp, NodeId};
use std::fmt;
use std::io;
use std::path::Path;

const RECORD_SPEC: RecordSpec = RecordSpec {
    marker: *b"UWDJRN01",
    hash_domain: b"uwueave.document-journal.v1",
};

const MOVE_TAG: u8 = 0;
const GRANT_TAG: u8 = 1;
const REVOCATION_TAG: u8 = 2;
const CHECKPOINT_TAG: u8 = 3;

/// The authoritative kind represented by one physical document record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DocumentEntryKind {
    /// One grow-only [`MoveOp`].
    MoveOperation,
    /// One grow-only [`Grant`].
    GrantIssued,
    /// One grow-only revoked grant id.
    GrantRevoked,
    /// A validated snapshot of the three [`MoveLog`] sets through a named
    /// mutation prefix. It is a recovery accelerator, never a derived view.
    MoveLogCheckpoint,
}

/// One decoded authoritative runtime record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DocumentEntry {
    /// A move operation to feed to [`MoveLog::record`].
    Move(MoveOp),
    /// A grant to feed to [`MoveLog::issue`].
    Grant(Grant),
    /// A grant id to feed to [`MoveLog::revoke`].
    Revocation(u64),
    /// Complete authoritative `MoveLog` sets after `covers_through`.
    Checkpoint {
        /// Last physical mutation sequence represented, or `None` for the
        /// empty log.
        covers_through: Option<u64>,
        /// Snapshot rebuilt through the public `MoveLog` APIs.
        log: MoveLog,
    },
}

impl DocumentEntry {
    /// Discriminant without exposing storage tags.
    pub fn kind(&self) -> DocumentEntryKind {
        match self {
            Self::Move(_) => DocumentEntryKind::MoveOperation,
            Self::Grant(_) => DocumentEntryKind::GrantIssued,
            Self::Revocation(_) => DocumentEntryKind::GrantRevoked,
            Self::Checkpoint { .. } => DocumentEntryKind::MoveLogCheckpoint,
        }
    }
}

/// Result metadata from opening a document journal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DocumentOpenReport {
    /// Number of complete checksummed records recovered.
    pub recovered_records: usize,
    /// Number of bytes discarded from one physical torn tail.
    pub truncated_bytes: u64,
    /// Whether opening created the journal file.
    pub created: bool,
}

/// Why a document journal operation failed.
#[derive(Debug)]
pub enum DocumentJournalError {
    /// An operating-system operation failed.
    Io(io::Error),
    /// Another live handle/process holds the exclusive advisory writer lock.
    Locked,
    /// The final physical record is a syntactic prefix and policy refused it.
    TornTail { offset: u64, bytes: u64 },
    /// A complete checksum/header/sequence failed. Corruption is never
    /// silently truncated, including at EOF.
    CorruptPhysical {
        sequence: u64,
        offset: u64,
        reason: &'static str,
    },
    /// A checksummed record body is malformed or noncanonical.
    CorruptEntry { sequence: u64, reason: &'static str },
    /// A checkpoint did not describe exactly the preceding mutation prefix.
    InvalidCheckpoint { sequence: u64 },
    /// The configured per-record allocation bound was exceeded.
    RecordTooLarge { actual: u64, maximum: u64 },
    /// Append skipped the next internal physical sequence.
    SequenceGap { expected: u64, requested: u64 },
    /// An idempotent retry named an occupied sequence with different bytes.
    SequenceConflict { sequence: u64 },
    /// No further sequence can be allocated.
    SequenceExhausted,
    /// An I/O/sync failure left the append result uncertain; reopen first.
    Poisoned,
}

impl fmt::Display for DocumentJournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(source) => write!(f, "document journal I/O failed: {source}"),
            Self::Locked => write!(f, "document journal already has a live writer"),
            Self::TornTail { offset, bytes } => {
                write!(
                    f,
                    "document journal has a {bytes}-byte torn tail at byte {offset}"
                )
            }
            Self::CorruptPhysical {
                sequence,
                offset,
                reason,
            } => write!(
                f,
                "document physical record {sequence} is corrupt at byte {offset}: {reason}"
            ),
            Self::CorruptEntry { sequence, reason } => {
                write!(f, "document record {sequence} is invalid: {reason}")
            }
            Self::InvalidCheckpoint { sequence } => write!(
                f,
                "document checkpoint {sequence} does not equal its preceding mutation prefix"
            ),
            Self::RecordTooLarge { actual, maximum } => write!(
                f,
                "document record is {actual} bytes; configured maximum is {maximum}"
            ),
            Self::SequenceGap {
                expected,
                requested,
            } => write!(
                f,
                "document sequence gap: expected {expected}, requested {requested}"
            ),
            Self::SequenceConflict { sequence } => {
                write!(
                    f,
                    "document sequence {sequence} already contains different bytes"
                )
            }
            Self::SequenceExhausted => write!(f, "document sequence space is exhausted"),
            Self::Poisoned => write!(
                f,
                "document journal append state is uncertain after an I/O failure; reopen it"
            ),
        }
    }
}

impl std::error::Error for DocumentJournalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(source) => Some(source),
            _ => None,
        }
    }
}

impl From<io::Error> for DocumentJournalError {
    fn from(source: io::Error) -> Self {
        Self::Io(source)
    }
}

impl From<RawJournalError> for DocumentJournalError {
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

/// Consumer of recovered typed records.
///
/// [`DocumentJournal::replay_into`] restores the newest validated checkpoint,
/// then sends only later mutations. Implementations can call existing runtime
/// APIs; [`DocumentJournal::recovered_move_log`] is the built-in `MoveLog`
/// consumer.
pub trait DocumentReplay {
    /// Consumer-specific failure.
    type Error;

    /// Restore a complete authoritative checkpoint.
    fn restore_move_log(&mut self, checkpoint: &MoveLog) -> Result<(), Self::Error>;
    /// Apply one later move operation.
    fn record_move(&mut self, op: MoveOp) -> Result<(), Self::Error>;
    /// Apply one later grant.
    fn issue_grant(&mut self, grant: Grant) -> Result<(), Self::Error>;
    /// Apply one later revocation.
    fn revoke_grant(&mut self, grant_id: u64) -> Result<(), Self::Error>;
}

/// Error from the typed replay adapter.
#[derive(Debug, PartialEq, Eq)]
pub struct DocumentReplayError<E> {
    /// Physical record whose typed application failed.
    pub sequence: u64,
    /// Consumer error.
    pub source: E,
}

/// Single-writer, append-only authoritative `MoveLog` journal.
#[derive(Debug)]
pub struct DocumentJournal {
    raw: RawJournal,
    entries: Vec<DocumentEntry>,
    current: MoveLog,
    last_mutation_sequence: Option<u64>,
    report: DocumentOpenReport,
}

impl DocumentJournal {
    /// Open/create, exclusively lock, scan, checksum, canonically decode, and
    /// reconstruct the typed move substrate.
    pub fn open(
        path: impl AsRef<Path>,
        options: JournalOptions,
    ) -> Result<Self, DocumentJournalError> {
        let raw = RawJournal::open(path, RECORD_SPEC, options)?;
        let mut entries = Vec::with_capacity(raw.records().len());
        let mut current = MoveLog::new();
        let mut last_mutation_sequence = None;
        for (sequence, bytes) in raw.records().iter().enumerate() {
            let sequence = sequence as u64;
            let entry = decode_entry(bytes).ok_or(DocumentJournalError::CorruptEntry {
                sequence,
                reason: "malformed or noncanonical typed MoveLog entry",
            })?;
            match &entry {
                DocumentEntry::Move(op) => {
                    current.record(*op);
                    last_mutation_sequence = Some(sequence);
                }
                DocumentEntry::Grant(grant) => {
                    current.issue(*grant);
                    last_mutation_sequence = Some(sequence);
                }
                DocumentEntry::Revocation(id) => {
                    current.revoke(*id);
                    last_mutation_sequence = Some(sequence);
                }
                DocumentEntry::Checkpoint {
                    covers_through,
                    log,
                } => {
                    if *covers_through != last_mutation_sequence || log != &current {
                        return Err(DocumentJournalError::InvalidCheckpoint { sequence });
                    }
                }
            }
            entries.push(entry);
        }
        let raw_report = raw.report();
        let report = DocumentOpenReport {
            recovered_records: entries.len(),
            truncated_bytes: raw_report.truncated_bytes,
            created: raw_report.created,
        };
        Ok(Self {
            raw,
            entries,
            current,
            last_mutation_sequence,
            report,
        })
    }

    /// Backing path.
    pub fn path(&self) -> &Path {
        self.raw.path()
    }

    /// Opening scan result.
    pub fn open_report(&self) -> DocumentOpenReport {
        self.report
    }

    /// Decoded authoritative records, in contiguous physical sequence order.
    pub fn entries(&self) -> &[DocumentEntry] {
        &self.entries
    }

    /// Next sequence a new append must name.
    pub fn next_sequence(&self) -> u64 {
        self.raw.next_sequence()
    }

    /// `MoveLog` reconstructed by existing public mutation APIs. This is the
    /// authoritative substrate; call `replay`/`replay_traced` with a weave to
    /// derive a view through the Lean kernel.
    pub fn recovered_move_log(&self) -> &MoveLog {
        &self.current
    }

    /// Sequence-addressed, idempotently retryable move append.
    pub fn append_move_at(
        &mut self,
        sequence: u64,
        op: MoveOp,
    ) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_entry_at(sequence, DocumentEntry::Move(op))
    }

    /// Append a move at [`Self::next_sequence`]. Retain the sequence when an
    /// I/O result is uncertain and retry with [`Self::append_move_at`].
    pub fn append_move(&mut self, op: MoveOp) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_move_at(self.next_sequence(), op)
    }

    /// Sequence-addressed, idempotently retryable grant append.
    pub fn append_grant_at(
        &mut self,
        sequence: u64,
        grant: Grant,
    ) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_entry_at(sequence, DocumentEntry::Grant(grant))
    }

    /// Append a grant at [`Self::next_sequence`].
    pub fn append_grant(&mut self, grant: Grant) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_grant_at(self.next_sequence(), grant)
    }

    /// Sequence-addressed, idempotently retryable revocation append.
    pub fn append_revocation_at(
        &mut self,
        sequence: u64,
        grant_id: u64,
    ) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_entry_at(sequence, DocumentEntry::Revocation(grant_id))
    }

    /// Append a revocation at [`Self::next_sequence`].
    pub fn append_revocation(
        &mut self,
        grant_id: u64,
    ) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_revocation_at(self.next_sequence(), grant_id)
    }

    /// Append a checkpoint of exactly the preceding typed mutation prefix.
    pub fn append_checkpoint_at(
        &mut self,
        sequence: u64,
    ) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_entry_at(
            sequence,
            DocumentEntry::Checkpoint {
                covers_through: self.last_mutation_sequence,
                log: self.current.clone(),
            },
        )
    }

    /// Append a checkpoint at [`Self::next_sequence`].
    pub fn append_checkpoint(&mut self) -> Result<AppendReceipt, DocumentJournalError> {
        self.append_checkpoint_at(self.next_sequence())
    }

    /// Strengthen durability independently of the configured append policy.
    pub fn sync(&mut self, policy: SyncPolicy) -> Result<(), DocumentJournalError> {
        self.raw.sync(policy).map_err(Into::into)
    }

    /// Replay from the newest validated checkpoint and apply later mutations.
    /// Checkpoints themselves were checked against their full preceding
    /// prefix at open time, so this optimization cannot change the result.
    pub fn replay_into<R: DocumentReplay>(
        &self,
        consumer: &mut R,
    ) -> Result<(), DocumentReplayError<R::Error>> {
        let checkpoint = self
            .entries
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, entry)| {
                if let DocumentEntry::Checkpoint { log, .. } = entry {
                    Some((i, log))
                } else {
                    None
                }
            });
        let start = if let Some((sequence, log)) = checkpoint {
            consumer
                .restore_move_log(log)
                .map_err(|source| DocumentReplayError {
                    sequence: sequence as u64,
                    source,
                })?;
            sequence + 1
        } else {
            0
        };
        for (sequence, entry) in self.entries.iter().enumerate().skip(start) {
            let result = match entry {
                DocumentEntry::Move(op) => consumer.record_move(*op),
                DocumentEntry::Grant(grant) => consumer.issue_grant(*grant),
                DocumentEntry::Revocation(id) => consumer.revoke_grant(*id),
                DocumentEntry::Checkpoint { .. } => continue,
            };
            result.map_err(|source| DocumentReplayError {
                sequence: sequence as u64,
                source,
            })?;
        }
        Ok(())
    }

    fn append_entry_at(
        &mut self,
        sequence: u64,
        entry: DocumentEntry,
    ) -> Result<AppendReceipt, DocumentJournalError> {
        let bytes = encode_entry(&entry);
        let receipt = self.raw.append_at(sequence, &bytes)?;
        if receipt.status == AppendStatus::Appended {
            match &entry {
                DocumentEntry::Move(op) => {
                    self.current.record(*op);
                    self.last_mutation_sequence = Some(sequence);
                }
                DocumentEntry::Grant(grant) => {
                    self.current.issue(*grant);
                    self.last_mutation_sequence = Some(sequence);
                }
                DocumentEntry::Revocation(id) => {
                    self.current.revoke(*id);
                    self.last_mutation_sequence = Some(sequence);
                }
                DocumentEntry::Checkpoint { .. } => {}
            }
            self.entries.push(entry);
        }
        Ok(receipt)
    }
}

fn encode_entry(entry: &DocumentEntry) -> Vec<u8> {
    let mut bytes = Vec::new();
    match entry {
        DocumentEntry::Move(op) => {
            bytes.push(MOVE_TAG);
            put_u64(&mut bytes, op.lamport);
            put_u64(&mut bytes, op.replica);
            bytes.extend_from_slice(&op.child);
            match op.dest {
                None => bytes.push(0),
                Some(dest) => {
                    bytes.push(1);
                    bytes.extend_from_slice(&dest);
                }
            }
            put_u64(&mut bytes, op.cite);
        }
        DocumentEntry::Grant(grant) => {
            bytes.push(GRANT_TAG);
            put_grant(&mut bytes, *grant);
        }
        DocumentEntry::Revocation(id) => {
            bytes.push(REVOCATION_TAG);
            put_u64(&mut bytes, *id);
        }
        DocumentEntry::Checkpoint {
            covers_through,
            log,
        } => {
            bytes.push(CHECKPOINT_TAG);
            match covers_through {
                None => bytes.push(0),
                Some(sequence) => {
                    bytes.push(1);
                    put_u64(&mut bytes, *sequence);
                }
            }
            put_u64(&mut bytes, log.ops().count() as u64);
            for op in log.ops() {
                put_move_without_tag(&mut bytes, *op);
            }
            put_u64(&mut bytes, log.grants().count() as u64);
            for grant in log.grants() {
                put_grant(&mut bytes, *grant);
            }
            put_u64(&mut bytes, log.revocations().count() as u64);
            for id in log.revocations() {
                put_u64(&mut bytes, *id);
            }
        }
    }
    bytes
}

fn decode_entry(bytes: &[u8]) -> Option<DocumentEntry> {
    let mut cursor = Cursor::new(bytes);
    let tag = cursor.byte()?;
    let entry = match tag {
        MOVE_TAG => DocumentEntry::Move(cursor.move_op()?),
        GRANT_TAG => DocumentEntry::Grant(cursor.grant()?),
        REVOCATION_TAG => DocumentEntry::Revocation(cursor.u64()?),
        CHECKPOINT_TAG => {
            let covers_through = match cursor.byte()? {
                0 => None,
                1 => Some(cursor.u64()?),
                _ => return None,
            };
            let mut log = MoveLog::new();
            let op_count = cursor.count(57)?;
            for _ in 0..op_count {
                log.record(cursor.move_op()?);
            }
            let grant_count = cursor.count(24)?;
            for _ in 0..grant_count {
                log.issue(cursor.grant()?);
            }
            let revocation_count = cursor.count(8)?;
            for _ in 0..revocation_count {
                log.revoke(cursor.u64()?);
            }
            DocumentEntry::Checkpoint {
                covers_through,
                log,
            }
        }
        _ => return None,
    };
    if !cursor.is_empty() || encode_entry(&entry) != bytes {
        return None;
    }
    Some(entry)
}

fn put_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn put_grant(bytes: &mut Vec<u8>, grant: Grant) {
    put_u64(bytes, grant.id);
    put_u64(bytes, grant.parent);
    put_u64(bytes, grant.scope);
}

fn put_move_without_tag(bytes: &mut Vec<u8>, op: MoveOp) {
    put_u64(bytes, op.lamport);
    put_u64(bytes, op.replica);
    bytes.extend_from_slice(&op.child);
    match op.dest {
        None => bytes.push(0),
        Some(dest) => {
            bytes.push(1);
            bytes.extend_from_slice(&dest);
        }
    }
    put_u64(bytes, op.cite);
}

struct Cursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn is_empty(&self) -> bool {
        self.offset == self.bytes.len()
    }

    fn byte(&mut self) -> Option<u8> {
        let byte = *self.bytes.get(self.offset)?;
        self.offset += 1;
        Some(byte)
    }

    fn take(&mut self, count: usize) -> Option<&'a [u8]> {
        let end = self.offset.checked_add(count)?;
        let slice = self.bytes.get(self.offset..end)?;
        self.offset = end;
        Some(slice)
    }

    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }

    fn node_id(&mut self) -> Option<NodeId> {
        self.take(32)?.try_into().ok()
    }

    fn count(&mut self, minimum_item_bytes: usize) -> Option<usize> {
        let count = usize::try_from(self.u64()?).ok()?;
        let needed = count.checked_mul(minimum_item_bytes)?;
        if needed > self.bytes.len().saturating_sub(self.offset) {
            return None;
        }
        Some(count)
    }

    fn grant(&mut self) -> Option<Grant> {
        Some(Grant {
            id: self.u64()?,
            parent: self.u64()?,
            scope: self.u64()?,
        })
    }

    fn move_op(&mut self) -> Option<MoveOp> {
        let lamport = self.u64()?;
        let replica = self.u64()?;
        let child = self.node_id()?;
        let dest = match self.byte()? {
            0 => None,
            1 => Some(self.node_id()?),
            _ => return None,
        };
        let cite = self.u64()?;
        Some(MoveOp {
            lamport,
            replica,
            child,
            dest,
            cite,
        })
    }
}
