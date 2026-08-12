//! Checksummed persistence for a causally closed history event set.
//!
//! Each event carries an explicit, application-assigned 32-byte id, a
//! canonical parent set, and opaque payload bytes. [`HistoryJournal`] requires
//! parents immediately, keeping every accepted physical prefix causally closed.
//! [`BufferedHistoryJournal`] optionally adds a visible bounded out-of-order
//! endpoint whose pending events are deliberately non-durable and vanish on
//! reopen; only ready events enter the physical journal.
//!
//! Event ids are uniqueness claims, not authentication. Repeating the exact
//! event is idempotent, while resolving one id to different parents or payload
//! is refused as corruption. Applications that need unforgeable history ids
//! must authenticate or content-address them before admission.

use super::record::{RawJournal, RawJournalError, RecordSpec};
use super::{AppendReceipt, AppendStatus, JournalOptions, SyncPolicy};
use crate::NodeIdDisplay;
use std::collections::{btree_map::Entry, BTreeMap};
use std::fmt;
use std::io;
use std::path::Path;

const RECORD_SPEC: RecordSpec = RecordSpec {
    marker: *b"UWHIST01",
    hash_domain: b"uwueave.history-journal.v1",
};

const EVENT_FORMAT_VERSION: u8 = 1;
const ID_BYTES: usize = 32;
const U64_BYTES: usize = 8;

/// Stable identity of one history event.
pub type HistoryEventId = [u8; ID_BYTES];

/// A canonical causal history event.
///
/// Parent ids are strictly increasing. This makes them a set with exactly one
/// byte encoding: reordered or duplicate parents are rejected at construction
/// and recovery rather than being normalized silently.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HistoryEvent {
    id: HistoryEventId,
    parents: Vec<HistoryEventId>,
    payload: Vec<u8>,
}

impl HistoryEvent {
    /// Construct an event after validating its canonical parent set.
    pub fn new(
        id: HistoryEventId,
        parents: Vec<HistoryEventId>,
        payload: Vec<u8>,
    ) -> Result<Self, HistoryEventError> {
        validate_parents(&id, &parents)?;
        Ok(Self {
            id,
            parents,
            payload,
        })
    }

    /// Application-assigned stable event id.
    pub fn id(&self) -> HistoryEventId {
        self.id
    }

    /// Canonically ordered parent set.
    pub fn parents(&self) -> &[HistoryEventId] {
        &self.parents
    }

    /// Opaque authoritative event payload.
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
}

/// Why an event could not be constructed canonically.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HistoryEventError {
    /// An event may not name itself as a parent.
    SelfParent,
    /// Parents must be strictly increasing, which also excludes duplicates.
    ParentsNotStrictlyIncreasing,
}

impl fmt::Display for HistoryEventError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SelfParent => write!(f, "history event names itself as a parent"),
            Self::ParentsNotStrictlyIncreasing => {
                write!(f, "history event parents are not strictly increasing")
            }
        }
    }
}

impl std::error::Error for HistoryEventError {}

/// Result metadata from opening a history journal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HistoryOpenReport {
    /// Number of complete checksummed physical records recovered.
    pub recovered_records: usize,
    /// Number of distinct causal events reconstructed.
    pub recovered_events: usize,
    /// Number of bytes discarded from one physical torn tail.
    pub truncated_bytes: u64,
    /// Whether opening created the journal file.
    pub created: bool,
}

/// Why a history journal operation failed.
#[derive(Debug)]
pub enum HistoryJournalError {
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
    /// A checksummed event body is malformed or noncanonical.
    CorruptEvent { sequence: u64, reason: &'static str },
    /// A named parent is not in the accepted causal prefix.
    MissingParent {
        sequence: u64,
        event: HistoryEventId,
        parent: HistoryEventId,
    },
    /// One id resolves to different event content.
    IdCollision {
        id: HistoryEventId,
        existing_sequence: u64,
        incoming_sequence: u64,
    },
    /// One buffered id resolves to different event content. Buffered events do
    /// not yet have a physical sequence.
    PendingIdCollision { id: HistoryEventId },
    /// The explicit non-durable out-of-order buffer has no free slot.
    BufferFull { capacity: usize },
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

impl fmt::Display for HistoryJournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(source) => write!(f, "history journal I/O failed: {source}"),
            Self::Locked => write!(f, "history journal already has a live writer"),
            Self::TornTail { offset, bytes } => write!(
                f,
                "history journal has a {bytes}-byte torn tail at byte {offset}"
            ),
            Self::CorruptPhysical {
                sequence,
                offset,
                reason,
            } => write!(
                f,
                "history physical record {sequence} is corrupt at byte {offset}: {reason}"
            ),
            Self::CorruptEvent { sequence, reason } => {
                write!(f, "history event record {sequence} is invalid: {reason}")
            }
            Self::MissingParent {
                sequence,
                event,
                parent,
            } => write!(
                f,
                "history event {} at sequence {sequence} is missing parent {}",
                NodeIdDisplay::new(event),
                NodeIdDisplay::new(parent)
            ),
            Self::IdCollision {
                id,
                existing_sequence,
                incoming_sequence,
            } => write!(
                f,
                "history event id {} at sequence {incoming_sequence} conflicts with sequence {existing_sequence}",
                NodeIdDisplay::new(id)
            ),
            Self::PendingIdCollision { id } => write!(
                f,
                "buffered history event id {} resolves to different content",
                NodeIdDisplay::new(id)
            ),
            Self::BufferFull { capacity } => {
                write!(f, "history out-of-order buffer is full at capacity {capacity}")
            }
            Self::RecordTooLarge { actual, maximum } => write!(
                f,
                "history event record is {actual} bytes; configured maximum is {maximum}"
            ),
            Self::SequenceGap {
                expected,
                requested,
            } => write!(
                f,
                "history sequence gap: expected {expected}, requested {requested}"
            ),
            Self::SequenceConflict { sequence } => write!(
                f,
                "history sequence {sequence} already contains different bytes"
            ),
            Self::SequenceExhausted => write!(f, "history sequence space is exhausted"),
            Self::Poisoned => write!(
                f,
                "history journal append state is uncertain after an I/O failure; reopen it"
            ),
        }
    }
}

impl std::error::Error for HistoryJournalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(source) => Some(source),
            _ => None,
        }
    }
}

impl From<io::Error> for HistoryJournalError {
    fn from(source: io::Error) -> Self {
        Self::Io(source)
    }
}

impl From<RawJournalError> for HistoryJournalError {
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

/// Single-writer append journal whose every accepted prefix is causally closed.
#[derive(Debug)]
pub struct HistoryJournal {
    raw: RawJournal,
    events: BTreeMap<HistoryEventId, HistoryEvent>,
    sequences: BTreeMap<HistoryEventId, u64>,
    report: HistoryOpenReport,
}

impl HistoryJournal {
    /// Open/create, exclusively lock, scan, checksum, canonically decode, and
    /// validate the complete causal prefix.
    pub fn open(
        path: impl AsRef<Path>,
        options: JournalOptions,
    ) -> Result<Self, HistoryJournalError> {
        let raw = RawJournal::open(path, RECORD_SPEC, options)?;
        let mut events = BTreeMap::new();
        let mut sequences = BTreeMap::new();
        for (sequence, bytes) in raw.records().iter().enumerate() {
            let sequence = sequence as u64;
            let event = decode_event(bytes).ok_or(HistoryJournalError::CorruptEvent {
                sequence,
                reason: "malformed or noncanonical history event",
            })?;
            admit(&events, &sequences, sequence, &event)?;
            if let Entry::Vacant(slot) = events.entry(event.id) {
                sequences.insert(event.id, sequence);
                slot.insert(event);
            }
        }
        let raw_report = raw.report();
        let report = HistoryOpenReport {
            recovered_records: raw.records().len(),
            recovered_events: events.len(),
            truncated_bytes: raw_report.truncated_bytes,
            created: raw_report.created,
        };
        Ok(Self {
            raw,
            events,
            sequences,
            report,
        })
    }

    /// Backing path.
    pub fn path(&self) -> &Path {
        self.raw.path()
    }

    /// Opening scan result.
    pub fn open_report(&self) -> HistoryOpenReport {
        self.report
    }

    /// Number of distinct accepted events.
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Whether no event has been accepted.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Events in deterministic id order, independent of physical arrival.
    pub fn events(&self) -> impl Iterator<Item = &HistoryEvent> {
        self.events.values()
    }

    /// Full id-to-event set used for convergence comparisons.
    pub fn event_set(&self) -> &BTreeMap<HistoryEventId, HistoryEvent> {
        &self.events
    }

    /// Look up one event by its complete id.
    pub fn event(&self, id: &HistoryEventId) -> Option<&HistoryEvent> {
        self.events.get(id)
    }

    /// Compare full id-to-event content, deliberately ignoring arrival order.
    pub fn same_event_set(&self, other: &Self) -> bool {
        self.events == other.events
    }

    /// Next physical sequence a new event would occupy.
    pub fn next_sequence(&self) -> u64 {
        self.raw.next_sequence()
    }

    /// Append at the next physical sequence. Re-appending the identical event
    /// is a no-write logical retry and returns its original sequence.
    pub fn append(&mut self, event: HistoryEvent) -> Result<AppendReceipt, HistoryJournalError> {
        self.append_at(self.next_sequence(), event)
    }

    /// Sequence-addressed, idempotently retryable causal append.
    ///
    /// When `sequence` is the next physical sequence and the exact event is
    /// already present, no duplicate record is written and the receipt names
    /// the event's original sequence. A retry at the original sequence is
    /// checked byte-for-byte by the underlying journal.
    pub fn append_at(
        &mut self,
        sequence: u64,
        event: HistoryEvent,
    ) -> Result<AppendReceipt, HistoryJournalError> {
        admit(&self.events, &self.sequences, sequence, &event)?;
        let bytes = encode_event(&event);

        if let Some(&existing_sequence) = self.sequences.get(&event.id) {
            if sequence == self.next_sequence() {
                return Ok(AppendReceipt {
                    sequence: existing_sequence,
                    status: AppendStatus::AlreadyPresent,
                });
            }
            return self.raw.append_at(sequence, &bytes).map_err(Into::into);
        }

        let receipt = self.raw.append_at(sequence, &bytes)?;
        if receipt.status == AppendStatus::Appended {
            self.sequences.insert(event.id, sequence);
            self.events.insert(event.id, event);
        }
        Ok(receipt)
    }

    /// Strengthen durability independently of the configured append policy.
    pub fn sync(&mut self, policy: SyncPolicy) -> Result<(), HistoryJournalError> {
        self.raw.sync(policy).map_err(Into::into)
    }
}

/// Outcome of one delivery to [`BufferedHistoryJournal`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HistoryDeliveryStatus {
    /// The event was appended to the causally closed physical journal.
    Appended,
    /// The event is waiting in the bounded, non-durable missing-parent buffer.
    Buffered,
    /// The exact complete event was already accepted or buffered.
    Retry,
}

/// Receipt for one bounded delivery.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HistoryDeliveryReceipt {
    /// Immediate disposition of the presented event.
    pub status: HistoryDeliveryStatus,
    /// Physical sequence for an immediate append or accepted retry.
    pub sequence: Option<u64>,
    /// Number of older buffered events causally drained after this delivery.
    pub drained: usize,
}

/// A causal history journal with an explicit bounded **volatile** out-of-order
/// endpoint.
///
/// Only causally ready events reach the checksummed [`HistoryJournal`]. Missing
/// parent events live in `pending` until a later delivery makes them ready.
/// The buffer is intentionally in-memory and non-authoritative: reopening
/// reconstructs the causally closed physical prefix and starts with no pending
/// events. A transport which needs pending durability must journal its arrival
/// queue separately and define that queue's own authority/recovery contract.
/// That durable arrival queue is not implemented here. In particular, this is
/// not a refinement of Lean `PersistentHistoryRuntime.deliverySchema`, whose
/// authoritative arrival cursor can replay/checkpoint buffered arrivals.
#[derive(Debug)]
pub struct BufferedHistoryJournal {
    journal: HistoryJournal,
    pending: BTreeMap<HistoryEventId, HistoryEvent>,
    capacity: usize,
}

impl BufferedHistoryJournal {
    /// Open the durable causal prefix with an empty non-durable pending buffer.
    pub fn open(
        path: impl AsRef<Path>,
        options: JournalOptions,
        capacity: usize,
    ) -> Result<Self, HistoryJournalError> {
        Ok(Self {
            journal: HistoryJournal::open(path, options)?,
            pending: BTreeMap::new(),
            capacity,
        })
    }

    /// The causally closed durable journal.
    pub fn journal(&self) -> &HistoryJournal {
        &self.journal
    }

    /// Mutable durable journal access, for explicit synchronization.
    pub fn journal_mut(&mut self) -> &mut HistoryJournal {
        &mut self.journal
    }

    /// Caller-selected maximum number of pending complete events.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Number of currently buffered events.
    pub fn pending_len(&self) -> usize {
        self.pending.len()
    }

    /// Whether no missing-parent events remain buffered.
    pub fn is_settled(&self) -> bool {
        self.pending.is_empty()
    }

    /// Pending events in deterministic id order.
    pub fn pending(&self) -> impl Iterator<Item = &HistoryEvent> {
        self.pending.values()
    }

    /// Compare full durable event content, deliberately ignoring arrival and
    /// physical append order. Callers normally require both endpoints settled.
    pub fn same_event_set(&self, other: &Self) -> bool {
        self.journal.same_event_set(&other.journal)
    }

    /// Require both volatile buffers empty before comparing the full durable
    /// event sets. This is the endpoint convergence predicate.
    pub fn settled_same_event_set(&self, other: &Self) -> bool {
        self.is_settled() && other.is_settled() && self.same_event_set(other)
    }

    /// Receive one caller-identified complete event.
    ///
    /// Identifiers are equality keys, not authentication. Exact retry is a
    /// no-op across accepted and pending stores; different content under either
    /// key is refused. A ready event is durably appended and then drains every
    /// now-ready buffered layer in deterministic id order.
    pub fn receive(
        &mut self,
        event: HistoryEvent,
    ) -> Result<HistoryDeliveryReceipt, HistoryJournalError> {
        if let Some(existing) = self.journal.event(&event.id) {
            if existing != &event {
                return Err(HistoryJournalError::IdCollision {
                    id: event.id,
                    existing_sequence: self.journal.sequences[&event.id],
                    incoming_sequence: self.journal.next_sequence(),
                });
            }
            return Ok(HistoryDeliveryReceipt {
                status: HistoryDeliveryStatus::Retry,
                sequence: Some(self.journal.sequences[&event.id]),
                drained: 0,
            });
        }
        if let Some(existing) = self.pending.get(&event.id) {
            if existing != &event {
                return Err(HistoryJournalError::PendingIdCollision { id: event.id });
            }
            return Ok(HistoryDeliveryReceipt {
                status: HistoryDeliveryStatus::Retry,
                sequence: None,
                drained: 0,
            });
        }

        let ready = event
            .parents
            .iter()
            .all(|parent| self.journal.event(parent).is_some());
        if !ready {
            if self.pending.len() >= self.capacity {
                return Err(HistoryJournalError::BufferFull {
                    capacity: self.capacity,
                });
            }
            self.pending.insert(event.id, event);
            return Ok(HistoryDeliveryReceipt {
                status: HistoryDeliveryStatus::Buffered,
                sequence: None,
                drained: 0,
            });
        }

        let receipt = self.journal.append(event)?;
        let drained = self.drain_ready()?;
        Ok(HistoryDeliveryReceipt {
            status: HistoryDeliveryStatus::Appended,
            sequence: Some(receipt.sequence),
            drained,
        })
    }

    fn drain_ready(&mut self) -> Result<usize, HistoryJournalError> {
        let mut drained = 0;
        loop {
            let ready = self
                .pending
                .iter()
                .find(|(_, event)| {
                    event
                        .parents
                        .iter()
                        .all(|parent| self.journal.event(parent).is_some())
                })
                .map(|(id, event)| (*id, event.clone()));
            let Some((id, event)) = ready else {
                return Ok(drained);
            };
            self.journal.append(event)?;
            self.pending.remove(&id);
            drained += 1;
        }
    }
}

fn validate_parents(
    id: &HistoryEventId,
    parents: &[HistoryEventId],
) -> Result<(), HistoryEventError> {
    if parents.iter().any(|parent| parent == id) {
        return Err(HistoryEventError::SelfParent);
    }
    if parents.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(HistoryEventError::ParentsNotStrictlyIncreasing);
    }
    Ok(())
}

fn admit(
    events: &BTreeMap<HistoryEventId, HistoryEvent>,
    sequences: &BTreeMap<HistoryEventId, u64>,
    sequence: u64,
    event: &HistoryEvent,
) -> Result<(), HistoryJournalError> {
    if let Some(existing) = events.get(&event.id) {
        if existing != event {
            return Err(HistoryJournalError::IdCollision {
                id: event.id,
                existing_sequence: sequences[&event.id],
                incoming_sequence: sequence,
            });
        }
        return Ok(());
    }
    for parent in &event.parents {
        if !events.contains_key(parent) {
            return Err(HistoryJournalError::MissingParent {
                sequence,
                event: event.id,
                parent: *parent,
            });
        }
    }
    Ok(())
}

fn encode_event(event: &HistoryEvent) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(
        1 + ID_BYTES + U64_BYTES + event.parents.len() * ID_BYTES + U64_BYTES + event.payload.len(),
    );
    bytes.push(EVENT_FORMAT_VERSION);
    bytes.extend_from_slice(&event.id);
    bytes.extend_from_slice(&(event.parents.len() as u64).to_le_bytes());
    for parent in &event.parents {
        bytes.extend_from_slice(parent);
    }
    bytes.extend_from_slice(&(event.payload.len() as u64).to_le_bytes());
    bytes.extend_from_slice(&event.payload);
    bytes
}

fn decode_event(bytes: &[u8]) -> Option<HistoryEvent> {
    let mut cursor = Cursor::new(bytes);
    if cursor.byte()? != EVENT_FORMAT_VERSION {
        return None;
    }
    let id = cursor.id()?;
    let parent_count = cursor.count(ID_BYTES)?;
    let mut parents = Vec::with_capacity(parent_count);
    for _ in 0..parent_count {
        parents.push(cursor.id()?);
    }
    let payload_len = cursor.count(1)?;
    let payload = cursor.take(payload_len)?.to_vec();
    if !cursor.is_empty() {
        return None;
    }
    let event = HistoryEvent::new(id, parents, payload).ok()?;
    (encode_event(&event) == bytes).then_some(event)
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

    fn take(&mut self, count: usize) -> Option<&'a [u8]> {
        let end = self.offset.checked_add(count)?;
        let slice = self.bytes.get(self.offset..end)?;
        self.offset = end;
        Some(slice)
    }

    fn byte(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }

    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(U64_BYTES)?.try_into().ok()?))
    }

    fn id(&mut self) -> Option<HistoryEventId> {
        self.take(ID_BYTES)?.try_into().ok()
    }

    fn count(&mut self, minimum_item_bytes: usize) -> Option<usize> {
        let count = usize::try_from(self.u64()?).ok()?;
        let needed = count.checked_mul(minimum_item_bytes)?;
        (needed <= self.bytes.len().saturating_sub(self.offset)).then_some(count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::persistence::TornTailPolicy;
    use std::fs;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

    struct TempFile(PathBuf);

    impl TempFile {
        fn new(label: &str) -> Self {
            let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "uwueave-history-{label}-{}-{nonce}.journal",
                std::process::id()
            ));
            let _ = fs::remove_file(&path);
            Self(path)
        }
    }

    impl Drop for TempFile {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    fn options(torn_tail: TornTailPolicy) -> JournalOptions {
        JournalOptions {
            torn_tail,
            sync: SyncPolicy::Buffered,
            ..JournalOptions::default()
        }
    }

    fn event(id: u8, parents: &[u8], payload: &[u8]) -> HistoryEvent {
        HistoryEvent::new(
            [id; ID_BYTES],
            parents.iter().map(|byte| [*byte; ID_BYTES]).collect(),
            payload.to_vec(),
        )
        .unwrap()
    }

    #[test]
    fn canonical_parent_set_refuses_self_duplicates_and_reordering() {
        assert_eq!(
            HistoryEvent::new([2; ID_BYTES], vec![[2; ID_BYTES]], vec![]),
            Err(HistoryEventError::SelfParent)
        );
        assert_eq!(
            HistoryEvent::new([3; ID_BYTES], vec![[1; ID_BYTES], [1; ID_BYTES]], vec![]),
            Err(HistoryEventError::ParentsNotStrictlyIncreasing)
        );
        assert_eq!(
            HistoryEvent::new([3; ID_BYTES], vec![[2; ID_BYTES], [1; ID_BYTES]], vec![]),
            Err(HistoryEventError::ParentsNotStrictlyIncreasing)
        );
    }

    #[test]
    fn causal_append_retry_duplicate_collision_and_reopen_are_exact() {
        let temp = TempFile::new("append-reopen");
        let root = event(1, &[], b"root");
        let child = event(2, &[1], b"child");
        let orphan = event(3, &[9], b"orphan");
        {
            let mut journal =
                HistoryJournal::open(&temp.0, options(TornTailPolicy::Refuse)).unwrap();
            assert_eq!(
                journal.append(root.clone()).unwrap().status,
                AppendStatus::Appended
            );
            let one_record_bytes = fs::metadata(&temp.0).unwrap().len();

            assert_eq!(
                journal.append_at(0, root.clone()).unwrap(),
                AppendReceipt {
                    sequence: 0,
                    status: AppendStatus::AlreadyPresent
                }
            );
            assert_eq!(
                journal.append(root.clone()).unwrap(),
                AppendReceipt {
                    sequence: 0,
                    status: AppendStatus::AlreadyPresent
                }
            );
            assert_eq!(fs::metadata(&temp.0).unwrap().len(), one_record_bytes);

            assert!(matches!(
                journal.append(orphan),
                Err(HistoryJournalError::MissingParent { parent, .. }) if parent == [9; ID_BYTES]
            ));
            assert_eq!(journal.append(child.clone()).unwrap().sequence, 1);
            assert!(matches!(
                journal.append(event(2, &[1], b"forged child")),
                Err(HistoryJournalError::IdCollision {
                    id,
                    existing_sequence: 1,
                    incoming_sequence: 2,
                }) if id == [2; ID_BYTES]
            ));
        }

        let reopened = HistoryJournal::open(&temp.0, options(TornTailPolicy::Refuse)).unwrap();
        assert_eq!(reopened.len(), 2);
        assert_eq!(reopened.event(&root.id()), Some(&root));
        assert_eq!(reopened.event(&child.id()), Some(&child));
        assert_eq!(reopened.next_sequence(), 2);
        assert_eq!(
            reopened.open_report(),
            HistoryOpenReport {
                recovered_records: 2,
                recovered_events: 2,
                truncated_bytes: 0,
                created: false,
            }
        );
    }

    #[test]
    fn same_event_set_converges_across_arrival_orders_and_compares_content() {
        let left_path = TempFile::new("converge-left");
        let right_path = TempFile::new("converge-right");
        let root = event(1, &[], b"root");
        let a = event(2, &[1], b"a");
        let b = event(3, &[1], b"b");
        let mut left = HistoryJournal::open(&left_path.0, options(TornTailPolicy::Refuse)).unwrap();
        let mut right =
            HistoryJournal::open(&right_path.0, options(TornTailPolicy::Refuse)).unwrap();
        for event in [root.clone(), a.clone(), b.clone()] {
            left.append(event).unwrap();
        }
        for event in [root, b, a] {
            right.append(event).unwrap();
        }
        assert!(left.same_event_set(&right));
        assert_eq!(left.event_set(), right.event_set());

        let different_path = TempFile::new("converge-content");
        let mut different =
            HistoryJournal::open(&different_path.0, options(TornTailPolicy::Refuse)).unwrap();
        different.append(event(1, &[], b"different root")).unwrap();
        assert!(!left.same_event_set(&different));
    }

    #[test]
    fn torn_tail_refuses_or_recovers_exact_complete_causal_prefix() {
        let temp = TempFile::new("torn");
        let root = event(1, &[], b"root");
        let child = event(2, &[1], b"child");
        let prefix_len;
        {
            let mut journal =
                HistoryJournal::open(&temp.0, options(TornTailPolicy::Refuse)).unwrap();
            journal.append(root.clone()).unwrap();
            prefix_len = fs::metadata(&temp.0).unwrap().len() as usize;
            journal.append(child).unwrap();
        }
        let complete = fs::read(&temp.0).unwrap();
        fs::write(&temp.0, &complete[..prefix_len + 10]).unwrap();
        assert!(matches!(
            HistoryJournal::open(&temp.0, options(TornTailPolicy::Refuse)),
            Err(HistoryJournalError::TornTail { bytes: 10, .. })
        ));
        let recovered = HistoryJournal::open(&temp.0, options(TornTailPolicy::Truncate)).unwrap();
        assert_eq!(recovered.events().collect::<Vec<_>>(), vec![&root]);
        assert_eq!(recovered.open_report().truncated_bytes, 10);
        drop(recovered);
        assert_eq!(fs::metadata(&temp.0).unwrap().len() as usize, prefix_len);
    }

    #[test]
    fn complete_physical_corruption_is_never_treated_as_a_torn_tail() {
        let temp = TempFile::new("physical-corrupt");
        {
            let mut journal =
                HistoryJournal::open(&temp.0, options(TornTailPolicy::Refuse)).unwrap();
            journal.append(event(1, &[], b"payload")).unwrap();
        }
        let mut bytes = fs::read(&temp.0).unwrap();
        bytes[56 + 1 + ID_BYTES + U64_BYTES + U64_BYTES] ^= 0x80;
        fs::write(&temp.0, bytes).unwrap();
        assert!(matches!(
            HistoryJournal::open(&temp.0, options(TornTailPolicy::Truncate)),
            Err(HistoryJournalError::CorruptPhysical { sequence: 0, .. })
        ));
    }

    #[test]
    fn checksummed_noncanonical_missing_parent_and_collision_records_refuse_on_reopen() {
        let malformed_path = TempFile::new("logical-corrupt");
        {
            let mut raw = RawJournal::open(
                &malformed_path.0,
                RECORD_SPEC,
                options(TornTailPolicy::Refuse),
            )
            .unwrap();
            raw.append_at(0, &[99]).unwrap();
        }
        assert!(matches!(
            HistoryJournal::open(&malformed_path.0, options(TornTailPolicy::Truncate)),
            Err(HistoryJournalError::CorruptEvent { sequence: 0, .. })
        ));

        let orphan_path = TempFile::new("reopen-orphan");
        {
            let mut raw =
                RawJournal::open(&orphan_path.0, RECORD_SPEC, options(TornTailPolicy::Refuse))
                    .unwrap();
            raw.append_at(0, &encode_event(&event(2, &[1], b"orphan")))
                .unwrap();
        }
        assert!(matches!(
            HistoryJournal::open(&orphan_path.0, options(TornTailPolicy::Truncate)),
            Err(HistoryJournalError::MissingParent { sequence: 0, .. })
        ));

        let collision_path = TempFile::new("reopen-collision");
        {
            let mut raw = RawJournal::open(
                &collision_path.0,
                RECORD_SPEC,
                options(TornTailPolicy::Refuse),
            )
            .unwrap();
            raw.append_at(0, &encode_event(&event(1, &[], b"one")))
                .unwrap();
            raw.append_at(1, &encode_event(&event(1, &[], b"two")))
                .unwrap();
        }
        assert!(matches!(
            HistoryJournal::open(&collision_path.0, options(TornTailPolicy::Truncate)),
            Err(HistoryJournalError::IdCollision {
                existing_sequence: 0,
                incoming_sequence: 1,
                ..
            })
        ));
    }

    #[test]
    fn bounded_reverse_criss_cross_drains_and_converges() {
        let causal_path = TempFile::new("buffered-criss-cross-causal");
        let reverse_path = TempFile::new("buffered-criss-cross-reverse");
        let root = event(1, &[], b"root");
        let left = event(2, &[1], b"left");
        let right = event(3, &[1], b"right");
        let merge_left = event(4, &[2, 3], b"merge-left");
        let merge_right = event(5, &[2, 3], b"merge-right");
        let tip = event(6, &[4, 5], b"merge-tip");
        let causal = [
            root.clone(),
            left.clone(),
            right.clone(),
            merge_left.clone(),
            merge_right.clone(),
            tip.clone(),
        ];
        let reverse = [tip, merge_right, merge_left, right, left, root];

        let mut causal_journal =
            BufferedHistoryJournal::open(&causal_path.0, options(TornTailPolicy::Refuse), 5)
                .unwrap();
        for event in causal {
            assert_eq!(
                causal_journal.receive(event).unwrap().status,
                HistoryDeliveryStatus::Appended
            );
        }

        let mut reverse_journal =
            BufferedHistoryJournal::open(&reverse_path.0, options(TornTailPolicy::Refuse), 5)
                .unwrap();
        for event in &reverse[..5] {
            assert_eq!(
                reverse_journal.receive(event.clone()).unwrap().status,
                HistoryDeliveryStatus::Buffered
            );
        }
        let root_receipt = reverse_journal.receive(reverse[5].clone()).unwrap();
        assert_eq!(root_receipt.status, HistoryDeliveryStatus::Appended);
        assert_eq!(root_receipt.drained, 5);
        assert!(causal_journal.settled_same_event_set(&reverse_journal));
        assert_eq!(causal_journal.journal().len(), 6);
        assert_eq!(reverse_journal.journal().len(), 6);

        drop(reverse_journal);
        let reopened =
            BufferedHistoryJournal::open(&reverse_path.0, options(TornTailPolicy::Refuse), 5)
                .unwrap();
        assert!(reopened.is_settled());
        assert_eq!(reopened.journal().len(), 6);
        assert!(causal_journal.settled_same_event_set(&reopened));
    }

    #[test]
    fn bounded_buffer_retries_collisions_capacity_and_reopen_loss_are_exact() {
        let path = TempFile::new("buffered-policy");
        let orphan = event(2, &[1], b"child");
        {
            let mut buffered =
                BufferedHistoryJournal::open(&path.0, options(TornTailPolicy::Refuse), 1).unwrap();
            assert_eq!(
                buffered.receive(orphan.clone()).unwrap(),
                HistoryDeliveryReceipt {
                    status: HistoryDeliveryStatus::Buffered,
                    sequence: None,
                    drained: 0,
                }
            );
            assert_eq!(
                buffered.receive(orphan.clone()).unwrap().status,
                HistoryDeliveryStatus::Retry
            );
            assert!(matches!(
                buffered.receive(event(2, &[1], b"forged")),
                Err(HistoryJournalError::PendingIdCollision { id }) if id == [2; ID_BYTES]
            ));
            assert!(matches!(
                buffered.receive(event(3, &[1], b"second")),
                Err(HistoryJournalError::BufferFull { capacity: 1 })
            ));
            assert!(!buffered.settled_same_event_set(&buffered));
            assert_eq!(buffered.journal().len(), 0);
            assert_eq!(fs::metadata(&path.0).unwrap().len(), 0);
        }

        // Pending arrivals are intentionally not authoritative and disappear
        // on reopen; the physical journal remains the empty causal prefix.
        let mut reopened =
            BufferedHistoryJournal::open(&path.0, options(TornTailPolicy::Refuse), 1).unwrap();
        assert!(reopened.is_settled());
        assert_eq!(reopened.pending_len(), 0);
        assert_eq!(reopened.journal().len(), 0);

        assert_eq!(
            reopened.receive(event(1, &[], b"root")).unwrap().status,
            HistoryDeliveryStatus::Appended
        );
        assert_eq!(
            reopened.receive(orphan.clone()).unwrap().status,
            HistoryDeliveryStatus::Appended
        );
        assert_eq!(
            reopened.receive(orphan).unwrap().status,
            HistoryDeliveryStatus::Retry
        );
        assert!(matches!(
            reopened.receive(event(2, &[1], b"forged accepted")),
            Err(HistoryJournalError::IdCollision {
                existing_sequence: 1,
                ..
            })
        ));
    }
}
