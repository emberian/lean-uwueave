//! Filesystem persistence with explicit recovery and synchronization policies.
//!
//! The two stores in this module intentionally do not share a wire format:
//!
//! * [`ArtifactJournal`] stores the exact bytes produced by Lean's
//!   `Preo.ArtifactDurable.projectionBytes` as unchanged payloads inside a
//!   checksummed physical journal. Direct logical stream import/export remains
//!   exact frame concatenation. Rust classifies the v2 envelope and delegates
//!   exact canonical payload acceptance to Lean; there is no second semantic
//!   decoder here.
//! * [`DocumentJournal`] owns a separate, checksummed operation/event and
//!   checkpoint log. Its byte records are a runtime storage format, not a
//!   Preoscript artifact schema.
//!
//! These implementations and their fault-injection tests are deployment
//! evidence. They are not a theorem about a filesystem, a drive write cache,
//! atomic sectors, or power-loss behavior.
//!
//! ## Physical contract
//!
//! Both physical files use distinct eight-byte markers and checksum domains.
//! A record is `marker | sequence:u64le | length:u64le | header-blake3 |
//! body | body-blake3`. Sequences start at zero and are contiguous. The
//! configured maximum is checked before allocating the body. An append names
//! its sequence, so reopening after an uncertain result can retry the same
//! `(sequence, body)` idempotently; the same sequence with different bytes and
//! sequence gaps refuse.
//!
//! One exclusive [`std::fs::File::try_lock`] is held for the handle's lifetime.
//! The lock may be advisory, so all writers must use this API. A checksum,
//! marker, or sequence failure in any complete record—including the last—is
//! corruption and is never truncated. Only an EOF-short final record prefix
//! is governed by [`TornTailPolicy`]; a corruption wholly inside bytes that
//! were never completed cannot be distinguished from a tear.
//!
//! [`SyncPolicy::SyncData`] and [`SyncPolicy::SyncAll`] inherit the host
//! platform's `File` promises. `SyncAll` also syncs the parent directory on
//! every open (including after this API creates a new journal name). Directory
//! handles and syncing are platform capabilities; Windows portability remains
//! open. It does not claim atomic sectors, controller-cache persistence, or
//! that a non-cooperating writer respects the lock.
//!
//! The bounds here are per-record, plus a stricter pre-FFI artifact-frame
//! bound. Total file bytes and record count are not yet bounded. Paths are
//! caller-trusted rather than symlink-hardened. Checksums detect accidental
//! corruption but neither authenticate a writer nor pin a journal head, so
//! rollback detection and authenticated recovery remain separate open work.
//!
//! The current backend is a small `std` + BLAKE3 append log because it most
//! directly exercises the proved complete-prefix/torn-tail model while making
//! every physical decision visible. A future transactional backend (for
//! example `redb`) should implement a separate `AtomicCommitStore`-style
//! adapter and differential tests; it must not silently reuse either wire
//! format or turn a database transaction into a durability theorem.

mod artifact;
mod document;
mod record;

pub use artifact::{
    decode_artifact_frame_stream, encode_artifact_frame_stream, ArtifactFrame, ArtifactFrameError,
    ArtifactJournal, ArtifactJournalError, ArtifactOpenReport, ArtifactStreamError,
    ARTIFACT_DOMAIN, ARTIFACT_FORMAT_VERSION, MAX_ARTIFACT_FRAME_BYTES,
};
pub use document::{
    DocumentEntry, DocumentEntryKind, DocumentJournal, DocumentJournalError, DocumentOpenReport,
    DocumentReplay, DocumentReplayError,
};

/// Default maximum size of one physical journal record (64 MiB).
pub const DEFAULT_MAX_RECORD_BYTES: u64 = 64 * 1024 * 1024;

/// Common opening and append policy for both physical journals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JournalOptions {
    /// What to do with one syntactically torn final physical record.
    pub torn_tail: TornTailPolicy,
    /// Synchronization requested after appends and recovery truncation.
    pub sync: SyncPolicy,
    /// Allocation/record bound enforced before a body is read or appended.
    pub max_record_bytes: u64,
}

impl Default for JournalOptions {
    fn default() -> Self {
        Self {
            torn_tail: TornTailPolicy::Refuse,
            sync: SyncPolicy::SyncData,
            max_record_bytes: DEFAULT_MAX_RECORD_BYTES,
        }
    }
}

/// Whether an idempotent sequence-addressed append wrote a new record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AppendStatus {
    /// The requested sequence was the next sequence and was appended.
    Appended,
    /// That sequence already held byte-for-byte identical content.
    AlreadyPresent,
}

/// Receipt for a sequence-addressed append.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AppendReceipt {
    /// Internally allocated, contiguous physical record sequence.
    pub sequence: u64,
    /// Whether this call wrote or recognized an idempotent retry.
    pub status: AppendStatus,
}

/// What opening a journal should do with one syntactically torn final record.
///
/// Corrupt complete records and corruption before the final record are always
/// refused. Recovery never scans past a refused record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TornTailPolicy {
    /// Opening fails and leaves the file untouched.
    Refuse,
    /// Keep the complete prefix and physically truncate the torn suffix before
    /// permitting another append.
    Truncate,
}

/// The persistence action performed after an append.
///
/// `flush`, `sync_data`, and `sync_all` have the meanings supplied by
/// [`std::fs::File`]. In particular, this enum does not manufacture a
/// filesystem or hardware durability theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyncPolicy {
    /// Return after `write_all`; userspace buffering is not used by these
    /// journals, but no flush or sync syscall is requested.
    Buffered,
    /// Call [`std::io::Write::flush`].
    Flush,
    /// Flush, then call [`std::fs::File::sync_data`].
    SyncData,
    /// Flush, then call [`std::fs::File::sync_all`].
    SyncAll,
}
