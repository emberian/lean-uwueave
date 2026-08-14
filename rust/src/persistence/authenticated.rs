//! Authenticated-only move admission persistence.
//!
//! This wire is intentionally isolated from the legacy `DocumentJournal`.
//! Every record is one caller-checked UWV4 kind-3 request, its exact Lean
//! projection, the concrete resolved [`MoveOp`], and the admission context it
//! used. Storage checks its own canonical envelope, hash chain, and atomic
//! nonce/operation-id indexes. It does not parse UWV4, verify signatures or
//! context commitments, or turn an unpinned reopen into a secure ready state.

use super::record::{RawJournal, RawJournalError, RecordSpec};
use super::{AppendReceipt, JournalOptions, SyncPolicy};
use crate::MoveOp;
use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::Path;

const RECORD_SPEC: RecordSpec = RecordSpec {
    marker: *b"UWAMV401",
    hash_domain: b"uwueave.authenticated-move-journal.v1",
};
const RECORD_VERSION: u8 = 1;
const CHAIN_DOMAIN: &[u8] = b"uwueave.authenticated-move-journal.v1.chain\0";

/// Nonce scope projected by Lean from one context-bound UWV4 request.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct NonceKey {
    pub document: Vec<u8>,
    pub genesis: Vec<u8>,
    pub issuer: u64,
    pub key_epoch: u64,
    pub nonce: Vec<u8>,
}

/// Stable operation identity scoped to a document and genesis.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct OperationKey {
    pub document: Vec<u8>,
    pub genesis: Vec<u8>,
    pub operation_id: Vec<u8>,
}

/// Exact policy-bearing state reference signed by the kind-3 request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionContextRef {
    pub commitment: Vec<u8>,
    /// Framed digest of the exact execution weave and grant/revocation base.
    /// The digest is an identity label under collision resistance, not an
    /// authenticator; the signed context provider remains the authority.
    pub execution_binding: [u8; 32],
    pub resolver_policy: u64,
    pub authority_policy: u64,
    pub membership_policy: u64,
    /// Hash-chain head immediately before this admission.
    pub previous_admission_commitment: Option<[u8; 32]>,
}

/// Exact Lean projection plus the concrete resolver result observed by the
/// checked runtime before storage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelObservation {
    pub signature_algorithm: u8,
    pub signing_bytes: Vec<u8>,
    pub signature: Vec<u8>,
    pub child_stable: Vec<u8>,
    pub child_index: u64,
    pub destination_stable: Option<Vec<u8>>,
    pub destination_index: Option<u64>,
    pub lamport: u64,
    pub replica: u64,
    pub cite: u64,
    pub resolved_move: MoveOp,
    pub admission: KernelAdmissionObservation,
}

/// Lean kernel observation permitted at the authenticated append boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelAdmissionObservation {
    Applied,
    SkippedCycle,
}

/// A runtime-created checked admission. Fields are private so callers outside
/// this crate cannot label arbitrary bytes as authenticated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedAdmission {
    canonical_request: Vec<u8>,
    nonce_key: NonceKey,
    operation_key: OperationKey,
    context: AdmissionContextRef,
    observation: KernelObservation,
}

impl CheckedAdmission {
    pub(crate) fn new(
        canonical_request: Vec<u8>,
        nonce_key: NonceKey,
        operation_key: OperationKey,
        context: AdmissionContextRef,
        observation: KernelObservation,
    ) -> Result<Self, &'static str> {
        let value = Self {
            canonical_request,
            nonce_key,
            operation_key,
            context,
            observation,
        };
        validate_admission(&value)?;
        Ok(value)
    }

    pub fn canonical_request(&self) -> &[u8] {
        &self.canonical_request
    }
    pub fn nonce_key(&self) -> &NonceKey {
        &self.nonce_key
    }
    pub fn operation_key(&self) -> &OperationKey {
        &self.operation_key
    }
    pub fn context(&self) -> &AdmissionContextRef {
        &self.context
    }
    pub fn observation(&self) -> &KernelObservation {
        &self.observation
    }
}

/// One recovered canonical authenticated-move record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthenticatedMoveRecord {
    pub sequence: u64,
    pub commitment: [u8; 32],
    admission: CheckedAdmission,
}

impl AuthenticatedMoveRecord {
    pub fn admission(&self) -> &CheckedAdmission {
        &self.admission
    }
}

/// Externally persisted pin required to detect a clean suffix rollback.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecoveryExpectation {
    pub last_sequence: Option<u64>,
    pub head_commitment: Option<[u8; 32]>,
}

impl RecoveryExpectation {
    pub const EMPTY: Self = Self {
        last_sequence: None,
        head_commitment: None,
    };
}

/// Result of applying one checked admission to both durable indexes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StoreDecision {
    Fresh {
        receipt: AppendReceipt,
        head_commitment: [u8; 32],
    },
    Retry {
        existing_sequence: u64,
        head_commitment: [u8; 32],
    },
    NonceCollision {
        existing_sequence: u64,
    },
    OperationCollision {
        existing_sequence: u64,
    },
}

/// Read-only classification of an already-verified request against the two
/// recovered durable indexes. Exact signed-content bytes, rather than a hash,
/// distinguish retry from collision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StorePreview {
    Fresh,
    Retry { existing_sequence: u64 },
    NonceCollision { existing_sequence: u64 },
    OperationCollision { existing_sequence: u64 },
}

/// Result metadata from opening the authenticated-only journal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AuthenticatedOpenReport {
    pub recovered_records: usize,
    pub truncated_bytes: u64,
    pub created: bool,
    /// False for `open_unpinned`; such a handle exposes records for explicit
    /// revalidation but is not recovery evidence for a ready runtime.
    pub externally_pinned: bool,
}

#[derive(Debug)]
pub enum AuthenticatedJournalError {
    Io(io::Error),
    Locked,
    TornTail {
        offset: u64,
        bytes: u64,
    },
    CorruptPhysical {
        sequence: u64,
        offset: u64,
        reason: &'static str,
    },
    CorruptRecord {
        sequence: u64,
        reason: &'static str,
    },
    BrokenChain {
        sequence: u64,
    },
    DuplicateNonce {
        sequence: u64,
        prior_sequence: u64,
    },
    DuplicateOperation {
        sequence: u64,
        prior_sequence: u64,
    },
    RecoveryHeadMismatch {
        expected_sequence: Option<u64>,
        actual_sequence: Option<u64>,
        expected_head: Option<[u8; 32]>,
        actual_head: Option<[u8; 32]>,
    },
    InvalidAdmission {
        reason: &'static str,
    },
    InvalidAdmissionPrefix {
        expected: Option<[u8; 32]>,
        actual: Option<[u8; 32]>,
    },
    /// An unpinned reopen is inspection-only until the runtime explicitly
    /// revalidates it against trusted recovery state.
    UnpinnedAppend,
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

impl fmt::Display for AuthenticatedJournalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "authenticated move journal failed: {self:?}")
    }
}
impl std::error::Error for AuthenticatedJournalError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}
impl From<RawJournalError> for AuthenticatedJournalError {
    fn from(value: RawJournalError) -> Self {
        match value {
            RawJournalError::Io(e) => Self::Io(e),
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
pub struct AuthenticatedMoveJournal {
    raw: RawJournal,
    records: Vec<AuthenticatedMoveRecord>,
    nonce_index: BTreeMap<NonceKey, (Vec<u8>, u64)>,
    operation_index: BTreeMap<OperationKey, (Vec<u8>, u64)>,
    report: AuthenticatedOpenReport,
}

impl AuthenticatedMoveJournal {
    pub fn open_pinned(
        path: impl AsRef<Path>,
        options: JournalOptions,
        expectation: RecoveryExpectation,
    ) -> Result<Self, AuthenticatedJournalError> {
        Self::open_inner(path, options, Some(expectation))
    }

    /// Open and validate the internal wire without supplying rollback evidence.
    /// The recovered records must be explicitly revalidated before use.
    pub fn open_unpinned(
        path: impl AsRef<Path>,
        options: JournalOptions,
    ) -> Result<Self, AuthenticatedJournalError> {
        Self::open_inner(path, options, None)
    }

    fn open_inner(
        path: impl AsRef<Path>,
        options: JournalOptions,
        expectation: Option<RecoveryExpectation>,
    ) -> Result<Self, AuthenticatedJournalError> {
        let raw = RawJournal::open(path, RECORD_SPEC, options)?;
        let mut records = Vec::with_capacity(raw.records().len());
        let mut nonce_index = BTreeMap::new();
        let mut operation_index = BTreeMap::new();
        let mut head = None;
        for (index, body) in raw.records().iter().enumerate() {
            let sequence =
                u64::try_from(index).map_err(|_| AuthenticatedJournalError::CorruptRecord {
                    sequence: u64::MAX,
                    reason: "record count exceeds sequence space",
                })?;
            let admission = decode_admission(body).ok_or(Self::record_error(sequence))?;
            if admission.context.previous_admission_commitment != head {
                return Err(AuthenticatedJournalError::BrokenChain { sequence });
            }
            let commitment = record_commitment(body);
            if let Some((_, prior_sequence)) = nonce_index.insert(
                admission.nonce_key.clone(),
                (admission.observation.signing_bytes.clone(), sequence),
            ) {
                return Err(AuthenticatedJournalError::DuplicateNonce {
                    sequence,
                    prior_sequence,
                });
            }
            if let Some((_, prior_sequence)) = operation_index.insert(
                admission.operation_key.clone(),
                (admission.observation.signing_bytes.clone(), sequence),
            ) {
                return Err(AuthenticatedJournalError::DuplicateOperation {
                    sequence,
                    prior_sequence,
                });
            }
            records.push(AuthenticatedMoveRecord {
                sequence,
                commitment,
                admission,
            });
            head = Some(commitment);
        }
        let actual_sequence = records.last().map(|r| r.sequence);
        if let Some(expected) = expectation {
            if expected.last_sequence != actual_sequence || expected.head_commitment != head {
                return Err(AuthenticatedJournalError::RecoveryHeadMismatch {
                    expected_sequence: expected.last_sequence,
                    actual_sequence,
                    expected_head: expected.head_commitment,
                    actual_head: head,
                });
            }
        }
        let raw_report = raw.report();
        let report = AuthenticatedOpenReport {
            recovered_records: records.len(),
            truncated_bytes: raw_report.truncated_bytes,
            created: raw_report.created,
            externally_pinned: expectation.is_some(),
        };
        Ok(Self {
            raw,
            records,
            nonce_index,
            operation_index,
            report,
        })
    }

    fn record_error(sequence: u64) -> AuthenticatedJournalError {
        AuthenticatedJournalError::CorruptRecord {
            sequence,
            reason: "malformed or noncanonical authenticated admission",
        }
    }

    pub fn path(&self) -> &Path {
        self.raw.path()
    }
    pub fn open_report(&self) -> AuthenticatedOpenReport {
        self.report
    }
    pub fn records(&self) -> &[AuthenticatedMoveRecord] {
        &self.records
    }
    pub fn next_sequence(&self) -> u64 {
        self.raw.next_sequence()
    }
    pub fn head_commitment(&self) -> Option<[u8; 32]> {
        self.records.last().map(|record| record.commitment)
    }
    pub fn recovery_expectation(&self) -> RecoveryExpectation {
        RecoveryExpectation {
            last_sequence: self.records.last().map(|record| record.sequence),
            head_commitment: self.head_commitment(),
        }
    }

    pub(crate) fn classify(
        &self,
        nonce_key: &NonceKey,
        operation_key: &OperationKey,
        signing_bytes: &[u8],
    ) -> StorePreview {
        if let Some((prior_bytes, prior_sequence)) = self.nonce_index.get(nonce_key) {
            return if prior_bytes == signing_bytes {
                StorePreview::Retry {
                    existing_sequence: *prior_sequence,
                }
            } else {
                StorePreview::NonceCollision {
                    existing_sequence: *prior_sequence,
                }
            };
        }
        if let Some((prior_bytes, prior_sequence)) = self.operation_index.get(operation_key) {
            return if prior_bytes == signing_bytes {
                StorePreview::Retry {
                    existing_sequence: *prior_sequence,
                }
            } else {
                StorePreview::OperationCollision {
                    existing_sequence: *prior_sequence,
                }
            };
        }
        StorePreview::Fresh
    }

    pub(crate) fn append_checked_at(
        &mut self,
        sequence: u64,
        admission: CheckedAdmission,
    ) -> Result<StoreDecision, AuthenticatedJournalError> {
        if !self.report.externally_pinned {
            return Err(AuthenticatedJournalError::UnpinnedAppend);
        }
        validate_admission(&admission)
            .map_err(|reason| AuthenticatedJournalError::InvalidAdmission { reason })?;
        match self.classify(
            &admission.nonce_key,
            &admission.operation_key,
            &admission.observation.signing_bytes,
        ) {
            StorePreview::Fresh => {}
            StorePreview::Retry { existing_sequence } => {
                return self.resync_verified_retry(existing_sequence);
            }
            StorePreview::NonceCollision { existing_sequence } => {
                return Ok(StoreDecision::NonceCollision { existing_sequence });
            }
            StorePreview::OperationCollision { existing_sequence } => {
                return Ok(StoreDecision::OperationCollision { existing_sequence });
            }
        }
        let expected_head = self.head_commitment();
        if admission.context.previous_admission_commitment != expected_head {
            return Err(AuthenticatedJournalError::InvalidAdmissionPrefix {
                expected: expected_head,
                actual: admission.context.previous_admission_commitment,
            });
        }
        let body = encode_admission(&admission);
        let commitment = record_commitment(&body);
        let receipt = self.raw.append_at(sequence, &body)?;
        if receipt.status == super::AppendStatus::Appended {
            self.nonce_index.insert(
                admission.nonce_key.clone(),
                (admission.observation.signing_bytes.clone(), sequence),
            );
            self.operation_index.insert(
                admission.operation_key.clone(),
                (admission.observation.signing_bytes.clone(), sequence),
            );
            self.records.push(AuthenticatedMoveRecord {
                sequence,
                commitment,
                admission,
            });
        }
        Ok(StoreDecision::Fresh {
            receipt,
            head_commitment: commitment,
        })
    }

    /// Re-run the configured physical durability action for a retry already
    /// classified and verified by the runtime. No new logical record or index
    /// entry is created.
    pub(crate) fn resync_verified_retry(
        &mut self,
        existing_sequence: u64,
    ) -> Result<StoreDecision, AuthenticatedJournalError> {
        if !self.report.externally_pinned {
            return Err(AuthenticatedJournalError::UnpinnedAppend);
        }
        self.resync_retry(existing_sequence)
    }

    fn resync_retry(
        &mut self,
        existing_sequence: u64,
    ) -> Result<StoreDecision, AuthenticatedJournalError> {
        let index = usize::try_from(existing_sequence).map_err(|_| {
            AuthenticatedJournalError::CorruptRecord {
                sequence: existing_sequence,
                reason: "indexed sequence exceeds host address space",
            }
        })?;
        let record = self
            .records
            .get(index)
            .ok_or(AuthenticatedJournalError::CorruptRecord {
                sequence: existing_sequence,
                reason: "indexed sequence has no recovered record",
            })?;
        let body = encode_admission(&record.admission);
        self.raw.append_at(existing_sequence, &body)?;
        Ok(StoreDecision::Retry {
            existing_sequence,
            head_commitment: self
                .head_commitment()
                .expect("retry requires existing record"),
        })
    }

    pub fn sync(&mut self, policy: SyncPolicy) -> Result<(), AuthenticatedJournalError> {
        self.raw.sync(policy).map_err(Into::into)
    }
}

fn validate_admission(value: &CheckedAdmission) -> Result<(), &'static str> {
    if !value.canonical_request.starts_with(b"UWV4\x04\x03") {
        return Err("request is not context-bound UWV4 kind 3");
    }
    if value.nonce_key.document.is_empty()
        || value.nonce_key.genesis.is_empty()
        || value.nonce_key.nonce.is_empty()
        || value.operation_key.operation_id.is_empty()
        || value.observation.signing_bytes.is_empty()
        || value.observation.signature.is_empty()
        || value.observation.child_stable.is_empty()
        || value.context.commitment.is_empty()
    {
        return Err("required authenticated field is empty");
    }
    if value.nonce_key.document != value.operation_key.document
        || value.nonce_key.genesis != value.operation_key.genesis
    {
        return Err("nonce and operation scopes disagree");
    }
    if value.observation.destination_stable.is_some()
        != value.observation.destination_index.is_some()
    {
        return Err("destination stable id and index disagree");
    }
    if matches!(value.observation.destination_stable.as_ref(), Some(id) if id.is_empty()) {
        return Err("destination stable id is empty");
    }
    if value.observation.replica != value.nonce_key.issuer
        || value.observation.lamport != value.observation.resolved_move.lamport
        || value.observation.replica != value.observation.resolved_move.replica
        || value.observation.cite != value.observation.resolved_move.cite
    {
        return Err("Lean projection and resolved move disagree");
    }
    Ok(())
}

fn record_commitment(body: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(CHAIN_DOMAIN);
    hasher.update(body);
    *hasher.finalize().as_bytes()
}

fn encode_admission(value: &CheckedAdmission) -> Vec<u8> {
    let mut out = vec![RECORD_VERSION];
    put_bytes(&mut out, &value.canonical_request);
    put_bytes(&mut out, &value.nonce_key.document);
    put_bytes(&mut out, &value.nonce_key.genesis);
    put_u64(&mut out, value.nonce_key.issuer);
    put_u64(&mut out, value.nonce_key.key_epoch);
    put_bytes(&mut out, &value.nonce_key.nonce);
    put_bytes(&mut out, &value.operation_key.document);
    put_bytes(&mut out, &value.operation_key.genesis);
    put_bytes(&mut out, &value.operation_key.operation_id);
    put_bytes(&mut out, &value.context.commitment);
    out.extend_from_slice(&value.context.execution_binding);
    put_u64(&mut out, value.context.resolver_policy);
    put_u64(&mut out, value.context.authority_policy);
    put_u64(&mut out, value.context.membership_policy);
    put_optional_hash(&mut out, value.context.previous_admission_commitment);
    out.push(value.observation.signature_algorithm);
    put_bytes(&mut out, &value.observation.signing_bytes);
    put_bytes(&mut out, &value.observation.signature);
    put_bytes(&mut out, &value.observation.child_stable);
    put_u64(&mut out, value.observation.child_index);
    put_optional_bytes(&mut out, value.observation.destination_stable.as_deref());
    put_optional_u64(&mut out, value.observation.destination_index);
    put_u64(&mut out, value.observation.lamport);
    put_u64(&mut out, value.observation.replica);
    put_u64(&mut out, value.observation.cite);
    put_move(&mut out, value.observation.resolved_move);
    out.push(match value.observation.admission {
        KernelAdmissionObservation::Applied => 0,
        KernelAdmissionObservation::SkippedCycle => 1,
    });
    out
}

fn decode_admission(bytes: &[u8]) -> Option<CheckedAdmission> {
    let mut c = Cursor { bytes, at: 0 };
    if c.byte()? != RECORD_VERSION {
        return None;
    }
    let value = CheckedAdmission {
        canonical_request: c.bytes()?,
        nonce_key: NonceKey {
            document: c.bytes()?,
            genesis: c.bytes()?,
            issuer: c.u64()?,
            key_epoch: c.u64()?,
            nonce: c.bytes()?,
        },
        operation_key: OperationKey {
            document: c.bytes()?,
            genesis: c.bytes()?,
            operation_id: c.bytes()?,
        },
        context: AdmissionContextRef {
            commitment: c.bytes()?,
            execution_binding: c.hash()?,
            resolver_policy: c.u64()?,
            authority_policy: c.u64()?,
            membership_policy: c.u64()?,
            previous_admission_commitment: c.optional_hash()?,
        },
        observation: KernelObservation {
            signature_algorithm: c.byte()?,
            signing_bytes: c.bytes()?,
            signature: c.bytes()?,
            child_stable: c.bytes()?,
            child_index: c.u64()?,
            destination_stable: c.optional_bytes()?,
            destination_index: c.optional_u64()?,
            lamport: c.u64()?,
            replica: c.u64()?,
            cite: c.u64()?,
            resolved_move: c.move_op()?,
            admission: match c.byte()? {
                0 => KernelAdmissionObservation::Applied,
                1 => KernelAdmissionObservation::SkippedCycle,
                _ => return None,
            },
        },
    };
    if !c.done() || validate_admission(&value).is_err() || encode_admission(&value) != bytes {
        None
    } else {
        Some(value)
    }
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}
fn put_bytes(out: &mut Vec<u8>, value: &[u8]) {
    // `Vec` is host-addressable, and therefore cannot exceed u64 on supported
    // targets. RawJournal still applies the configured per-record bound before
    // any bytes are written.
    let length = u64::try_from(value.len()).expect("Vec length exceeds u64");
    put_u64(out, length);
    out.extend_from_slice(value);
}
fn put_optional_u64(out: &mut Vec<u8>, value: Option<u64>) {
    match value {
        None => out.push(0),
        Some(v) => {
            out.push(1);
            put_u64(out, v);
        }
    }
}
fn put_optional_hash(out: &mut Vec<u8>, value: Option<[u8; 32]>) {
    match value {
        None => out.push(0),
        Some(v) => {
            out.push(1);
            out.extend_from_slice(&v);
        }
    }
}
fn put_optional_bytes(out: &mut Vec<u8>, value: Option<&[u8]>) {
    match value {
        None => out.push(0),
        Some(v) => {
            out.push(1);
            put_bytes(out, v);
        }
    }
}
fn put_move(out: &mut Vec<u8>, op: MoveOp) {
    put_u64(out, op.lamport);
    put_u64(out, op.replica);
    out.extend_from_slice(&op.child);
    put_optional_node(out, op.dest);
    put_u64(out, op.cite);
}
fn put_optional_node(out: &mut Vec<u8>, value: Option<[u8; 32]>) {
    match value {
        None => out.push(0),
        Some(v) => {
            out.push(1);
            out.extend_from_slice(&v);
        }
    }
}

struct Cursor<'a> {
    bytes: &'a [u8],
    at: usize,
}
impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.at.checked_add(n)?;
        let v = self.bytes.get(self.at..end)?;
        self.at = end;
        Some(v)
    }
    fn byte(&mut self) -> Option<u8> {
        Some(*self.take(1)?.first()?)
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn bytes(&mut self) -> Option<Vec<u8>> {
        let n = usize::try_from(self.u64()?).ok()?;
        Some(self.take(n)?.to_vec())
    }
    fn hash(&mut self) -> Option<[u8; 32]> {
        self.take(32)?.try_into().ok()
    }
    fn optional_u64(&mut self) -> Option<Option<u64>> {
        match self.byte()? {
            0 => Some(None),
            1 => Some(Some(self.u64()?)),
            _ => None,
        }
    }
    fn optional_hash(&mut self) -> Option<Option<[u8; 32]>> {
        match self.byte()? {
            0 => Some(None),
            1 => Some(Some(self.hash()?)),
            _ => None,
        }
    }
    fn optional_bytes(&mut self) -> Option<Option<Vec<u8>>> {
        match self.byte()? {
            0 => Some(None),
            1 => Some(Some(self.bytes()?)),
            _ => None,
        }
    }
    fn optional_node(&mut self) -> Option<Option<[u8; 32]>> {
        match self.byte()? {
            0 => Some(None),
            1 => Some(Some(self.hash()?)),
            _ => None,
        }
    }
    fn move_op(&mut self) -> Option<MoveOp> {
        Some(MoveOp {
            lamport: self.u64()?,
            replica: self.u64()?,
            child: self.hash()?,
            dest: self.optional_node()?,
            cite: self.u64()?,
        })
    }
    fn done(&self) -> bool {
        self.at == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::persistence::{AppendStatus, DocumentJournal, TornTailPolicy};
    use std::fs;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

    struct TempFile(PathBuf);
    impl TempFile {
        fn new(label: &str) -> Self {
            let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "uwueave-authenticated-{label}-{}-{nonce}.journal",
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

    fn admission(
        previous: Option<[u8; 32]>,
        nonce: u8,
        operation: u8,
        signed_content: u8,
        signature: u8,
    ) -> CheckedAdmission {
        CheckedAdmission::new(
            vec![b'U', b'W', b'V', b'4', 4, 3, signed_content, signature],
            NonceKey {
                document: vec![1, 2],
                genesis: vec![3, 4],
                issuer: 17,
                key_epoch: 2,
                nonce: vec![nonce],
            },
            OperationKey {
                document: vec![1, 2],
                genesis: vec![3, 4],
                operation_id: vec![operation],
            },
            AdmissionContextRef {
                // Deliberately not 32 bytes: the signed StableId is arbitrary
                // nonempty canonical bytes and storage preserves it exactly.
                commitment: vec![91, 92, 93],
                execution_binding: [94; 32],
                resolver_policy: 5,
                authority_policy: 6,
                membership_policy: 7,
                previous_admission_commitment: previous,
            },
            KernelObservation {
                signature_algorithm: 1,
                signing_bytes: vec![b'U', b'W', b'V', b'4', 4, 3, signed_content],
                signature: vec![signature],
                child_stable: vec![10, 11],
                child_index: 3,
                destination_stable: Some(vec![12, 13]),
                destination_index: Some(4),
                lamport: 9,
                replica: 17,
                cite: 7,
                resolved_move: MoveOp {
                    lamport: 9,
                    replica: 17,
                    child: [10; 32],
                    dest: Some([12; 32]),
                    cite: 7,
                },
                admission: KernelAdmissionObservation::Applied,
            },
        )
        .unwrap()
    }

    #[test]
    fn kind_three_and_arbitrary_context_roundtrip_but_kind_two_refuses() {
        let value = admission(None, 5, 21, 31, 41);
        let encoded = encode_admission(&value);
        let decoded = decode_admission(&encoded).unwrap();
        assert_eq!(decoded, value);
        assert_eq!(decoded.context().commitment, vec![91, 92, 93]);

        let mut wrong_kind = value;
        wrong_kind.canonical_request[5] = 2;
        assert_eq!(
            validate_admission(&wrong_kind),
            Err("request is not context-bound UWV4 kind 3")
        );
    }

    #[test]
    fn fresh_retry_and_both_collision_indexes_are_atomic() {
        let temp = TempFile::new("decisions");
        let mut journal = AuthenticatedMoveJournal::open_pinned(
            &temp.0,
            options(TornTailPolicy::Refuse),
            RecoveryExpectation::EMPTY,
        )
        .unwrap();
        let first = admission(None, 5, 21, 31, 41);
        assert_eq!(
            journal.classify(
                first.nonce_key(),
                first.operation_key(),
                &first.observation().signing_bytes,
            ),
            StorePreview::Fresh
        );
        let first_decision = journal.append_checked_at(0, first.clone()).unwrap();
        assert!(matches!(
            first_decision,
            StoreDecision::Fresh {
                receipt: AppendReceipt {
                    sequence: 0,
                    status: AppendStatus::Appended
                },
                ..
            }
        ));
        let before = fs::read(&temp.0).unwrap();

        // Signature bytes are outside signed-content identity. The exact same
        // signing bytes retry and re-sync the existing physical record.
        let retry = admission(None, 5, 21, 31, 99);
        let records_before_preview = journal.records().len();
        assert_eq!(
            journal.classify(
                retry.nonce_key(),
                retry.operation_key(),
                &retry.observation().signing_bytes,
            ),
            StorePreview::Retry {
                existing_sequence: 0
            }
        );
        assert_eq!(journal.records().len(), records_before_preview);
        assert!(matches!(
            journal.resync_verified_retry(0).unwrap(),
            StoreDecision::Retry {
                existing_sequence: 0,
                ..
            }
        ));
        assert_eq!(fs::read(&temp.0).unwrap(), before);
        assert!(matches!(
            journal.append_checked_at(1, retry).unwrap(),
            StoreDecision::Retry {
                existing_sequence: 0,
                ..
            }
        ));
        assert_eq!(fs::read(&temp.0).unwrap(), before);
        assert_eq!(journal.records().len(), 1);

        let nonce_collision = admission(journal.head_commitment(), 5, 22, 32, 42);
        assert_eq!(
            journal.classify(
                nonce_collision.nonce_key(),
                nonce_collision.operation_key(),
                &nonce_collision.observation().signing_bytes,
            ),
            StorePreview::NonceCollision {
                existing_sequence: 0
            }
        );
        assert_eq!(
            journal.append_checked_at(1, nonce_collision).unwrap(),
            StoreDecision::NonceCollision {
                existing_sequence: 0
            }
        );
        let operation_collision = admission(journal.head_commitment(), 6, 21, 32, 42);
        assert_eq!(
            journal.classify(
                operation_collision.nonce_key(),
                operation_collision.operation_key(),
                &operation_collision.observation().signing_bytes,
            ),
            StorePreview::OperationCollision {
                existing_sequence: 0
            }
        );
        assert_eq!(
            journal.append_checked_at(1, operation_collision).unwrap(),
            StoreDecision::OperationCollision {
                existing_sequence: 0
            }
        );
        assert_eq!(fs::read(&temp.0).unwrap(), before);
        assert_eq!(journal.next_sequence(), 1);
    }

    #[test]
    fn pinned_reopen_rebuilds_indexes_and_detects_clean_suffix_rollback() {
        let temp = TempFile::new("pinned");
        let first_len;
        let first_pin;
        let full_pin;
        {
            let mut journal = AuthenticatedMoveJournal::open_pinned(
                &temp.0,
                options(TornTailPolicy::Refuse),
                RecoveryExpectation::EMPTY,
            )
            .unwrap();
            journal
                .append_checked_at(0, admission(None, 5, 21, 31, 41))
                .unwrap();
            first_len = fs::metadata(&temp.0).unwrap().len();
            first_pin = journal.recovery_expectation();
            journal
                .append_checked_at(1, admission(journal.head_commitment(), 6, 22, 32, 42))
                .unwrap();
            full_pin = journal.recovery_expectation();
        }

        let reopened = AuthenticatedMoveJournal::open_pinned(
            &temp.0,
            options(TornTailPolicy::Refuse),
            full_pin,
        )
        .unwrap();
        assert!(reopened.open_report().externally_pinned);
        assert_eq!(reopened.records().len(), 2);
        assert_eq!(
            reopened.records()[0].admission().context().commitment,
            vec![91, 92, 93]
        );
        drop(reopened);

        let full = fs::read(&temp.0).unwrap();
        fs::write(&temp.0, &full[..first_len as usize]).unwrap();
        assert!(matches!(
            AuthenticatedMoveJournal::open_pinned(
                &temp.0,
                options(TornTailPolicy::Refuse),
                full_pin,
            ),
            Err(AuthenticatedJournalError::RecoveryHeadMismatch { .. })
        ));
        AuthenticatedMoveJournal::open_pinned(&temp.0, options(TornTailPolicy::Refuse), first_pin)
            .unwrap();
    }

    #[test]
    fn unpinned_recovery_is_inspection_only_and_torn_tail_is_policy_controlled() {
        let temp = TempFile::new("unpinned-torn");
        let complete;
        {
            let mut journal = AuthenticatedMoveJournal::open_pinned(
                &temp.0,
                options(TornTailPolicy::Refuse),
                RecoveryExpectation::EMPTY,
            )
            .unwrap();
            journal
                .append_checked_at(0, admission(None, 5, 21, 31, 41))
                .unwrap();
            complete = fs::read(&temp.0).unwrap();
        }
        let mut unpinned =
            AuthenticatedMoveJournal::open_unpinned(&temp.0, options(TornTailPolicy::Refuse))
                .unwrap();
        assert!(!unpinned.open_report().externally_pinned);
        assert!(matches!(
            unpinned.append_checked_at(1, admission(unpinned.head_commitment(), 6, 22, 32, 42),),
            Err(AuthenticatedJournalError::UnpinnedAppend)
        ));
        drop(unpinned);

        let mut torn = complete.clone();
        torn.extend_from_slice(b"UWAM");
        fs::write(&temp.0, torn).unwrap();
        assert!(matches!(
            AuthenticatedMoveJournal::open_unpinned(&temp.0, options(TornTailPolicy::Refuse),),
            Err(AuthenticatedJournalError::TornTail { bytes: 4, .. })
        ));
        let recovered =
            AuthenticatedMoveJournal::open_unpinned(&temp.0, options(TornTailPolicy::Truncate))
                .unwrap();
        assert_eq!(recovered.records().len(), 1);
        assert_eq!(fs::read(&temp.0).unwrap(), complete);
    }

    #[test]
    fn legacy_document_wire_cannot_open_as_authenticated() {
        let temp = TempFile::new("legacy-isolation");
        {
            let mut legacy =
                DocumentJournal::open(&temp.0, options(TornTailPolicy::Refuse)).unwrap();
            legacy.append_revocation(7).unwrap();
        }
        assert!(matches!(
            AuthenticatedMoveJournal::open_unpinned(&temp.0, options(TornTailPolicy::Refuse),),
            Err(AuthenticatedJournalError::CorruptPhysical {
                sequence: 0,
                reason: "wrong physical record marker",
                ..
            })
        ));
    }

    #[test]
    fn refused_oversized_append_preserves_prefix_and_indexes() {
        let temp = TempFile::new("bounded-refusal");
        let mut bounded = options(TornTailPolicy::Refuse);
        bounded.max_record_bytes = 16;
        let mut journal =
            AuthenticatedMoveJournal::open_pinned(&temp.0, bounded, RecoveryExpectation::EMPTY)
                .unwrap();
        let first = admission(None, 5, 21, 31, 41);
        assert!(matches!(
            journal.append_checked_at(0, first.clone()),
            Err(AuthenticatedJournalError::RecordTooLarge { maximum: 16, .. })
        ));
        assert_eq!(journal.next_sequence(), 0);
        assert!(journal.records().is_empty());
        assert!(fs::read(&temp.0).unwrap().is_empty());

        // If either index had changed before the physical append, these would
        // classify as Retry/Collision instead of reaching the same size gate.
        let collision = admission(None, 5, 22, 32, 42);
        assert!(matches!(
            journal.append_checked_at(0, collision),
            Err(AuthenticatedJournalError::RecordTooLarge { maximum: 16, .. })
        ));
        assert_eq!(journal.next_sequence(), 0);
        assert!(journal.records().is_empty());
    }
}
