//! Authenticated-only move admission persistence.
//!
//! This wire is intentionally isolated from the legacy `DocumentJournal`.
//! Every new record is one Lean-validated v2 admission certificate: the
//! caller's UWV4 kind-3 request, exact kind-4 projection response, normalized
//! host-stage receipts, exact FORMAT-v3 request/response trace, concrete
//! resolved [`MoveOp`], and the admission context it used. Storage preserves
//! the exact checker-accepted certificate bytes while checking its canonical
//! envelope, hash chain, and atomic nonce/operation-id indexes. A recovered
//! [`CheckedAdmission`] is only a canonical stored value: the ready runtime
//! must submit its exact certificate bytes to the Lean trace checker again
//! before provider replay or execution commit. Storage itself does not verify
//! signatures or context commitments and cannot turn an unpinned reopen into
//! a secure ready state.

use super::record::{RawJournal, RawJournalError, RecordSpec};
use super::{AppendReceipt, JournalOptions, SyncPolicy};
use crate::auth::LeanValidatedAdmissionTrace;
use crate::{MoveOp, NodeId};
use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::Path;

const RECORD_SPEC: RecordSpec = RecordSpec {
    marker: *b"UWAMV401",
    hash_domain: b"uwueave.authenticated-move-journal.v1",
};
const RECORD_VERSION: u8 = 2;
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
    /// Exact dense execution index space used to construct the FORMAT-v3
    /// request. Signed child/destination indices must select the concrete
    /// content-addressed nodes in `resolved_move` from this vector.
    pub execution_nodes: Vec<NodeId>,
    pub admission: KernelAdmissionObservation,
}

impl KernelObservation {
    pub fn execution_nodes(&self) -> &[NodeId] {
        &self.execution_nodes
    }
}

/// Lean kernel observation permitted at the authenticated append boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelAdmissionObservation {
    Applied,
    SkippedCycle,
}

/// Normalized evidence that every host-owned stage accepted the exact values
/// carried by the certificate.
///
/// These are deliberately first-order one-byte receipts rather than claims
/// inferred later from the presence of ordinary fields. Construction is
/// crate-private and occurs only after the runtime has consumed and matched
/// the corresponding provider receipt. The Lean trace checker requires every
/// canonical byte to be exactly `1`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdmissionStageReceipts {
    verification: bool,
    context: bool,
    resolution: bool,
    authority: bool,
    membership: bool,
}

impl AdmissionStageReceipts {
    pub(crate) const fn all_accepted() -> Self {
        Self {
            verification: true,
            context: true,
            resolution: true,
            authority: true,
            membership: true,
        }
    }

    pub const fn verification(&self) -> bool {
        self.verification
    }
    pub const fn context(&self) -> bool {
        self.context
    }
    pub const fn resolution(&self) -> bool {
        self.resolution
    }
    pub const fn authority(&self) -> bool {
        self.authority
    }
    pub const fn membership(&self) -> bool {
        self.membership
    }

    const fn all_are_accepted(&self) -> bool {
        self.verification && self.context && self.resolution && self.authority && self.membership
    }
}

/// Exact shipping-kernel evidence appended to the v2 admission certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionTrace {
    /// Exactly the canonical kind-3 request length, retained as the bound
    /// passed to the Lean projection endpoint. Larger equivalent bounds are
    /// noncanonical certificate spellings.
    projection_bound: u64,
    projection_response: Vec<u8>,
    format_v3_request: Vec<u8>,
    format_v3_response: Vec<u8>,
    selected_request_slot: u64,
    operation_was_new: bool,
    stage_receipts: AdmissionStageReceipts,
}

impl AdmissionTrace {
    pub(crate) fn new(
        projection_bound: u64,
        projection_response: Vec<u8>,
        format_v3_request: Vec<u8>,
        format_v3_response: Vec<u8>,
        selected_request_slot: u64,
        operation_was_new: bool,
        stage_receipts: AdmissionStageReceipts,
    ) -> Self {
        Self {
            projection_bound,
            projection_response,
            format_v3_request,
            format_v3_response,
            selected_request_slot,
            operation_was_new,
            stage_receipts,
        }
    }

    pub fn projection_bound(&self) -> u64 {
        self.projection_bound
    }
    pub fn projection_response(&self) -> &[u8] {
        &self.projection_response
    }
    pub fn format_v3_request(&self) -> &[u8] {
        &self.format_v3_request
    }
    pub fn format_v3_response(&self) -> &[u8] {
        &self.format_v3_response
    }
    pub fn selected_request_slot(&self) -> u64 {
        self.selected_request_slot
    }
    pub fn operation_was_new(&self) -> bool {
        self.operation_was_new
    }
    pub fn stage_receipts(&self) -> AdmissionStageReceipts {
        self.stage_receipts
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AdmissionFields {
    canonical_request: Vec<u8>,
    nonce_key: NonceKey,
    operation_key: OperationKey,
    context: AdmissionContextRef,
    observation: KernelObservation,
    trace: AdmissionTrace,
}

/// Canonical v2 bytes awaiting acceptance by the Lean trace checker.
///
/// This type is not admission evidence. It exists so `auth_runtime` can build
/// one exact byte string, submit that same string to Lean, and then consume
/// the opaque [`LeanValidatedAdmissionTrace`] token when constructing the
/// persistable value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UncheckedAdmissionCertificate {
    certificate_bytes: Vec<u8>,
}

impl UncheckedAdmissionCertificate {
    pub(crate) fn new(
        canonical_request: Vec<u8>,
        nonce_key: NonceKey,
        operation_key: OperationKey,
        context: AdmissionContextRef,
        observation: KernelObservation,
        trace: AdmissionTrace,
    ) -> Result<Self, &'static str> {
        let fields = AdmissionFields {
            canonical_request,
            nonce_key,
            operation_key,
            context,
            observation,
            trace,
        };
        validate_admission(&fields)?;
        Ok(Self {
            certificate_bytes: encode_admission(&fields),
        })
    }

    pub(crate) fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }
}

/// A runtime-created checked admission. Fields are private so callers outside
/// this crate cannot label arbitrary bytes as authenticated. Fresh production
/// construction requires an opaque token returned by the Lean trace checker.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedAdmission {
    certificate_bytes: Vec<u8>,
    fields: AdmissionFields,
}

impl CheckedAdmission {
    pub(crate) fn from_lean_validated(
        validated: &LeanValidatedAdmissionTrace,
    ) -> Result<Self, &'static str> {
        checked_from_canonical_bytes(validated.certificate_bytes())
            .ok_or("Lean-validated admission certificate is not canonical v2")
    }

    /// Exact canonical bytes accepted by Lean and written as the raw journal
    /// record body. Recovery must recheck these same bytes before use.
    pub fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }

    pub fn canonical_request(&self) -> &[u8] {
        &self.fields.canonical_request
    }
    pub fn nonce_key(&self) -> &NonceKey {
        &self.fields.nonce_key
    }
    pub fn operation_key(&self) -> &OperationKey {
        &self.fields.operation_key
    }
    pub fn context(&self) -> &AdmissionContextRef {
        &self.fields.context
    }
    pub fn observation(&self) -> &KernelObservation {
        &self.fields.observation
    }
    pub fn trace(&self) -> &AdmissionTrace {
        &self.fields.trace
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
            if admission.context().previous_admission_commitment != head {
                return Err(AuthenticatedJournalError::BrokenChain { sequence });
            }
            let commitment = record_commitment(body);
            if let Some((_, prior_sequence)) = nonce_index.insert(
                admission.nonce_key().clone(),
                (admission.observation().signing_bytes.clone(), sequence),
            ) {
                return Err(AuthenticatedJournalError::DuplicateNonce {
                    sequence,
                    prior_sequence,
                });
            }
            if let Some((_, prior_sequence)) = operation_index.insert(
                admission.operation_key().clone(),
                (admission.observation().signing_bytes.clone(), sequence),
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
        validate_admission(&admission.fields)
            .map_err(|reason| AuthenticatedJournalError::InvalidAdmission { reason })?;
        if encode_admission(&admission.fields) != admission.certificate_bytes {
            return Err(AuthenticatedJournalError::InvalidAdmission {
                reason: "admission certificate bytes are not canonical",
            });
        }
        match self.classify(
            admission.nonce_key(),
            admission.operation_key(),
            &admission.observation().signing_bytes,
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
        if admission.context().previous_admission_commitment != expected_head {
            return Err(AuthenticatedJournalError::InvalidAdmissionPrefix {
                expected: expected_head,
                actual: admission.context().previous_admission_commitment,
            });
        }
        let commitment = record_commitment(admission.certificate_bytes());
        let receipt = self
            .raw
            .append_at(sequence, admission.certificate_bytes())?;
        if receipt.status == super::AppendStatus::Appended {
            self.nonce_index.insert(
                admission.nonce_key().clone(),
                (admission.observation().signing_bytes.clone(), sequence),
            );
            self.operation_index.insert(
                admission.operation_key().clone(),
                (admission.observation().signing_bytes.clone(), sequence),
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
        self.raw
            .append_at(existing_sequence, record.admission.certificate_bytes())?;
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

fn validate_admission(value: &AdmissionFields) -> Result<(), &'static str> {
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
        || value.observation.execution_nodes.is_empty()
        || value.context.commitment.is_empty()
        || value.trace.projection_response.is_empty()
        || value.trace.format_v3_request.is_empty()
        || value.trace.format_v3_response.is_empty()
    {
        return Err("required authenticated field is empty");
    }
    if !value
        .trace
        .projection_response
        .starts_with(b"UWV4\x04\x04\x00")
    {
        return Err("projection response is not an accepted UWV4 kind 4 response");
    }
    let request_length = u64::try_from(value.canonical_request.len())
        .map_err(|_| "canonical request length exceeds projection bound space")?;
    if request_length != value.trace.projection_bound {
        return Err("projection bound is not the exact canonical request length");
    }
    if !value.trace.stage_receipts.all_are_accepted() {
        return Err("normalized admission stage receipt is not accepted");
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
    let child_index = usize::try_from(value.observation.child_index)
        .map_err(|_| "child index exceeds execution node address space")?;
    if value.observation.execution_nodes.get(child_index)
        != Some(&value.observation.resolved_move.child)
    {
        return Err("child index does not select the resolved move node");
    }
    match (
        value.observation.destination_index,
        value.observation.resolved_move.dest,
    ) {
        (None, None) => {}
        (Some(index), Some(destination)) => {
            let index = usize::try_from(index)
                .map_err(|_| "destination index exceeds execution node address space")?;
            if value.observation.execution_nodes.get(index) != Some(&destination) {
                return Err("destination index does not select the resolved move node");
            }
        }
        _ => return Err("destination projection and resolved move disagree"),
    }
    if value.observation.cite == 0 {
        return Err("citation zero cannot cross the checked boundary");
    }
    Ok(())
}

fn record_commitment(body: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(CHAIN_DOMAIN);
    hasher.update(body);
    *hasher.finalize().as_bytes()
}

fn encode_admission(value: &AdmissionFields) -> Vec<u8> {
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
    put_nodes(&mut out, &value.observation.execution_nodes);
    out.push(match value.observation.admission {
        KernelAdmissionObservation::Applied => 0,
        KernelAdmissionObservation::SkippedCycle => 1,
    });
    put_u64(&mut out, value.trace.projection_bound);
    put_bytes(&mut out, &value.trace.projection_response);
    put_bytes(&mut out, &value.trace.format_v3_request);
    put_bytes(&mut out, &value.trace.format_v3_response);
    put_u64(&mut out, value.trace.selected_request_slot);
    put_bool(&mut out, value.trace.operation_was_new);
    put_accepted_receipt(&mut out, value.trace.stage_receipts.verification);
    put_accepted_receipt(&mut out, value.trace.stage_receipts.context);
    put_accepted_receipt(&mut out, value.trace.stage_receipts.resolution);
    put_accepted_receipt(&mut out, value.trace.stage_receipts.authority);
    put_accepted_receipt(&mut out, value.trace.stage_receipts.membership);
    out
}

fn decode_admission(bytes: &[u8]) -> Option<CheckedAdmission> {
    checked_from_canonical_bytes(bytes)
}

fn checked_from_canonical_bytes(bytes: &[u8]) -> Option<CheckedAdmission> {
    let mut c = Cursor { bytes, at: 0 };
    if c.byte()? != RECORD_VERSION {
        return None;
    }
    let fields = AdmissionFields {
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
            execution_nodes: c.nodes()?,
            admission: match c.byte()? {
                0 => KernelAdmissionObservation::Applied,
                1 => KernelAdmissionObservation::SkippedCycle,
                _ => return None,
            },
        },
        trace: AdmissionTrace {
            projection_bound: c.u64()?,
            projection_response: c.bytes()?,
            format_v3_request: c.bytes()?,
            format_v3_response: c.bytes()?,
            selected_request_slot: c.u64()?,
            operation_was_new: c.bool()?,
            stage_receipts: AdmissionStageReceipts {
                verification: c.accepted_receipt()?,
                context: c.accepted_receipt()?,
                resolution: c.accepted_receipt()?,
                authority: c.accepted_receipt()?,
                membership: c.accepted_receipt()?,
            },
        },
    };
    if !c.done() || validate_admission(&fields).is_err() || encode_admission(&fields) != bytes {
        None
    } else {
        Some(CheckedAdmission {
            certificate_bytes: bytes.to_vec(),
            fields,
        })
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
fn put_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}
fn put_accepted_receipt(out: &mut Vec<u8>, value: bool) {
    // `validate_admission` admits only true receipts. Keeping the encoder
    // total makes canonical re-encoding independently reject any future
    // non-normalized in-memory value.
    put_bool(out, value);
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
fn put_nodes(out: &mut Vec<u8>, nodes: &[NodeId]) {
    let count = u64::try_from(nodes.len()).expect("execution node count exceeds u64");
    put_u64(out, count);
    for node in nodes {
        out.extend_from_slice(node);
    }
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
    fn bool(&mut self) -> Option<bool> {
        match self.byte()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
    }
    fn accepted_receipt(&mut self) -> Option<bool> {
        match self.byte()? {
            1 => Some(true),
            _ => None,
        }
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
    fn nodes(&mut self) -> Option<Vec<NodeId>> {
        let count = usize::try_from(self.u64()?).ok()?;
        let encoded_length = count.checked_mul(std::mem::size_of::<NodeId>())?;
        let encoded = self.take(encoded_length)?;
        let mut nodes = Vec::with_capacity(count);
        for node in encoded.chunks_exact(std::mem::size_of::<NodeId>()) {
            nodes.push(node.try_into().ok()?);
        }
        Some(nodes)
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
        let unchecked = UncheckedAdmissionCertificate::new(
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
                execution_nodes: vec![[0; 32], [1; 32], [2; 32], [10; 32], [12; 32]],
                admission: KernelAdmissionObservation::Applied,
            },
            AdmissionTrace::new(
                8,
                b"UWV4\x04\x04\x00projection".to_vec(),
                b"format-v3-request".to_vec(),
                b"format-v3-response".to_vec(),
                0,
                true,
                AdmissionStageReceipts::all_accepted(),
            ),
        )
        .unwrap();
        checked_from_canonical_bytes(unchecked.certificate_bytes()).unwrap()
    }

    #[test]
    fn kind_three_and_arbitrary_context_roundtrip_but_kind_two_refuses() {
        let value = admission(None, 5, 21, 31, 41);
        let encoded = value.certificate_bytes().to_vec();
        let decoded = decode_admission(&encoded).unwrap();
        assert_eq!(decoded, value);
        assert_eq!(decoded.context().commitment, vec![91, 92, 93]);
        assert_eq!(decoded.trace().projection_bound(), 8);
        assert!(decoded.trace().operation_was_new());
        assert!(decoded.trace().stage_receipts().verification());
        assert_eq!(decoded.observation().execution_nodes().len(), 5);

        let mut wrong_kind = value;
        wrong_kind.fields.canonical_request[5] = 2;
        assert_eq!(
            validate_admission(&wrong_kind.fields),
            Err("request is not context-bound UWV4 kind 3")
        );

        let mut non_exact_bound = admission(None, 5, 21, 31, 41);
        non_exact_bound.fields.trace.projection_bound += 1;
        assert_eq!(
            validate_admission(&non_exact_bound.fields),
            Err("projection bound is not the exact canonical request length")
        );

        let mut empty_nodes = admission(None, 5, 21, 31, 41);
        empty_nodes.fields.observation.execution_nodes.clear();
        assert_eq!(
            validate_admission(&empty_nodes.fields),
            Err("required authenticated field is empty")
        );

        let mut wrong_child_node = admission(None, 5, 21, 31, 41);
        wrong_child_node.fields.observation.execution_nodes[3] = [99; 32];
        assert_eq!(
            validate_admission(&wrong_child_node.fields),
            Err("child index does not select the resolved move node")
        );

        let mut wrong_destination_node = admission(None, 5, 21, 31, 41);
        wrong_destination_node.fields.observation.execution_nodes[4] = [99; 32];
        assert_eq!(
            validate_admission(&wrong_destination_node.fields),
            Err("destination index does not select the resolved move node")
        );
    }

    #[test]
    fn v2_decoder_rejects_noncanonical_boolean_receipts_and_suffixes() {
        let encoded = admission(None, 5, 21, 31, 41).certificate_bytes().to_vec();

        let mut wrong_version = encoded.clone();
        wrong_version[0] = 1;
        assert!(decode_admission(&wrong_version).is_none());

        // The canonical v2 suffix is operation_was_new followed by five
        // normalized acceptance receipts.
        let operation_was_new = encoded.len() - 6;
        let mut non_boolean = encoded.clone();
        non_boolean[operation_was_new] = 2;
        assert!(decode_admission(&non_boolean).is_none());

        let mut refused_receipt = encoded.clone();
        refused_receipt[encoded.len() - 1] = 0;
        assert!(decode_admission(&refused_receipt).is_none());

        let mut noncanonical_receipt = encoded.clone();
        noncanonical_receipt[encoded.len() - 1] = 2;
        assert!(decode_admission(&noncanonical_receipt).is_none());

        let mut trailing = encoded;
        trailing.push(0);
        assert!(decode_admission(&trailing).is_none());
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
        assert_eq!(
            journal.records()[0].admission().certificate_bytes(),
            first.certificate_bytes(),
            "journal retains the exact candidate bytes accepted by Lean"
        );
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
        assert_eq!(reopened.records()[0].admission().certificate_bytes()[0], 2);
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
