//! Fail-closed orchestration for context-bound UWV4 move admission.
//!
//! The only public admission input is the raw kind-3 request.  Lean owns
//! bounded decoding, shape/width checks, canonical signing bytes, and the
//! neutral projection.  The host then verifies those exact bytes, classifies
//! durable nonce and operation identities, pins one immutable context, resolves
//! stable ids, retains exact positive authority and membership receipts, and
//! asks the existing Lean-authored move kernel for exact prospective request,
//! response, slot, status, and set-insertion evidence. Those actual locals form
//! one canonical v2 semantic certificate. Lean must accept its exact bytes
//! before storage can construct or append a checked record, and the in-memory
//! move log commits only after append. A verified retry cites that prior
//! accepted certificate and does not claim to rerun later policy stages.
//!
//! Every policy trait in this module is a deployment-owned trust boundary.  A
//! successful call is evidence about the configured implementations, not a
//! cryptographic theorem. Recovery first rechecks every stored certificate in
//! Lean, then exactly rebuilds it through the historical providers and shipping
//! replay kernel before committing that operation. It remains authoritative
//! only relative to the externally supplied journal head pin and historical
//! context provider.
//!
//! Construction and recovery do not claim Lean `Authority.WF` or
//! `Authority.UniqueGrant` for the provider's grant substrate. The runtime
//! scope carries no root-scope policy from which to check `WF`, while a finite
//! duplicate-id check would not discharge the content-addressing premise
//! behind `UniqueGrant`. Adding partial checks here would therefore overstate
//! the boundary and disrupt historical providers. Admission instead rejects
//! citation zero independently and retains the existing hypothesis-free gate
//! safety direction; exact substrate premises remain provider obligations.

use crate::auth::{
    check_runtime_auth_v4_admission_trace, project_runtime_auth_v4_admission,
    LeanValidatedAdmissionTrace, RuntimeAuthV4AdmissionOutcome, RuntimeAuthV4AdmissionProjection,
    RuntimeAuthV4AdmissionRefusal, RuntimeAuthV4AdmissionTraceRefusal,
};
use crate::auth_verifier::{
    RequestVerifier, VerificationAcceptance, VerificationInput, VerificationRefusal,
};
use crate::persistence::{
    AdmissionContextRef, AdmissionStageReceipts, AdmissionTrace, AppendStatus,
    AuthenticatedJournalError, AuthenticatedMoveJournal, CheckedAdmission,
    KernelAdmissionObservation, KernelObservation, NonceKey, OperationKey, StoreDecision,
    StorePreview, UncheckedAdmissionCertificate,
};
use crate::{CausalWeave, MoveLog, MoveOp, NodeId, OpOutcome};
use std::collections::BTreeSet;

/// One immutable historical context returned by the deployment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinnedAdmissionContext<C> {
    /// Must equal the exact opaque commitment signed by the request.
    pub commitment: Vec<u8>,
    pub document: Vec<u8>,
    pub genesis: Vec<u8>,
    /// Exact digest of the weave topology and grant/revocation substrate used
    /// by the Lean execution kernel for this historical context.
    pub execution_binding: [u8; 32],
    pub resolver_policy: u64,
    pub authority_policy: u64,
    pub membership_policy: u64,
    pub substrate: C,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContextRefusal {
    Unknown,
    Mismatch,
    Unavailable,
}

/// Resolve the exact signed context commitment without substituting current
/// state for historical state.
pub trait AdmissionContextProvider {
    type Context;

    fn pin(
        &self,
        commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
    ) -> Result<PinnedAdmissionContext<Self::Context>, ContextRefusal>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResolvedNode {
    pub node_id: NodeId,
    pub kernel_index: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolverRefusal {
    Missing,
    Unavailable,
}

pub trait StableIdResolver<C> {
    fn resolve(
        &self,
        context: &PinnedAdmissionContext<C>,
        stable_id: &[u8],
    ) -> Result<ResolvedNode, ResolverRefusal>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuthorityRefusal {
    Denied,
    Unavailable,
}

/// The exact values presented to an authority policy.
///
/// `context_commitment` and `authority_policy` identify the immutable policy
/// snapshot. `issuer`, `cite`, and `operation` bind the holder decision to the
/// exact signed principal and resolved move that continue through admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AuthorityInput<'a> {
    pub context_commitment: &'a [u8],
    pub authority_policy: u64,
    pub issuer: u64,
    pub cite: u64,
    pub operation: &'a MoveOp,
}

/// A trusted authority provider's attestation that it accepted one exact
/// holder check.
///
/// Construction is public because [`MoveAuthority`] is a deployment-owned
/// trust boundary. This is an ordinary receipt, not an unforgeable capability
/// or formal proof; admission still checks that the receipt exactly matches
/// the input currently moving through the pipeline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorityAcceptance {
    context_commitment: Vec<u8>,
    authority_policy: u64,
    issuer: u64,
    cite: u64,
    operation: MoveOp,
}

impl AuthorityAcceptance {
    /// Attest that a trusted authority provider accepted this exact input.
    /// Calling this constructor performs no authority check.
    pub fn from_authority_acceptance(input: AuthorityInput<'_>) -> Self {
        Self {
            context_commitment: input.context_commitment.to_vec(),
            authority_policy: input.authority_policy,
            issuer: input.issuer,
            cite: input.cite,
            operation: *input.operation,
        }
    }

    /// Check that this trusted-boundary receipt names exactly `input`.
    pub fn matches_input(&self, input: AuthorityInput<'_>) -> bool {
        self.context_commitment == input.context_commitment
            && self.authority_policy == input.authority_policy
            && self.issuer == input.issuer
            && self.cite == input.cite
            && self.operation == *input.operation
    }
}

pub trait MoveAuthority<C> {
    fn authorize(
        &self,
        context: &PinnedAdmissionContext<C>,
        input: AuthorityInput<'_>,
    ) -> Result<AuthorityAcceptance, AuthorityRefusal>;
}

/// Immutable issuer/citation holder bindings carried by a pinned context.
///
/// The relation answers the holder question omitted by the execution grant
/// triple itself: which authenticated issuer may exercise a given grant id.
/// Multiple issuers may legitimately hold the same citation.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GrantHolderBindings {
    holders: BTreeSet<(u64, u64)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GrantHolderBindingRefusal {
    NullCitation,
    DuplicateBinding { issuer: u64, cite: u64 },
}

impl GrantHolderBindings {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add one immutable holder binding. Duplicate pairs are refused, while
    /// distinct issuers may hold the same nonzero citation. Citation zero is
    /// the execution carrier's "cites nothing" sentinel and cannot acquire a
    /// holder through deployment policy.
    pub fn bind(&mut self, issuer: u64, cite: u64) -> Result<(), GrantHolderBindingRefusal> {
        if cite == 0 {
            return Err(GrantHolderBindingRefusal::NullCitation);
        }
        if !self.holders.insert((issuer, cite)) {
            return Err(GrantHolderBindingRefusal::DuplicateBinding { issuer, cite });
        }
        Ok(())
    }

    pub fn holds(&self, issuer: u64, cite: u64) -> bool {
        self.holders.contains(&(issuer, cite))
    }
}

/// A context substrate exposing its immutable citation-holder relation.
pub trait GrantHolderContext {
    fn holds_grant(&self, issuer: u64, cite: u64) -> bool;
}

impl GrantHolderContext for GrantHolderBindings {
    fn holds_grant(&self, issuer: u64, cite: u64) -> bool {
        self.holds(issuer, cite)
    }
}

/// Deterministic holder policy backed by the exact pinned context substrate.
#[derive(Debug, Clone, Copy, Default)]
pub struct ContextGrantHolderAuthority;

impl<C: GrantHolderContext> MoveAuthority<C> for ContextGrantHolderAuthority {
    fn authorize(
        &self,
        context: &PinnedAdmissionContext<C>,
        input: AuthorityInput<'_>,
    ) -> Result<AuthorityAcceptance, AuthorityRefusal> {
        if input.cite == 0
            || input.context_commitment != context.commitment
            || input.authority_policy != context.authority_policy
            || input.cite != input.operation.cite
            || !context.substrate.holds_grant(input.issuer, input.cite)
        {
            return Err(AuthorityRefusal::Denied);
        }
        Ok(AuthorityAcceptance::from_authority_acceptance(input))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MembershipRefusal {
    Denied,
    Unavailable,
}

/// The exact values presented to a membership policy.
///
/// This is distinct from [`AuthorityInput`]: membership is an independent
/// deployment boundary with its own immutable policy identity. Keeping its
/// complete input lets admission retain positive evidence for the exact
/// resolved operation rather than reducing the call to an unbound boolean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MembershipInput<'a> {
    pub context_commitment: &'a [u8],
    pub membership_policy: u64,
    pub issuer: u64,
    pub operation: &'a MoveOp,
}

/// Runtime-normalized evidence that a trusted membership provider accepted one
/// exact membership check.
///
/// This is not a formal proof or an unforgeable capability. Its constructor is
/// crate-private: the runtime creates it only after the deployment-owned
/// [`MoveMembership`] implementation returned success for the same context,
/// issuer, and resolved move.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MembershipAcceptance {
    context_commitment: Vec<u8>,
    membership_policy: u64,
    issuer: u64,
    operation: MoveOp,
}

impl MembershipAcceptance {
    /// Normalize one successful trusted membership call into exact evidence.
    pub(crate) fn from_membership_acceptance(input: MembershipInput<'_>) -> Self {
        Self {
            context_commitment: input.context_commitment.to_vec(),
            membership_policy: input.membership_policy,
            issuer: input.issuer,
            operation: *input.operation,
        }
    }

    /// Check that this trusted-boundary receipt names exactly `input`.
    pub fn matches_input(&self, input: MembershipInput<'_>) -> bool {
        self.context_commitment == input.context_commitment
            && self.membership_policy == input.membership_policy
            && self.issuer == input.issuer
            && self.operation == *input.operation
    }
}

pub trait MoveMembership<C> {
    fn allows_move(
        &self,
        context: &PinnedAdmissionContext<C>,
        issuer: u64,
        operation: &MoveOp,
    ) -> Result<(), MembershipRefusal>;
}

/// Concrete execution seam backed by the already-shipped Lean move kernel.
#[derive(Debug, Clone)]
pub struct LeanMoveExecution<T> {
    log: MoveLog,
    weave: CausalWeave<T>,
}

impl<T> LeanMoveExecution<T> {
    pub fn new(log: MoveLog, weave: CausalWeave<T>) -> Self {
        Self { log, weave }
    }

    pub fn log(&self) -> &MoveLog {
        &self.log
    }

    pub fn weave(&self) -> &CausalWeave<T> {
        &self.weave
    }

    pub fn into_parts(self) -> (MoveLog, CausalWeave<T>) {
        (self.log, self.weave)
    }

    /// Domain-separated identity of the exact execution base. Node ids commit
    /// to contents and parents; explicit parents/ranks plus grants and
    /// revocations pin the complete topology and authority substrate. Move ops
    /// are excluded because admission grows them only after durable append.
    pub fn base_binding(&self) -> [u8; 32]
    where
        T: AsRef<[u8]> + Clone + PartialEq,
    {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"uwueave.authenticated-runtime.execution-base.v1\0");
        hasher.update(b"nodes\0");
        hasher.update(&(self.weave.len() as u64).to_le_bytes());
        for node in self.weave.nodes() {
            hasher.update(&node.id());
            hasher.update(&node.rank().to_le_bytes());
            hasher.update(&(node.parents().len() as u64).to_le_bytes());
            for parent in node.parents() {
                hasher.update(parent);
            }
        }
        hasher.update(b"grants\0");
        hasher.update(&(self.log.grants().count() as u64).to_le_bytes());
        for grant in self.log.grants() {
            hasher.update(&grant.id.to_le_bytes());
            hasher.update(&grant.parent.to_le_bytes());
            hasher.update(&grant.scope.to_le_bytes());
        }
        hasher.update(b"revocations\0");
        hasher.update(&(self.log.revocations().count() as u64).to_le_bytes());
        for revoked in self.log.revocations() {
            hasher.update(&revoked.to_le_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    fn preflight(&self, operation: MoveOp) -> Result<KernelPreflightEvidence, ExecutionRefusal>
    where
        T: AsRef<[u8]> + Clone + PartialEq,
    {
        let prospective = self
            .log
            .prospective_replay_certified(&self.weave, operation);
        let selected_request_slot = prospective
            .selected_request_slot()
            .ok_or(ExecutionRefusal::OmittedUnknownNode)?;
        let selected_request_slot = u64::try_from(selected_request_slot)
            .map_err(|_| ExecutionRefusal::RequestSlotTooLarge)?;
        let admission = match prospective.selected_status() {
            Some(OpOutcome::Applied) => KernelAdmissionObservation::Applied,
            Some(OpOutcome::SkippedCycle) => KernelAdmissionObservation::SkippedCycle,
            Some(OpOutcome::SkippedUnauthorised) => {
                return Err(ExecutionRefusal::SkippedUnauthorised)
            }
            Some(OpOutcome::SkippedInvalid) => return Err(ExecutionRefusal::SkippedInvalid),
            Some(OpOutcome::OmittedUnknownNode) | None => {
                return Err(ExecutionRefusal::OmittedUnknownNode)
            }
        };
        Ok(KernelPreflightEvidence {
            execution_nodes: self.weave.nodes().map(|node| node.id()).collect(),
            canonical_request: prospective.replay().canonical_request().to_vec(),
            raw_response: prospective.replay().raw_response().to_vec(),
            selected_request_slot,
            operation_was_new: prospective.operation_was_new(),
            admission,
        })
    }

    fn commit(&mut self, operation: MoveOp) {
        self.log.record(operation);
    }

    fn kernel_index(&self, node_id: NodeId) -> Option<u64>
    where
        T: AsRef<[u8]> + Clone + PartialEq,
    {
        self.weave.nodes().enumerate().find_map(|(index, node)| {
            (node.id() == node_id)
                .then(|| u64::try_from(index).ok())
                .flatten()
        })
    }
}

/// Exact native replay evidence used to construct the semantic certificate.
/// The dense node-id vector comes from the same weave order used to encode
/// FORMAT-v3 indices; all request/response bytes come from the production Lean
/// encoder/kernel path retained by [`MoveLog::prospective_replay_certified`].
struct KernelPreflightEvidence {
    execution_nodes: Vec<NodeId>,
    canonical_request: Vec<u8>,
    raw_response: Vec<u8>,
    selected_request_slot: u64,
    operation_was_new: bool,
    admission: KernelAdmissionObservation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionRefusal {
    RequestSlotTooLarge,
    SkippedUnauthorised,
    SkippedInvalid,
    OmittedUnknownNode,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissionRefusal {
    Projection(RuntimeAuthV4AdmissionRefusal),
    KernelContractViolation,
    Verification(VerificationRefusal),
    VerificationReceiptMismatch,
    NonceCollision { existing_sequence: u64 },
    OperationCollision { existing_sequence: u64 },
    UnknownContext,
    ContextMismatch,
    MissingStableId,
    StableIndexMismatch { signed: u64, resolved: u64 },
    AuthorityDenied,
    AuthorityReceiptMismatch,
    MembershipDenied,
    Execution(ExecutionRefusal),
    TraceCertificate(RuntimeAuthV4AdmissionTraceRefusal),
    CheckedBoundary(&'static str),
    StoreContractViolation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissionUnavailable {
    VerificationRegistry,
    Context,
    Resolver,
    Authority,
    Membership,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdmissionDisposition {
    Appended,
    Retry,
}

/// The evidence exposed by one accepted runtime call.
///
/// Fresh admission returns the exact semantic certificate accepted by Lean.
/// A retry is deliberately a different claim: it cites a previously
/// validated durable certificate and carries only the current verifier's exact
/// receipt. It does not pretend that authority, membership, or replay
/// preflight ran again for the retry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissionCertificate {
    Fresh {
        trace: LeanValidatedAdmissionTrace,
        verification: VerificationAcceptance,
        authority: AuthorityAcceptance,
        membership: MembershipAcceptance,
    },
    VerifiedRetry {
        prior_sequence: u64,
        prior_commitment: [u8; 32],
        prior_certificate: LeanValidatedAdmissionTrace,
        current_projection: RuntimeAuthV4AdmissionProjection,
        current_verification: VerificationAcceptance,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionReceipt {
    pub sequence: u64,
    pub disposition: AdmissionDisposition,
    pub kernel_observation: KernelAdmissionObservation,
    pub head_commitment: [u8; 32],
    pub certificate: AdmissionCertificate,
}

#[derive(Debug)]
pub enum AdmissionOutcome {
    Accepted(AdmissionReceipt),
    Refused(AdmissionRefusal),
    Unavailable(AdmissionUnavailable),
    /// A deterministic storage refusal known to have appended no new record.
    StorageRefused(AuthenticatedJournalError),
    /// An append or retry sync had an indeterminate physical result.  No
    /// in-memory execution commit has occurred; reopen with an external pin is
    /// required before retrying.
    StorageIndeterminate(AuthenticatedJournalError),
}

fn storage_outcome(error: AuthenticatedJournalError) -> AdmissionOutcome {
    match error {
        AuthenticatedJournalError::Io(_) | AuthenticatedJournalError::Poisoned => {
            AdmissionOutcome::StorageIndeterminate(error)
        }
        _ => AdmissionOutcome::StorageRefused(error),
    }
}

#[derive(Debug)]
pub enum RuntimeConstructionError {
    JournalNotExternallyPinned,
    NonemptyJournalRequiresRecovery,
    NonemptyExecutionLog,
    ExecutionBindingMismatch,
}

#[derive(Debug)]
pub enum RuntimeRecoveryError {
    JournalNotExternallyPinned,
    NonemptyExecutionLog,
    ExecutionBindingMismatch,
    Projection {
        sequence: u64,
    },
    Certificate {
        sequence: u64,
        reason: RuntimeAuthV4AdmissionTraceRefusal,
    },
    Refused {
        sequence: u64,
        reason: AdmissionRefusal,
    },
    Unavailable {
        sequence: u64,
        reason: AdmissionUnavailable,
    },
    RecordMismatch {
        sequence: u64,
    },
}

/// One durable record whose exact semantic certificate was rechecked by Lean
/// and whose provider/replay trace was rebuilt exactly during this runtime's
/// construction. A successfully recovered runtime exposes one entry per
/// journal record, in sequence order, including the actual positive provider
/// receipts and resolved kernel result rebuilt for that record. Failed
/// recovery returns no runtime and therefore no partial validated prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValidatedRecoveryRecord {
    pub sequence: u64,
    pub commitment: [u8; 32],
    pub certificate: LeanValidatedAdmissionTrace,
    pub operation: MoveOp,
    pub kernel_observation: KernelAdmissionObservation,
    pub verification: VerificationAcceptance,
    pub authority: AuthorityAcceptance,
    pub membership: MembershipAcceptance,
}

/// One fixed document/genesis/context scope served by a runtime instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeScope {
    pub document: Vec<u8>,
    pub genesis: Vec<u8>,
    pub context_commitment: Vec<u8>,
    pub execution_binding: [u8; 32],
}

pub struct AuthenticatedRuntime<V, C, R, A, M, T> {
    scope: RuntimeScope,
    verifier: V,
    contexts: C,
    resolver: R,
    authority: A,
    membership: M,
    execution: LeanMoveExecution<T>,
    journal: AuthenticatedMoveJournal,
    validated_records: Vec<ValidatedRecoveryRecord>,
}

impl<V, C, R, A, M, T> AuthenticatedRuntime<V, C, R, A, M, T>
where
    V: RequestVerifier,
    C: AdmissionContextProvider,
    R: StableIdResolver<C::Context>,
    A: MoveAuthority<C::Context>,
    M: MoveMembership<C::Context>,
    T: AsRef<[u8]> + Clone + PartialEq,
{
    pub fn new(
        scope: RuntimeScope,
        verifier: V,
        contexts: C,
        resolver: R,
        authority: A,
        membership: M,
        execution: LeanMoveExecution<T>,
        journal: AuthenticatedMoveJournal,
    ) -> Result<Self, RuntimeConstructionError> {
        if !journal.open_report().externally_pinned {
            return Err(RuntimeConstructionError::JournalNotExternallyPinned);
        }
        if !journal.records().is_empty() {
            return Err(RuntimeConstructionError::NonemptyJournalRequiresRecovery);
        }
        if !execution.log().is_empty() {
            return Err(RuntimeConstructionError::NonemptyExecutionLog);
        }
        if execution.base_binding() != scope.execution_binding {
            return Err(RuntimeConstructionError::ExecutionBindingMismatch);
        }
        Ok(Self {
            scope,
            verifier,
            contexts,
            resolver,
            authority,
            membership,
            execution,
            journal,
            validated_records: Vec::new(),
        })
    }

    /// Rebuild a ready runtime from an externally pinned journal.
    ///
    /// Every historical record is re-projected by Lean, re-verified, resolved
    /// against its exact historical context, re-authorized, re-membership
    /// checked, and re-executed.  The supplied executor is consumed on failure,
    /// so callers must provide an isolated recovery instance.
    pub fn recover(
        maximum_bytes: usize,
        scope: RuntimeScope,
        verifier: V,
        contexts: C,
        resolver: R,
        authority: A,
        membership: M,
        mut execution: LeanMoveExecution<T>,
        journal: AuthenticatedMoveJournal,
    ) -> Result<Self, RuntimeRecoveryError> {
        if !journal.open_report().externally_pinned {
            return Err(RuntimeRecoveryError::JournalNotExternallyPinned);
        }
        if !execution.log().is_empty() {
            return Err(RuntimeRecoveryError::NonemptyExecutionLog);
        }
        if execution.base_binding() != scope.execution_binding {
            return Err(RuntimeRecoveryError::ExecutionBindingMismatch);
        }
        let mut validated_records = Vec::with_capacity(journal.records().len());
        for record in journal.records() {
            let sequence = record.sequence;
            // Stored canonicality is a persistence property, not semantic
            // admission evidence. Re-establish the opaque Lean acceptance
            // before consulting any deployment provider or mutating recovery
            // execution state.
            let stored_certificate =
                check_runtime_auth_v4_admission_trace(record.admission().certificate_bytes())
                    .map_err(|reason| RuntimeRecoveryError::Certificate { sequence, reason })?;
            let projection_bound = record.admission().canonical_request().len();
            let exact_projection_bound = u64::try_from(projection_bound)
                .map_err(|_| RuntimeRecoveryError::Projection { sequence })?;
            if record.admission().trace().projection_bound() != exact_projection_bound {
                return Err(RuntimeRecoveryError::RecordMismatch { sequence });
            }
            if projection_bound > maximum_bytes {
                return Err(RuntimeRecoveryError::Projection { sequence });
            }
            let projection = match project_runtime_auth_v4_admission(
                projection_bound,
                record.admission().canonical_request(),
            ) {
                RuntimeAuthV4AdmissionOutcome::Accepted(value) => value,
                RuntimeAuthV4AdmissionOutcome::Refused(_) => {
                    return Err(RuntimeRecoveryError::Projection { sequence })
                }
                RuntimeAuthV4AdmissionOutcome::KernelContractViolation => {
                    return Err(RuntimeRecoveryError::Projection { sequence })
                }
            };
            let checked = validate_fresh(
                &verifier,
                &contexts,
                &resolver,
                &authority,
                &membership,
                &execution,
                &scope,
                record.admission().context().previous_admission_commitment,
                &projection,
            );
            let validated = match checked {
                Ok(value) => value,
                Err(StageFailure::Refused(reason)) => {
                    return Err(RuntimeRecoveryError::Refused { sequence, reason })
                }
                Err(StageFailure::Unavailable(reason)) => {
                    return Err(RuntimeRecoveryError::Unavailable { sequence, reason })
                }
            };
            if record.admission() != &validated.checked {
                return Err(RuntimeRecoveryError::RecordMismatch { sequence });
            }
            if validated.certificate != stored_certificate {
                return Err(RuntimeRecoveryError::RecordMismatch { sequence });
            }
            execution.commit(validated.operation);
            validated_records.push(ValidatedRecoveryRecord {
                sequence,
                commitment: record.commitment,
                certificate: stored_certificate,
                operation: validated.operation,
                kernel_observation: validated.kernel_observation,
                verification: validated.verification_acceptance,
                authority: validated.authority_acceptance,
                membership: validated.membership_acceptance,
            });
        }
        Ok(Self {
            scope,
            verifier,
            contexts,
            resolver,
            authority,
            membership,
            execution,
            journal,
            validated_records,
        })
    }

    pub fn admit(&mut self, maximum_bytes: usize, raw_request: &[u8]) -> AdmissionOutcome {
        let projection = match project_runtime_auth_v4_admission(maximum_bytes, raw_request) {
            RuntimeAuthV4AdmissionOutcome::Accepted(value) => value,
            RuntimeAuthV4AdmissionOutcome::Refused(reason) => {
                return AdmissionOutcome::Refused(AdmissionRefusal::Projection(reason))
            }
            RuntimeAuthV4AdmissionOutcome::KernelContractViolation => {
                return AdmissionOutcome::Refused(AdmissionRefusal::KernelContractViolation)
            }
        };

        let verification_input = verification_input(&projection);
        let acceptance = match self.verifier.verify(verification_input) {
            Ok(value) => value,
            Err(VerificationRefusal::RegistryUnavailable) => {
                return AdmissionOutcome::Unavailable(AdmissionUnavailable::VerificationRegistry)
            }
            Err(reason) => {
                return AdmissionOutcome::Refused(AdmissionRefusal::Verification(reason))
            }
        };
        if !acceptance.matches_input(verification_input) {
            return AdmissionOutcome::Refused(AdmissionRefusal::VerificationReceiptMismatch);
        }

        let nonce_key = nonce_key(&projection);
        let operation_key = operation_key(&projection);
        match self
            .journal
            .classify(&nonce_key, &operation_key, &projection.signing_bytes)
        {
            StorePreview::Fresh => {}
            StorePreview::Retry { existing_sequence } => {
                let Some(index) = usize::try_from(existing_sequence).ok() else {
                    return AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation);
                };
                let Some(record) = self.journal.records().get(index) else {
                    return AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation);
                };
                let Some(validated_record) = self.validated_records.get(index) else {
                    return AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation);
                };
                if record.sequence != existing_sequence
                    || validated_record.sequence != existing_sequence
                    || validated_record.commitment != record.commitment
                    || validated_record.certificate.certificate_bytes()
                        != record.admission().certificate_bytes()
                    || nonce_key != *record.admission().nonce_key()
                    || operation_key != *record.admission().operation_key()
                    || projection.signing_bytes != record.admission().observation().signing_bytes
                {
                    return AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation);
                }
                let observation = record.admission().observation().admission;
                let retry_certificate = AdmissionCertificate::VerifiedRetry {
                    prior_sequence: existing_sequence,
                    prior_commitment: record.commitment,
                    prior_certificate: validated_record.certificate.clone(),
                    current_projection: projection,
                    current_verification: acceptance,
                };
                return match self.journal.resync_verified_retry(existing_sequence) {
                    Ok(StoreDecision::Retry {
                        existing_sequence,
                        head_commitment,
                    }) => AdmissionOutcome::Accepted(AdmissionReceipt {
                        sequence: existing_sequence,
                        disposition: AdmissionDisposition::Retry,
                        kernel_observation: observation,
                        head_commitment,
                        certificate: retry_certificate,
                    }),
                    Ok(_) => AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation),
                    Err(error) => storage_outcome(error),
                };
            }
            StorePreview::NonceCollision { existing_sequence } => {
                return AdmissionOutcome::Refused(AdmissionRefusal::NonceCollision {
                    existing_sequence,
                })
            }
            StorePreview::OperationCollision { existing_sequence } => {
                return AdmissionOutcome::Refused(AdmissionRefusal::OperationCollision {
                    existing_sequence,
                })
            }
        }

        let validated = match validate_after_verification(
            &self.contexts,
            &self.resolver,
            &self.authority,
            &self.membership,
            &self.execution,
            &self.scope,
            self.journal.head_commitment(),
            projection,
            acceptance,
        ) {
            Ok(value) => value,
            Err(StageFailure::Refused(reason)) => return AdmissionOutcome::Refused(reason),
            Err(StageFailure::Unavailable(reason)) => return AdmissionOutcome::Unavailable(reason),
        };
        let sequence = self.journal.next_sequence();
        let ValidatedAdmission {
            checked,
            certificate,
            operation,
            kernel_observation,
            verification_acceptance,
            authority_acceptance,
            membership_acceptance,
        } = validated;
        match self.journal.append_checked_at(sequence, checked) {
            Ok(StoreDecision::Fresh {
                receipt,
                head_commitment,
            }) if receipt.status == AppendStatus::Appended => {
                self.execution.commit(operation);
                self.validated_records.push(ValidatedRecoveryRecord {
                    sequence: receipt.sequence,
                    commitment: head_commitment,
                    certificate: certificate.clone(),
                    operation,
                    kernel_observation,
                    verification: verification_acceptance.clone(),
                    authority: authority_acceptance.clone(),
                    membership: membership_acceptance.clone(),
                });
                AdmissionOutcome::Accepted(AdmissionReceipt {
                    sequence: receipt.sequence,
                    disposition: AdmissionDisposition::Appended,
                    kernel_observation,
                    head_commitment,
                    certificate: AdmissionCertificate::Fresh {
                        trace: certificate,
                        verification: verification_acceptance,
                        authority: authority_acceptance,
                        membership: membership_acceptance,
                    },
                })
            }
            Ok(StoreDecision::Retry { .. }) => {
                AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation)
            }
            Ok(StoreDecision::NonceCollision { existing_sequence }) => {
                AdmissionOutcome::Refused(AdmissionRefusal::NonceCollision { existing_sequence })
            }
            Ok(StoreDecision::OperationCollision { existing_sequence }) => {
                AdmissionOutcome::Refused(AdmissionRefusal::OperationCollision {
                    existing_sequence,
                })
            }
            Ok(StoreDecision::Fresh { .. }) => {
                AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation)
            }
            Err(error) => storage_outcome(error),
        }
    }

    pub fn journal(&self) -> &AuthenticatedMoveJournal {
        &self.journal
    }

    pub fn scope(&self) -> &RuntimeScope {
        &self.scope
    }

    pub fn execution(&self) -> &LeanMoveExecution<T> {
        &self.execution
    }

    /// Complete in-sequence list of journal records whose exact certificates
    /// have been accepted by Lean in this runtime and whose execution effects
    /// are present in `execution`. Fresh appends extend the same list, keeping
    /// the retry path tied to an opaque accepted token.
    pub fn validated_records(&self) -> &[ValidatedRecoveryRecord] {
        &self.validated_records
    }

    pub fn into_parts(
        self,
    ) -> (
        RuntimeScope,
        V,
        C,
        R,
        A,
        M,
        LeanMoveExecution<T>,
        AuthenticatedMoveJournal,
    ) {
        (
            self.scope,
            self.verifier,
            self.contexts,
            self.resolver,
            self.authority,
            self.membership,
            self.execution,
            self.journal,
        )
    }
}

struct ValidatedAdmission {
    checked: CheckedAdmission,
    certificate: LeanValidatedAdmissionTrace,
    operation: MoveOp,
    kernel_observation: KernelAdmissionObservation,
    verification_acceptance: VerificationAcceptance,
    authority_acceptance: AuthorityAcceptance,
    membership_acceptance: MembershipAcceptance,
}

enum StageFailure {
    Refused(AdmissionRefusal),
    Unavailable(AdmissionUnavailable),
}

fn verification_input(projection: &RuntimeAuthV4AdmissionProjection) -> VerificationInput<'_> {
    VerificationInput {
        context_commitment: &projection.context_commitment,
        document: &projection.document,
        genesis: &projection.genesis,
        algorithm: projection.signature_algorithm,
        issuer: projection.issuer,
        key_epoch: projection.key_epoch,
        signing_bytes: &projection.signing_bytes,
        signature: &projection.signature,
    }
}

fn nonce_key(projection: &RuntimeAuthV4AdmissionProjection) -> NonceKey {
    NonceKey {
        document: projection.document.clone(),
        genesis: projection.genesis.clone(),
        issuer: projection.issuer,
        key_epoch: projection.key_epoch,
        nonce: projection.nonce.clone(),
    }
}

fn operation_key(projection: &RuntimeAuthV4AdmissionProjection) -> OperationKey {
    OperationKey {
        document: projection.document.clone(),
        genesis: projection.genesis.clone(),
        operation_id: projection.operation_id.clone(),
    }
}

fn validate_fresh<V, C, R, A, M, T>(
    verifier: &V,
    contexts: &C,
    resolver: &R,
    authority: &A,
    membership: &M,
    execution: &LeanMoveExecution<T>,
    scope: &RuntimeScope,
    previous: Option<[u8; 32]>,
    projection: &RuntimeAuthV4AdmissionProjection,
) -> Result<ValidatedAdmission, StageFailure>
where
    V: RequestVerifier,
    C: AdmissionContextProvider,
    R: StableIdResolver<C::Context>,
    A: MoveAuthority<C::Context>,
    M: MoveMembership<C::Context>,
    T: AsRef<[u8]> + Clone + PartialEq,
{
    let input = verification_input(projection);
    let acceptance = verifier.verify(input).map_err(|reason| match reason {
        VerificationRefusal::RegistryUnavailable => {
            StageFailure::Unavailable(AdmissionUnavailable::VerificationRegistry)
        }
        other => StageFailure::Refused(AdmissionRefusal::Verification(other)),
    })?;
    if !acceptance.matches_input(input) {
        return Err(StageFailure::Refused(
            AdmissionRefusal::VerificationReceiptMismatch,
        ));
    }
    validate_after_verification(
        contexts,
        resolver,
        authority,
        membership,
        execution,
        scope,
        previous,
        projection.clone(),
        acceptance,
    )
}

fn validate_after_verification<C, R, A, M, T>(
    contexts: &C,
    resolver: &R,
    authority: &A,
    membership: &M,
    execution: &LeanMoveExecution<T>,
    scope: &RuntimeScope,
    previous: Option<[u8; 32]>,
    projection: RuntimeAuthV4AdmissionProjection,
    verification_acceptance: VerificationAcceptance,
) -> Result<ValidatedAdmission, StageFailure>
where
    C: AdmissionContextProvider,
    R: StableIdResolver<C::Context>,
    A: MoveAuthority<C::Context>,
    M: MoveMembership<C::Context>,
    T: AsRef<[u8]> + Clone + PartialEq,
{
    if projection.document != scope.document
        || projection.genesis != scope.genesis
        || projection.context_commitment != scope.context_commitment
    {
        return Err(StageFailure::Refused(AdmissionRefusal::ContextMismatch));
    }
    let context = contexts
        .pin(
            &projection.context_commitment,
            &projection.document,
            &projection.genesis,
        )
        .map_err(|reason| match reason {
            ContextRefusal::Unavailable => StageFailure::Unavailable(AdmissionUnavailable::Context),
            ContextRefusal::Unknown => StageFailure::Refused(AdmissionRefusal::UnknownContext),
            ContextRefusal::Mismatch => StageFailure::Refused(AdmissionRefusal::ContextMismatch),
        })?;
    if context.commitment != projection.context_commitment
        || context.document != projection.document
        || context.genesis != projection.genesis
        || context.execution_binding != scope.execution_binding
        || execution.base_binding() != scope.execution_binding
    {
        return Err(StageFailure::Refused(AdmissionRefusal::ContextMismatch));
    }
    let child = resolve_exact(
        &context,
        resolver,
        &projection.child.stable_id,
        projection.child.kernel_index,
    )?;
    let destination = match &projection.destination {
        None => None,
        Some(node) => Some(resolve_exact(
            &context,
            resolver,
            &node.stable_id,
            node.kernel_index,
        )?),
    };
    require_execution_index(execution, child, projection.child.kernel_index)?;
    if let (Some(resolved), Some(signed)) = (destination, projection.exec_destination) {
        require_execution_index(execution, resolved, signed)?;
    }
    let operation = MoveOp {
        lamport: projection.lamport,
        replica: projection.exec_replica,
        child: child.node_id,
        dest: destination.map(|node| node.node_id),
        cite: projection.exec_cite,
    };
    // Citation zero is the FORMAT-v3 "cites nothing" sentinel. Reject it in
    // the orchestration itself, before consulting even a trusted authority
    // provider: a malformed substrate containing a live grant id zero must
    // not let a permissive provider turn the sentinel into authority.
    if operation.cite == 0 {
        return Err(StageFailure::Refused(AdmissionRefusal::AuthorityDenied));
    }
    let authority_input = AuthorityInput {
        context_commitment: &context.commitment,
        authority_policy: context.authority_policy,
        issuer: projection.issuer,
        cite: operation.cite,
        operation: &operation,
    };
    let authority_acceptance =
        authority
            .authorize(&context, authority_input)
            .map_err(|reason| match reason {
                AuthorityRefusal::Denied => {
                    StageFailure::Refused(AdmissionRefusal::AuthorityDenied)
                }
                AuthorityRefusal::Unavailable => {
                    StageFailure::Unavailable(AdmissionUnavailable::Authority)
                }
            })?;
    if !authority_acceptance.matches_input(authority_input) {
        return Err(StageFailure::Refused(
            AdmissionRefusal::AuthorityReceiptMismatch,
        ));
    }
    let membership_input = MembershipInput {
        context_commitment: &context.commitment,
        membership_policy: context.membership_policy,
        issuer: projection.issuer,
        operation: &operation,
    };
    membership
        .allows_move(&context, projection.issuer, &operation)
        .map_err(|reason| match reason {
            MembershipRefusal::Denied => StageFailure::Refused(AdmissionRefusal::MembershipDenied),
            MembershipRefusal::Unavailable => {
                StageFailure::Unavailable(AdmissionUnavailable::Membership)
            }
        })?;
    let membership_acceptance = MembershipAcceptance::from_membership_acceptance(membership_input);
    let preflight = execution
        .preflight(operation)
        .map_err(|reason| StageFailure::Refused(AdmissionRefusal::Execution(reason)))?;
    let kernel_observation = preflight.admission;
    let nonce = nonce_key(&projection);
    let operation_identity = operation_key(&projection);
    let destination_stable = projection
        .destination
        .as_ref()
        .map(|node| node.stable_id.clone());
    let destination_index = projection
        .destination
        .as_ref()
        .map(|node| node.kernel_index);
    let projection_bound = u64::try_from(projection.canonical_request.len()).map_err(|_| {
        StageFailure::Refused(AdmissionRefusal::CheckedBoundary(
            "projection bound exceeds certificate word space",
        ))
    })?;
    let trace = AdmissionTrace::new(
        projection_bound,
        projection.projection_response,
        preflight.canonical_request,
        preflight.raw_response,
        preflight.selected_request_slot,
        preflight.operation_was_new,
        AdmissionStageReceipts::all_accepted(),
    );
    let candidate = UncheckedAdmissionCertificate::new(
        projection.canonical_request,
        nonce,
        operation_identity,
        AdmissionContextRef {
            commitment: context.commitment,
            execution_binding: scope.execution_binding,
            resolver_policy: context.resolver_policy,
            authority_policy: context.authority_policy,
            membership_policy: context.membership_policy,
            previous_admission_commitment: previous,
        },
        KernelObservation {
            signature_algorithm: projection.signature_algorithm,
            signing_bytes: projection.signing_bytes,
            signature: projection.signature,
            child_stable: projection.child.stable_id,
            child_index: projection.child.kernel_index,
            destination_stable,
            destination_index,
            lamport: projection.lamport,
            replica: projection.exec_replica,
            cite: projection.exec_cite,
            resolved_move: operation,
            execution_nodes: preflight.execution_nodes,
            admission: kernel_observation,
        },
        trace,
    )
    .map_err(|reason| StageFailure::Refused(AdmissionRefusal::CheckedBoundary(reason)))?;
    let certificate = check_runtime_auth_v4_admission_trace(candidate.certificate_bytes())
        .map_err(|reason| StageFailure::Refused(AdmissionRefusal::TraceCertificate(reason)))?;
    let checked = CheckedAdmission::from_lean_validated(&certificate)
        .map_err(|reason| StageFailure::Refused(AdmissionRefusal::CheckedBoundary(reason)))?;
    Ok(ValidatedAdmission {
        checked,
        certificate,
        operation,
        kernel_observation,
        verification_acceptance,
        authority_acceptance,
        membership_acceptance,
    })
}

fn resolve_exact<C, R>(
    context: &PinnedAdmissionContext<C>,
    resolver: &R,
    stable_id: &[u8],
    signed_index: u64,
) -> Result<ResolvedNode, StageFailure>
where
    R: StableIdResolver<C>,
{
    let resolved = resolver
        .resolve(context, stable_id)
        .map_err(|reason| match reason {
            ResolverRefusal::Missing => StageFailure::Refused(AdmissionRefusal::MissingStableId),
            ResolverRefusal::Unavailable => {
                StageFailure::Unavailable(AdmissionUnavailable::Resolver)
            }
        })?;
    if resolved.kernel_index != signed_index {
        return Err(StageFailure::Refused(
            AdmissionRefusal::StableIndexMismatch {
                signed: signed_index,
                resolved: resolved.kernel_index,
            },
        ));
    }
    Ok(resolved)
}

fn require_execution_index<T: AsRef<[u8]> + Clone + PartialEq>(
    execution: &LeanMoveExecution<T>,
    resolved: ResolvedNode,
    signed_index: u64,
) -> Result<(), StageFailure> {
    let actual = execution
        .kernel_index(resolved.node_id)
        .ok_or(StageFailure::Refused(AdmissionRefusal::MissingStableId))?;
    if actual != signed_index {
        return Err(StageFailure::Refused(
            AdmissionRefusal::StableIndexMismatch {
                signed: signed_index,
                resolved: actual,
            },
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Grant;

    #[test]
    fn execution_binding_frames_grants_and_revocations_as_distinct_lanes() {
        let weave = CausalWeave::<Vec<u8>>::new();
        let mut grant_log = MoveLog::new();
        grant_log.issue(Grant::delegate(3, 1, 5));
        let mut revocation_log = MoveLog::new();
        revocation_log.revoke(1);
        revocation_log.revoke(3);
        revocation_log.revoke(5);

        assert_ne!(
            LeanMoveExecution::new(grant_log, weave.clone()).base_binding(),
            LeanMoveExecution::new(revocation_log, weave).base_binding()
        );
    }
}
