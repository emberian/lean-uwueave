//! Fail-closed orchestration for context-bound UWV4 move admission.
//!
//! The only public admission input is the raw kind-3 request.  Lean owns
//! bounded decoding, shape/width checks, canonical signing bytes, and the
//! neutral projection.  The host then verifies those exact bytes, classifies
//! durable nonce and operation identities, pins one immutable context, resolves
//! stable ids, applies independent authority and membership policies, asks the
//! existing Lean-authored move kernel for the prospective outcome, and appends
//! one checked record before committing the in-memory move log.
//!
//! Every policy trait in this module is a deployment-owned trust boundary.  A
//! successful call is evidence about the configured implementations, not a
//! cryptographic theorem.  Recovery is authoritative only relative to the
//! externally supplied journal head pin and the historical context provider.

use crate::auth::{
    project_runtime_auth_v4_admission, RuntimeAuthV4AdmissionOutcome,
    RuntimeAuthV4AdmissionProjection, RuntimeAuthV4AdmissionRefusal,
};
use crate::auth_verifier::{RequestVerifier, VerificationInput, VerificationRefusal};
use crate::persistence::{
    AdmissionContextRef, AppendStatus, AuthenticatedJournalError, AuthenticatedMoveJournal,
    CheckedAdmission, KernelAdmissionObservation, KernelObservation, NonceKey, OperationKey,
    StoreDecision, StorePreview,
};
use crate::{CausalWeave, MoveLog, MoveOp, NodeId, OpOutcome};

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

pub trait MoveAuthority<C> {
    fn authorize(
        &self,
        context: &PinnedAdmissionContext<C>,
        issuer: u64,
        operation: &MoveOp,
    ) -> Result<(), AuthorityRefusal>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MembershipRefusal {
    Denied,
    Unavailable,
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

    fn preflight(&self, operation: MoveOp) -> OpOutcome
    where
        T: AsRef<[u8]> + Clone + PartialEq,
    {
        let mut prospective = self.log.clone();
        prospective.record(operation);
        prospective
            .replay_traced(&self.weave)
            .outcomes
            .into_iter()
            .find_map(|(candidate, outcome)| (candidate == operation).then_some(outcome))
            .unwrap_or(OpOutcome::OmittedUnknownNode)
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionRefusal {
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
    MembershipDenied,
    Execution(ExecutionRefusal),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdmissionReceipt {
    pub sequence: u64,
    pub disposition: AdmissionDisposition,
    pub kernel_observation: KernelAdmissionObservation,
    pub head_commitment: [u8; 32],
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
        for record in journal.records() {
            let sequence = record.sequence;
            let projection = match project_runtime_auth_v4_admission(
                maximum_bytes,
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
            execution.commit(validated.operation);
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
                let observation = usize::try_from(existing_sequence)
                    .ok()
                    .and_then(|index| self.journal.records().get(index))
                    .map(|record| record.admission().observation().admission);
                let Some(observation) = observation else {
                    return AdmissionOutcome::Refused(AdmissionRefusal::StoreContractViolation);
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
        ) {
            Ok(value) => value,
            Err(StageFailure::Refused(reason)) => return AdmissionOutcome::Refused(reason),
            Err(StageFailure::Unavailable(reason)) => return AdmissionOutcome::Unavailable(reason),
        };
        let sequence = self.journal.next_sequence();
        match self.journal.append_checked_at(sequence, validated.checked) {
            Ok(StoreDecision::Fresh {
                receipt,
                head_commitment,
            }) if receipt.status == AppendStatus::Appended => {
                self.execution.commit(validated.operation);
                AdmissionOutcome::Accepted(AdmissionReceipt {
                    sequence: receipt.sequence,
                    disposition: AdmissionDisposition::Appended,
                    kernel_observation: validated.kernel_observation,
                    head_commitment,
                })
            }
            Ok(StoreDecision::Retry {
                existing_sequence,
                head_commitment,
            }) => AdmissionOutcome::Accepted(AdmissionReceipt {
                sequence: existing_sequence,
                disposition: AdmissionDisposition::Retry,
                kernel_observation: validated.kernel_observation,
                head_commitment,
            }),
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
    operation: MoveOp,
    kernel_observation: KernelAdmissionObservation,
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
    authority
        .authorize(&context, projection.issuer, &operation)
        .map_err(|reason| match reason {
            AuthorityRefusal::Denied => StageFailure::Refused(AdmissionRefusal::AuthorityDenied),
            AuthorityRefusal::Unavailable => {
                StageFailure::Unavailable(AdmissionUnavailable::Authority)
            }
        })?;
    membership
        .allows_move(&context, projection.issuer, &operation)
        .map_err(|reason| match reason {
            MembershipRefusal::Denied => StageFailure::Refused(AdmissionRefusal::MembershipDenied),
            MembershipRefusal::Unavailable => {
                StageFailure::Unavailable(AdmissionUnavailable::Membership)
            }
        })?;
    let (kernel_observation, execution_refusal) = match execution.preflight(operation) {
        OpOutcome::Applied => (Some(KernelAdmissionObservation::Applied), None),
        OpOutcome::SkippedCycle => (Some(KernelAdmissionObservation::SkippedCycle), None),
        OpOutcome::SkippedUnauthorised => (None, Some(ExecutionRefusal::SkippedUnauthorised)),
        OpOutcome::SkippedInvalid => (None, Some(ExecutionRefusal::SkippedInvalid)),
        OpOutcome::OmittedUnknownNode => (None, Some(ExecutionRefusal::OmittedUnknownNode)),
    };
    if let Some(reason) = execution_refusal {
        return Err(StageFailure::Refused(AdmissionRefusal::Execution(reason)));
    }
    let kernel_observation = kernel_observation.expect("accepted outcomes carry observation");
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
    let checked = CheckedAdmission::new(
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
            admission: kernel_observation,
        },
    )
    .map_err(|reason| StageFailure::Refused(AdmissionRefusal::CheckedBoundary(reason)))?;
    Ok(ValidatedAdmission {
        checked,
        operation,
        kernel_observation,
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
