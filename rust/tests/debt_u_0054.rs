//! Immutable implementation evidence for debt U-0054.
//!
//! The request bytes and signing bytes come from Lean's kind-3 corpus emitter;
//! this target deliberately contains no request encoder.  The test exercises
//! only public shipping APIs and builds its own historical-context provider,
//! resolver, membership policy, execution bases, and journals.  Context
//! immutability, historical availability, digest collision resistance, and
//! external-pin custody remain documented deployment trust boundaries.

#[path = "support/runtime_auth_v4_admission.rs"]
mod corpus;

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::auth_runtime::{
    AdmissionContextProvider, AdmissionDisposition, AdmissionOutcome, AdmissionRefusal,
    AuthenticatedRuntime, ContextGrantHolderAuthority, ContextRefusal, GrantHolderBindings,
    LeanMoveExecution, MembershipRefusal, MoveMembership, PinnedAdmissionContext, ResolvedNode,
    ResolverRefusal, RuntimeConstructionError, RuntimeRecoveryError, RuntimeScope,
    StableIdResolver,
};
use uwueave::auth_verifier::{
    compute_keyed_blake3_mac, InMemoryKeyRegistry, KeyedBlake3Binding, KeyedBlake3Key,
    KeyedBlake3Verifier,
};
use uwueave::persistence::{
    AuthenticatedMoveJournal, JournalOptions, RecoveryExpectation, SyncPolicy, TornTailPolicy,
};
use uwueave::{CausalWeave, Grant, MoveLog, MoveOp, NodeId};

const CONTEXT: &[u8] = &[30, 31];
const SUCCESSOR_CONTEXT: &[u8] = &[32, 33];
const DOCUMENT: &[u8] = &[1, 2];
const GENESIS: &[u8] = &[3, 4];
const ISSUER: u64 = 17;
const EPOCH: u64 = 2;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempJournal(PathBuf);

impl TempJournal {
    fn new(label: &str) -> Self {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-debt-u-0054-{label}-{}-{nonce}.journal",
            std::process::id()
        ));
        let _ = fs::remove_file(&path);
        Self(path)
    }
}

impl Drop for TempJournal {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn journal_options() -> JournalOptions {
    JournalOptions {
        torn_tail: TornTailPolicy::Refuse,
        sync: SyncPolicy::Buffered,
        max_record_bytes: 1 << 20,
    }
}

fn key() -> KeyedBlake3Key {
    KeyedBlake3Key::from_bytes([7; 32])
}

fn signed(case: &str) -> corpus::SignedFixture {
    corpus::signed_fixture(case, |bytes| {
        compute_keyed_blake3_mac(&key(), bytes).to_vec()
    })
}

fn verifier(successor_revoked: bool) -> KeyedBlake3Verifier<InMemoryKeyRegistry> {
    let mut registry = InMemoryKeyRegistry::new();
    registry
        .insert_snapshot(
            CONTEXT,
            DOCUMENT,
            GENESIS,
            [KeyedBlake3Binding::active(ISSUER, EPOCH, key())],
        )
        .unwrap();
    registry
        .insert_snapshot(
            SUCCESSOR_CONTEXT,
            DOCUMENT,
            GENESIS,
            [if successor_revoked {
                KeyedBlake3Binding::revoked(ISSUER, EPOCH)
            } else {
                KeyedBlake3Binding::active(ISSUER, EPOCH, key())
            }],
        )
        .unwrap();
    KeyedBlake3Verifier::new(registry)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Substrate {
    child: NodeId,
    destination: NodeId,
    holders: GrantHolderBindings,
}

impl uwueave::auth_runtime::GrantHolderContext for Substrate {
    fn holds_grant(&self, issuer: u64, cite: u64) -> bool {
        self.holders.holds(issuer, cite)
    }
}

type Snapshot = PinnedAdmissionContext<Substrate>;
type ContextKey = (Vec<u8>, Vec<u8>, Vec<u8>);

#[derive(Clone, Default)]
struct HistoricalContexts {
    snapshots: BTreeMap<ContextKey, Snapshot>,
}

impl HistoricalContexts {
    fn insert(&mut self, snapshot: Snapshot) {
        let key = (
            snapshot.commitment.clone(),
            snapshot.document.clone(),
            snapshot.genesis.clone(),
        );
        assert!(self.snapshots.insert(key, snapshot).is_none());
    }

    fn insert_for(&mut self, key: ContextKey, snapshot: Snapshot) {
        assert!(self.snapshots.insert(key, snapshot).is_none());
    }
}

impl AdmissionContextProvider for HistoricalContexts {
    type Context = Substrate;

    fn pin(
        &self,
        commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
    ) -> Result<Snapshot, ContextRefusal> {
        let key = (commitment.to_vec(), document.to_vec(), genesis.to_vec());
        if let Some(snapshot) = self.snapshots.get(&key) {
            return Ok(snapshot.clone());
        }
        if self
            .snapshots
            .values()
            .any(|snapshot| snapshot.commitment == commitment)
        {
            Err(ContextRefusal::Mismatch)
        } else {
            Err(ContextRefusal::Unknown)
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ContextResolver;

impl StableIdResolver<Substrate> for ContextResolver {
    fn resolve(
        &self,
        context: &Snapshot,
        stable_id: &[u8],
    ) -> Result<ResolvedNode, ResolverRefusal> {
        if context.resolver_policy != 1 {
            return Err(ResolverRefusal::Missing);
        }
        match stable_id {
            [10, 11] => Ok(ResolvedNode {
                node_id: context.substrate.child,
                kernel_index: 3,
            }),
            [12, 13] => Ok(ResolvedNode {
                node_id: context.substrate.destination,
                kernel_index: 4,
            }),
            _ => Err(ResolverRefusal::Missing),
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ExactMembership;

impl MoveMembership<Substrate> for ExactMembership {
    fn allows_move(
        &self,
        context: &Snapshot,
        issuer: u64,
        operation: &MoveOp,
    ) -> Result<(), MembershipRefusal> {
        if context.membership_policy == 3
            && issuer == ISSUER
            && operation.replica == ISSUER
            && operation.cite == 7
        {
            Ok(())
        } else {
            Err(MembershipRefusal::Denied)
        }
    }
}

type Runtime = AuthenticatedRuntime<
    KeyedBlake3Verifier<InMemoryKeyRegistry>,
    HistoricalContexts,
    ContextResolver,
    ContextGrantHolderAuthority,
    ExactMembership,
    Vec<u8>,
>;

fn weave(extra_node: bool) -> CausalWeave<Vec<u8>> {
    let mut weave = CausalWeave::new();
    for index in 0..5 {
        weave
            .insert(vec![], format!("debt-u-0054-node-{index}").into_bytes())
            .unwrap();
    }
    if extra_node {
        weave
            .insert(vec![], b"debt-u-0054-topology-mutation".to_vec())
            .unwrap();
    }
    weave
}

fn log(extra_grant: bool, revoke: bool) -> MoveLog {
    let mut log = MoveLog::new();
    log.issue(Grant::universal(7));
    if extra_grant {
        log.issue(Grant::universal(8));
    }
    if revoke {
        log.revoke(7);
    }
    log
}

fn execution_and_snapshot(
    commitment: &[u8],
    extra_node: bool,
    extra_grant: bool,
    revoke: bool,
) -> (LeanMoveExecution<Vec<u8>>, Snapshot) {
    let weave = weave(extra_node);
    let ordered: Vec<_> = weave.nodes().map(|node| node.id()).collect();
    let execution = LeanMoveExecution::new(log(extra_grant, revoke), weave);
    let mut holders = GrantHolderBindings::new();
    holders.bind(ISSUER, 7).unwrap();
    let snapshot = Snapshot {
        commitment: commitment.to_vec(),
        document: DOCUMENT.to_vec(),
        genesis: GENESIS.to_vec(),
        execution_binding: execution.base_binding(),
        resolver_policy: 1,
        authority_policy: 2,
        membership_policy: 3,
        substrate: Substrate {
            child: ordered[3],
            destination: ordered[4],
            holders,
        },
    };
    (execution, snapshot)
}

fn scope(commitment: &[u8], binding: [u8; 32]) -> RuntimeScope {
    RuntimeScope {
        document: DOCUMENT.to_vec(),
        genesis: GENESIS.to_vec(),
        context_commitment: commitment.to_vec(),
        execution_binding: binding,
    }
}

fn open_empty(path: &TempJournal) -> AuthenticatedMoveJournal {
    AuthenticatedMoveJournal::open_pinned(&path.0, journal_options(), RecoveryExpectation::EMPTY)
        .unwrap()
}

fn new_runtime(
    path: &TempJournal,
    runtime_scope: RuntimeScope,
    execution: LeanMoveExecution<Vec<u8>>,
    contexts: HistoricalContexts,
    runtime_verifier: KeyedBlake3Verifier<InMemoryKeyRegistry>,
) -> Result<Runtime, RuntimeConstructionError> {
    AuthenticatedRuntime::new(
        runtime_scope,
        runtime_verifier,
        contexts,
        ContextResolver,
        ContextGrantHolderAuthority,
        ExactMembership,
        execution,
        open_empty(path),
    )
}

fn admitted(outcome: AdmissionOutcome) -> uwueave::auth_runtime::AdmissionReceipt {
    match outcome {
        AdmissionOutcome::Accepted(receipt) => receipt,
        other => panic!("expected accepted admission, got {other:?}"),
    }
}

#[test]
fn debt_closure_u_0054() {
    let base_request = signed("base");
    let successor_request = signed("other_context");

    // The digest is sensitive to each intended execution-base lane.
    let (base_execution, base_snapshot) = execution_and_snapshot(CONTEXT, false, false, false);
    let base_binding = base_execution.base_binding();
    let (topology_mutation, _) = execution_and_snapshot(CONTEXT, true, false, false);
    let (grant_mutation, _) = execution_and_snapshot(CONTEXT, false, true, false);
    let (revocation_mutation, successor_snapshot) =
        execution_and_snapshot(SUCCESSOR_CONTEXT, false, false, true);
    assert_ne!(base_binding, topology_mutation.base_binding());
    assert_ne!(base_binding, grant_mutation.base_binding());
    assert_ne!(base_binding, revocation_mutation.base_binding());

    // Construction recomputes the binding instead of accepting a caller label.
    let construction_path = TempJournal::new("wrong-construction-binding");
    let mut wrong_scope = scope(CONTEXT, base_binding);
    wrong_scope.execution_binding[0] ^= 1;
    let mut base_contexts = HistoricalContexts::default();
    base_contexts.insert(base_snapshot.clone());
    assert!(matches!(
        new_runtime(
            &construction_path,
            wrong_scope,
            base_execution,
            base_contexts,
            verifier(false),
        ),
        Err(RuntimeConstructionError::ExecutionBindingMismatch)
    ));

    // A correctly MACed successor commitment cannot be substituted into a
    // runtime scoped to the signed historical commitment.
    let substitution_path = TempJournal::new("signed-context-substitution");
    let (execution, snapshot) = execution_and_snapshot(CONTEXT, false, false, false);
    let mut contexts = HistoricalContexts::default();
    contexts.insert(snapshot);
    let mut scoped = new_runtime(
        &substitution_path,
        scope(CONTEXT, execution.base_binding()),
        execution,
        contexts,
        verifier(false),
    )
    .unwrap();
    assert!(matches!(
        scoped.admit(
            successor_request.canonical_request.len(),
            &successor_request.canonical_request,
        ),
        AdmissionOutcome::Refused(AdmissionRefusal::ContextMismatch)
    ));
    assert!(scoped.journal().records().is_empty());
    assert!(scoped.execution().log().is_empty());

    // An in-scope, correctly signed request still fails when the deployment
    // cannot resolve its historical commitment.
    let unknown_path = TempJournal::new("unknown-context");
    let (execution, _) = execution_and_snapshot(SUCCESSOR_CONTEXT, false, false, false);
    let mut unknown = new_runtime(
        &unknown_path,
        scope(SUCCESSOR_CONTEXT, execution.base_binding()),
        execution,
        HistoricalContexts::default(),
        verifier(false),
    )
    .unwrap();
    assert!(matches!(
        unknown.admit(
            successor_request.canonical_request.len(),
            &successor_request.canonical_request,
        ),
        AdmissionOutcome::Refused(AdmissionRefusal::UnknownContext)
    ));
    assert!(unknown.journal().records().is_empty());
    assert!(unknown.execution().log().is_empty());

    // A provider cannot label a different execution substrate with the signed
    // commitment and pass the runtime's independent scope/executor checks.
    let mismatch_path = TempJournal::new("provider-binding-mismatch");
    let (execution, snapshot) = execution_and_snapshot(CONTEXT, false, false, false);
    let mut mismatched = snapshot.clone();
    mismatched.execution_binding[0] ^= 1;
    let mut contexts = HistoricalContexts::default();
    contexts.insert_for(
        (CONTEXT.to_vec(), DOCUMENT.to_vec(), GENESIS.to_vec()),
        mismatched,
    );
    let mut mismatch_runtime = new_runtime(
        &mismatch_path,
        scope(CONTEXT, execution.base_binding()),
        execution,
        contexts,
        verifier(false),
    )
    .unwrap();
    assert!(matches!(
        mismatch_runtime.admit(
            base_request.canonical_request.len(),
            &base_request.canonical_request,
        ),
        AdmissionOutcome::Refused(AdmissionRefusal::ContextMismatch)
    ));
    assert!(mismatch_runtime.journal().records().is_empty());
    assert!(mismatch_runtime.execution().log().is_empty());

    // Append one exact Lean-emitted request and pin the resulting journal head.
    let history_path = TempJournal::new("historical-recovery");
    let (execution, snapshot) = execution_and_snapshot(CONTEXT, false, false, false);
    let binding = execution.base_binding();
    let mut contexts = HistoricalContexts::default();
    contexts.insert(snapshot);
    contexts.insert(successor_snapshot.clone());
    let mut runtime = new_runtime(
        &history_path,
        scope(CONTEXT, binding),
        execution,
        contexts,
        verifier(true),
    )
    .unwrap();
    let receipt = admitted(runtime.admit(
        base_request.canonical_request.len(),
        &base_request.canonical_request,
    ));
    assert_eq!(receipt.sequence, 0);
    assert_eq!(receipt.disposition, AdmissionDisposition::Appended);
    let stored = runtime.journal().records()[0].admission();
    assert_eq!(stored.canonical_request(), base_request.canonical_request);
    assert_eq!(
        stored.observation().signing_bytes,
        base_request.signing_bytes
    );
    assert_eq!(stored.context().commitment, CONTEXT);
    assert_eq!(stored.context().execution_binding, binding);
    assert_eq!(runtime.execution().log().len(), 1);
    let expectation = runtime.journal().recovery_expectation();
    drop(runtime);

    // Restart succeeds with the retained historical context even though a
    // distinct successor snapshot/key is now revoked.
    let reopened =
        AuthenticatedMoveJournal::open_pinned(&history_path.0, journal_options(), expectation)
            .unwrap();
    let (execution, snapshot) = execution_and_snapshot(CONTEXT, false, false, false);
    let mut historical_contexts = HistoricalContexts::default();
    historical_contexts.insert(snapshot);
    historical_contexts.insert(successor_snapshot);
    let recovered = AuthenticatedRuntime::recover(
        base_request.canonical_request.len(),
        scope(CONTEXT, execution.base_binding()),
        verifier(true),
        historical_contexts,
        ContextResolver,
        ContextGrantHolderAuthority,
        ExactMembership,
        execution,
        reopened,
    )
    .expect("recovery must replay the exact retained historical snapshot");
    assert_eq!(recovered.execution().log().len(), 1);
    assert_eq!(
        recovered.journal().records()[0]
            .admission()
            .canonical_request(),
        base_request.canonical_request
    );
    drop(recovered);

    // Losing that historical context is a typed refusal, not substitution of
    // the current successor snapshot.
    let reopened =
        AuthenticatedMoveJournal::open_pinned(&history_path.0, journal_options(), expectation)
            .unwrap();
    let (execution, _) = execution_and_snapshot(CONTEXT, false, false, false);
    let (_, successor_only) = execution_and_snapshot(SUCCESSOR_CONTEXT, false, false, true);
    let mut missing_history = HistoricalContexts::default();
    missing_history.insert(successor_only);
    assert!(matches!(
        AuthenticatedRuntime::recover(
            base_request.canonical_request.len(),
            scope(CONTEXT, execution.base_binding()),
            verifier(true),
            missing_history,
            ContextResolver,
            ContextGrantHolderAuthority,
            ExactMembership,
            execution,
            reopened,
        ),
        Err(RuntimeRecoveryError::Refused {
            sequence: 0,
            reason: AdmissionRefusal::UnknownContext,
        })
    ));

    // Even a provider snapshot with the same commitment and execution digest
    // cannot silently rewrite a stored policy version during recovery: the
    // reconstructed CheckedAdmission must equal the historical record.
    let reopened =
        AuthenticatedMoveJournal::open_pinned(&history_path.0, journal_options(), expectation)
            .unwrap();
    let (execution, mut changed_policy) = execution_and_snapshot(CONTEXT, false, false, false);
    changed_policy.authority_policy = 99;
    let mut changed_contexts = HistoricalContexts::default();
    changed_contexts.insert(changed_policy);
    assert!(matches!(
        AuthenticatedRuntime::recover(
            base_request.canonical_request.len(),
            scope(CONTEXT, execution.base_binding()),
            verifier(true),
            changed_contexts,
            ContextResolver,
            ContextGrantHolderAuthority,
            ExactMembership,
            execution,
            reopened,
        ),
        Err(RuntimeRecoveryError::RecordMismatch { sequence: 0 })
    ));

    let reopened =
        AuthenticatedMoveJournal::open_pinned(&history_path.0, journal_options(), expectation)
            .unwrap();
    let (execution, snapshot) = execution_and_snapshot(CONTEXT, false, false, false);
    let mut wrong_recovery_scope = scope(CONTEXT, execution.base_binding());
    wrong_recovery_scope.execution_binding[0] ^= 1;
    let mut contexts = HistoricalContexts::default();
    contexts.insert(snapshot);
    assert!(matches!(
        AuthenticatedRuntime::recover(
            base_request.canonical_request.len(),
            wrong_recovery_scope,
            verifier(true),
            contexts,
            ContextResolver,
            ContextGrantHolderAuthority,
            ExactMembership,
            execution,
            reopened,
        ),
        Err(RuntimeRecoveryError::ExecutionBindingMismatch)
    ));
}
