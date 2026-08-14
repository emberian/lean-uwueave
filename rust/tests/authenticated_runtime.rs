//! Adversarial canaries for the context-bound authenticated runtime path.
//!
//! All UWV4 request and signing bytes come from the Lean support emitter.
//! This test crate never implements a request encoder.

#[path = "support/runtime_auth_v4_admission.rs"]
mod corpus;

use std::cell::Cell;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::auth::{
    project_runtime_auth_v4_admission, RuntimeAuthV4AdmissionOutcome,
    RuntimeAuthV4AdmissionRefusal, RuntimeAuthV4DecodeRefusal, RuntimeAuthV4ShapeRefusal,
};
use uwueave::auth_runtime::{
    AdmissionContextProvider, AdmissionDisposition, AdmissionOutcome, AdmissionRefusal,
    AuthenticatedRuntime, AuthorityRefusal, ContextRefusal, LeanMoveExecution, MembershipRefusal,
    MoveAuthority, MoveMembership, PinnedAdmissionContext, ResolvedNode, ResolverRefusal,
    RuntimeConstructionError, RuntimeRecoveryError, RuntimeScope, StableIdResolver,
};
use uwueave::auth_verifier::{
    compute_keyed_blake3_mac, InMemoryKeyRegistry, KeyedBlake3Key, KeyedBlake3Verifier,
    RequestVerifier, VerificationAcceptance, VerificationInput, VerificationRefusal,
    KEYED_BLAKE3_ALGORITHM,
};
use uwueave::persistence::{
    AuthenticatedMoveJournal, JournalOptions, RecoveryExpectation, SyncPolicy, TornTailPolicy,
};
use uwueave::{CausalWeave, Grant, MoveLog, MoveOp, NodeId};

const CONTEXT: &[u8] = &[30, 31];
const DOCUMENT: &[u8] = &[1, 2];
const GENESIS: &[u8] = &[3, 4];
const ISSUER: u64 = 17;
const EPOCH: u64 = 2;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempPath(PathBuf);

impl TempPath {
    fn new(label: &str) -> Self {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-auth-runtime-{label}-{}-{nonce}.journal",
            std::process::id()
        ));
        let _ = fs::remove_file(&path);
        Self(path)
    }
}

impl Drop for TempPath {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn options(max_record_bytes: u64) -> JournalOptions {
    JournalOptions {
        torn_tail: TornTailPolicy::Refuse,
        sync: SyncPolicy::Buffered,
        max_record_bytes,
    }
}

fn key() -> KeyedBlake3Key {
    KeyedBlake3Key::from_bytes([7; 32])
}

fn verifier() -> KeyedBlake3Verifier<InMemoryKeyRegistry> {
    let mut registry = InMemoryKeyRegistry::new();
    registry.insert_key(CONTEXT, DOCUMENT, GENESIS, ISSUER, EPOCH, key());
    KeyedBlake3Verifier::new(registry)
}

fn keyed_fixture(case: &str) -> corpus::SignedFixture {
    corpus::signed_fixture(case, |signing_bytes| {
        compute_keyed_blake3_mac(&key(), signing_bytes).to_vec()
    })
}

#[test]
fn lean_emitter_keyed_verifier_and_projection_preserve_every_exact_field() {
    let fixture = keyed_fixture("base");
    assert_eq!(&fixture.canonical_request[..6], b"UWV4\x04\x03");

    let RuntimeAuthV4AdmissionOutcome::Accepted(projected) = project_runtime_auth_v4_admission(
        fixture.canonical_request.len(),
        &fixture.canonical_request,
    ) else {
        panic!("Lean refused its own keyed context-bound fixture")
    };
    assert_eq!(projected.canonical_request, fixture.canonical_request);
    assert_eq!(projected.signing_bytes, fixture.signing_bytes);
    assert_eq!(projected.signature_algorithm, KEYED_BLAKE3_ALGORITHM);
    assert_eq!(projected.document, DOCUMENT);
    assert_eq!(projected.genesis, GENESIS);
    assert_eq!(projected.context_commitment, CONTEXT);
    assert_eq!(projected.issuer, ISSUER);
    assert_eq!(projected.key_epoch, EPOCH);
    assert_eq!(projected.nonce, [5, 6]);
    assert_eq!(projected.operation_id, [21]);
    assert_eq!(projected.lamport, 9);
    assert_eq!(projected.child.stable_id, [10, 11]);
    assert_eq!(projected.child.kernel_index, 3);
    assert_eq!(projected.destination.as_ref().unwrap().stable_id, [12, 13]);
    assert_eq!(projected.destination.as_ref().unwrap().kernel_index, 4);
    assert_eq!(projected.exec_replica, 17);
    assert_eq!(projected.exec_child, 3);
    assert_eq!(projected.exec_destination, Some(4));
    assert_eq!(projected.exec_cite, 7);

    verifier()
        .verify(VerificationInput {
            context_commitment: &projected.context_commitment,
            document: &projected.document,
            genesis: &projected.genesis,
            algorithm: projected.signature_algorithm,
            issuer: projected.issuer,
            key_epoch: projected.key_epoch,
            signing_bytes: &projected.signing_bytes,
            signature: &projected.signature,
        })
        .expect("registered key accepts exact Lean signing bytes");
}

#[test]
fn legacy_kind_and_empty_shapes_fail_before_any_policy_stage() {
    let (mut runtime, _harness) = ordinary_runtime("projection-refusals");
    let legacy = corpus::legacy_request();
    assert_eq!(
        project_runtime_auth_v4_admission(1 << 20, &legacy),
        RuntimeAuthV4AdmissionOutcome::Refused(RuntimeAuthV4AdmissionRefusal::Decode(
            RuntimeAuthV4DecodeRefusal::WrongKind
        ))
    );
    assert!(matches!(
        runtime.admit(1 << 20, &legacy),
        AdmissionOutcome::Refused(AdmissionRefusal::Projection(
            RuntimeAuthV4AdmissionRefusal::Decode(RuntimeAuthV4DecodeRefusal::WrongKind)
        ))
    ));

    for (case, expected) in [
        ("empty_document", RuntimeAuthV4ShapeRefusal::EmptyDocument),
        ("empty_genesis", RuntimeAuthV4ShapeRefusal::EmptyGenesis),
        (
            "empty_context",
            RuntimeAuthV4ShapeRefusal::EmptyContextCommitment,
        ),
        ("empty_nonce", RuntimeAuthV4ShapeRefusal::EmptyNonce),
        (
            "empty_operation_id",
            RuntimeAuthV4ShapeRefusal::EmptyOperationId,
        ),
        ("empty_child_id", RuntimeAuthV4ShapeRefusal::EmptyChildId),
        (
            "empty_destination_id",
            RuntimeAuthV4ShapeRefusal::EmptyDestinationId,
        ),
    ] {
        let request = corpus::request(case, b"nonempty-signature");
        assert_eq!(
            project_runtime_auth_v4_admission(request.len(), &request),
            RuntimeAuthV4AdmissionOutcome::Refused(RuntimeAuthV4AdmissionRefusal::Shape(expected)),
            "case {case}"
        );
        assert!(matches!(
            runtime.admit(request.len(), &request),
            AdmissionOutcome::Refused(AdmissionRefusal::Projection(
                RuntimeAuthV4AdmissionRefusal::Shape(reason)
            )) if reason == expected
        ));
    }
    let empty_signature = corpus::empty_signature_request("base");
    assert_eq!(
        project_runtime_auth_v4_admission(empty_signature.len(), &empty_signature),
        RuntimeAuthV4AdmissionOutcome::Refused(RuntimeAuthV4AdmissionRefusal::Shape(
            RuntimeAuthV4ShapeRefusal::EmptySignature
        ))
    );
    assert!(matches!(
        runtime.admit(empty_signature.len(), &empty_signature),
        AdmissionOutcome::Refused(AdmissionRefusal::Projection(
            RuntimeAuthV4AdmissionRefusal::Shape(RuntimeAuthV4ShapeRefusal::EmptySignature)
        ))
    ));
    assert!(runtime.journal().records().is_empty());
    assert!(runtime.execution().log().is_empty());

    // Exact 2^64/2^63 host-width witnesses use unary Nat encoding and are
    // intentionally exercised directly by the Lean Wave-30 matrix rather
    // than materializing an infeasibly large subprocess fixture here.
}

#[test]
fn scoped_registry_and_exact_signature_fail_closed_for_every_substitution() {
    let base = keyed_fixture("base");
    let base_signature = project_signature(&base.canonical_request);

    for (case, expected) in [
        ("other_context", VerificationRefusal::UnknownContext),
        ("other_document", VerificationRefusal::UnknownDocument),
        ("other_genesis", VerificationRefusal::UnknownGenesis),
        (
            "other_issuer",
            VerificationRefusal::UnknownIssuer { issuer: 18 },
        ),
        (
            "other_epoch",
            VerificationRefusal::UnknownKeyEpoch {
                issuer: ISSUER,
                key_epoch: 3,
            },
        ),
        (
            "other_algorithm",
            VerificationRefusal::UnknownAlgorithm { algorithm: 2 },
        ),
    ] {
        let fixture = keyed_fixture(case);
        let projected = project(&fixture.canonical_request);
        assert_eq!(verify_projected(&projected), Err(expected), "case {case}");
        let (mut runtime, _harness) = ordinary_runtime(case);
        assert!(matches!(
            runtime.admit(
                fixture.canonical_request.len(),
                &fixture.canonical_request
            ),
            AdmissionOutcome::Refused(AdmissionRefusal::Verification(reason)) if reason == expected
        ));
        assert!(runtime.journal().records().is_empty(), "case {case}");
        assert!(runtime.execution().log().is_empty(), "case {case}");
    }

    // Keeping the old signature while Lean changes any signed field fails at
    // authenticity even when the original registry scope is otherwise valid.
    for case in [
        "other_nonce",
        "nonce_collision",
        "child_index_mismatch",
        "destination_index_mismatch",
        "child_identity_substitution",
    ] {
        let request = corpus::request(case, &base_signature);
        let projected = project(&request);
        assert_eq!(
            verify_projected(&projected),
            Err(VerificationRefusal::BadSignature),
            "case {case}"
        );
    }
}

#[test]
fn bad_signature_and_context_or_resolver_unavailability_leave_no_mutation() {
    let bad_signature = corpus::request("base", b"not-the-keyed-mac");
    let (mut bad_runtime, _harness) = ordinary_runtime("bad-signature");
    assert!(matches!(
        bad_runtime.admit(bad_signature.len(), &bad_signature),
        AdmissionOutcome::Refused(AdmissionRefusal::Verification(
            VerificationRefusal::BadSignature
        ))
    ));
    assert!(bad_runtime.journal().records().is_empty());
    assert!(bad_runtime.execution().log().is_empty());

    let fixture = keyed_fixture("base");
    for (label, context_mode, resolver_mode) in [
        ("context-mismatch", Err(ContextRefusal::Mismatch), Ok(())),
        (
            "context-unavailable",
            Err(ContextRefusal::Unavailable),
            Ok(()),
        ),
        ("resolver-missing", Ok(()), Err(ResolverRefusal::Missing)),
        (
            "resolver-unavailable",
            Ok(()),
            Err(ResolverRefusal::Unavailable),
        ),
    ] {
        let (mut runtime, _harness) = runtime(
            label,
            context_mode,
            TestResolver {
                index_delta: 0,
                mode: resolver_mode,
            },
            PolicyMode::Permit,
            PolicyMode::Permit,
            1 << 20,
        );
        assert!(matches!(
            runtime.admit(fixture.canonical_request.len(), &fixture.canonical_request),
            AdmissionOutcome::Refused(_) | AdmissionOutcome::Unavailable(_)
        ));
        assert!(runtime.journal().records().is_empty(), "case {label}");
        assert!(runtime.execution().log().is_empty(), "case {label}");
    }
}

fn project(request: &[u8]) -> uwueave::auth::RuntimeAuthV4AdmissionProjection {
    match project_runtime_auth_v4_admission(request.len(), request) {
        RuntimeAuthV4AdmissionOutcome::Accepted(projection) => projection,
        other => panic!("expected projection, got {other:?}"),
    }
}

fn project_signature(request: &[u8]) -> Vec<u8> {
    project(request).signature
}

fn verify_projected(
    projected: &uwueave::auth::RuntimeAuthV4AdmissionProjection,
) -> Result<uwueave::auth_verifier::VerificationAcceptance, VerificationRefusal> {
    verifier().verify(VerificationInput {
        context_commitment: &projected.context_commitment,
        document: &projected.document,
        genesis: &projected.genesis,
        algorithm: projected.signature_algorithm,
        issuer: projected.issuer,
        key_epoch: projected.key_epoch,
        signing_bytes: &projected.signing_bytes,
        signature: &projected.signature,
    })
}

#[derive(Debug, Clone, Copy)]
enum PolicyMode {
    Permit,
    Deny,
    Unavailable,
}

#[derive(Clone)]
struct TestContextProvider {
    mode: Result<(), ContextRefusal>,
    substrate: TestSubstrate,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TestSubstrate {
    child: NodeId,
    destination: NodeId,
    execution_binding: [u8; 32],
}

impl AdmissionContextProvider for TestContextProvider {
    type Context = TestSubstrate;

    fn pin(
        &self,
        commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
    ) -> Result<PinnedAdmissionContext<Self::Context>, ContextRefusal> {
        self.mode?;
        if commitment != CONTEXT || document != DOCUMENT || genesis != GENESIS {
            return Err(ContextRefusal::Mismatch);
        }
        Ok(PinnedAdmissionContext {
            commitment: commitment.to_vec(),
            document: document.to_vec(),
            genesis: genesis.to_vec(),
            execution_binding: self.substrate.execution_binding,
            resolver_policy: 1,
            authority_policy: 2,
            membership_policy: 3,
            substrate: self.substrate.clone(),
        })
    }
}

#[derive(Clone)]
struct TestResolver {
    index_delta: u64,
    mode: Result<(), ResolverRefusal>,
}

impl StableIdResolver<TestSubstrate> for TestResolver {
    fn resolve(
        &self,
        context: &PinnedAdmissionContext<TestSubstrate>,
        stable_id: &[u8],
    ) -> Result<ResolvedNode, ResolverRefusal> {
        self.mode?;
        match stable_id {
            [10, 11] => Ok(ResolvedNode {
                node_id: context.substrate.child,
                kernel_index: 3 + self.index_delta,
            }),
            [12, 13] => Ok(ResolvedNode {
                node_id: context.substrate.destination,
                kernel_index: 4 + self.index_delta,
            }),
            _ => Err(ResolverRefusal::Missing),
        }
    }
}

#[derive(Clone)]
struct TestAuthority {
    mode: PolicyMode,
    calls: Rc<Cell<usize>>,
}

impl MoveAuthority<TestSubstrate> for TestAuthority {
    fn authorize(
        &self,
        _context: &PinnedAdmissionContext<TestSubstrate>,
        issuer: u64,
        operation: &MoveOp,
    ) -> Result<(), AuthorityRefusal> {
        self.calls.set(self.calls.get() + 1);
        assert_eq!(issuer, ISSUER);
        assert_eq!(operation.cite, 7);
        match self.mode {
            PolicyMode::Permit => Ok(()),
            PolicyMode::Deny => Err(AuthorityRefusal::Denied),
            PolicyMode::Unavailable => Err(AuthorityRefusal::Unavailable),
        }
    }
}

#[derive(Clone)]
struct TestMembership {
    mode: PolicyMode,
    calls: Rc<Cell<usize>>,
}

impl MoveMembership<TestSubstrate> for TestMembership {
    fn allows_move(
        &self,
        _context: &PinnedAdmissionContext<TestSubstrate>,
        issuer: u64,
        operation: &MoveOp,
    ) -> Result<(), MembershipRefusal> {
        self.calls.set(self.calls.get() + 1);
        assert_eq!(issuer, ISSUER);
        assert_eq!(operation.replica, ISSUER);
        match self.mode {
            PolicyMode::Permit => Ok(()),
            PolicyMode::Deny => Err(MembershipRefusal::Denied),
            PolicyMode::Unavailable => Err(MembershipRefusal::Unavailable),
        }
    }
}

struct Harness {
    temp: TempPath,
    authority_calls: Rc<Cell<usize>>,
    membership_calls: Rc<Cell<usize>>,
}

type Runtime = AuthenticatedRuntime<
    KeyedBlake3Verifier<InMemoryKeyRegistry>,
    TestContextProvider,
    TestResolver,
    TestAuthority,
    TestMembership,
    Vec<u8>,
>;

fn execution_and_substrate() -> (LeanMoveExecution<Vec<u8>>, TestSubstrate) {
    let mut weave = CausalWeave::new();
    for index in 0..5 {
        weave
            .insert(vec![], format!("runtime-node-{index}").into_bytes())
            .unwrap();
    }
    let ordered: Vec<_> = weave.nodes().map(|node| node.id()).collect();
    let mut substrate = TestSubstrate {
        child: ordered[3],
        destination: ordered[4],
        execution_binding: [0; 32],
    };
    let mut log = MoveLog::new();
    log.issue(Grant::universal(7));
    let execution = LeanMoveExecution::new(log, weave);
    substrate.execution_binding = execution.base_binding();
    (execution, substrate)
}

fn runtime(
    label: &str,
    context_mode: Result<(), ContextRefusal>,
    resolver: TestResolver,
    authority_mode: PolicyMode,
    membership_mode: PolicyMode,
    max_record_bytes: u64,
) -> (Runtime, Harness) {
    let temp = TempPath::new(label);
    let journal = AuthenticatedMoveJournal::open_pinned(
        &temp.0,
        options(max_record_bytes),
        RecoveryExpectation::EMPTY,
    )
    .unwrap();
    let authority_calls = Rc::new(Cell::new(0));
    let membership_calls = Rc::new(Cell::new(0));
    let (execution, substrate) = execution_and_substrate();
    let scope = RuntimeScope {
        document: DOCUMENT.to_vec(),
        genesis: GENESIS.to_vec(),
        context_commitment: CONTEXT.to_vec(),
        execution_binding: execution.base_binding(),
    };
    let runtime = AuthenticatedRuntime::new(
        scope,
        verifier(),
        TestContextProvider {
            mode: context_mode,
            substrate,
        },
        resolver,
        TestAuthority {
            mode: authority_mode,
            calls: authority_calls.clone(),
        },
        TestMembership {
            mode: membership_mode,
            calls: membership_calls.clone(),
        },
        execution,
        journal,
    )
    .unwrap();
    (
        runtime,
        Harness {
            temp,
            authority_calls,
            membership_calls,
        },
    )
}

fn ordinary_runtime(label: &str) -> (Runtime, Harness) {
    runtime(
        label,
        Ok(()),
        TestResolver {
            index_delta: 0,
            mode: Ok(()),
        },
        PolicyMode::Permit,
        PolicyMode::Permit,
        1 << 20,
    )
}

fn admitted(outcome: AdmissionOutcome) -> uwueave::auth_runtime::AdmissionReceipt {
    match outcome {
        AdmissionOutcome::Accepted(receipt) => receipt,
        other => panic!("expected accepted admission, got {other:?}"),
    }
}

#[test]
fn runtime_appends_exact_bytes_before_ack_then_retry_skips_all_later_stages() {
    let fixture = keyed_fixture("base");
    let (mut runtime, harness) = ordinary_runtime("happy-retry");

    let first =
        admitted(runtime.admit(fixture.canonical_request.len(), &fixture.canonical_request));
    assert_eq!(first.sequence, 0);
    assert_eq!(first.disposition, AdmissionDisposition::Appended);
    assert_eq!(runtime.journal().records().len(), 1);
    let stored = runtime.journal().records()[0].admission();
    assert_eq!(stored.canonical_request(), fixture.canonical_request);
    assert_eq!(stored.observation().signing_bytes, fixture.signing_bytes);
    assert_eq!(runtime.execution().log().len(), 1);

    let retry =
        admitted(runtime.admit(fixture.canonical_request.len(), &fixture.canonical_request));
    assert_eq!(retry.sequence, 0);
    assert_eq!(retry.disposition, AdmissionDisposition::Retry);
    assert_eq!(runtime.journal().records().len(), 1);
    assert_eq!(runtime.execution().log().len(), 1);
    assert_eq!(harness.authority_calls.get(), 1);
    assert_eq!(harness.membership_calls.get(), 1);

    let expectation = runtime.journal().recovery_expectation();
    drop(runtime);
    let reopened =
        AuthenticatedMoveJournal::open_pinned(&harness.temp.0, options(1 << 20), expectation)
            .unwrap();
    assert_eq!(reopened.records().len(), 1);
    assert_eq!(
        reopened.records()[0].admission().canonical_request(),
        fixture.canonical_request
    );

    let (execution, substrate) = execution_and_substrate();
    let scope = RuntimeScope {
        document: DOCUMENT.to_vec(),
        genesis: GENESIS.to_vec(),
        context_commitment: CONTEXT.to_vec(),
        execution_binding: execution.base_binding(),
    };
    let recovered = AuthenticatedRuntime::recover(
        fixture.canonical_request.len(),
        scope,
        verifier(),
        TestContextProvider {
            mode: Ok(()),
            substrate,
        },
        TestResolver {
            index_delta: 0,
            mode: Ok(()),
        },
        TestAuthority {
            mode: PolicyMode::Permit,
            calls: Rc::new(Cell::new(0)),
        },
        TestMembership {
            mode: PolicyMode::Permit,
            calls: Rc::new(Cell::new(0)),
        },
        execution,
        reopened,
    )
    .expect("pinned recovery revalidates exact historical record");
    assert_eq!(recovered.execution().log().len(), 1);
}

#[test]
fn nonce_and_operation_collisions_refuse_without_policy_or_commit_mutation() {
    let (mut runtime, harness) = ordinary_runtime("collisions");
    let base = keyed_fixture("base");
    admitted(runtime.admit(base.canonical_request.len(), &base.canonical_request));

    let nonce_collision = keyed_fixture("nonce_collision");
    assert!(matches!(
        runtime.admit(
            nonce_collision.canonical_request.len(),
            &nonce_collision.canonical_request
        ),
        AdmissionOutcome::Refused(AdmissionRefusal::NonceCollision {
            existing_sequence: 0
        })
    ));
    let operation_collision = keyed_fixture("operation_id_collision");
    assert!(matches!(
        runtime.admit(
            operation_collision.canonical_request.len(),
            &operation_collision.canonical_request
        ),
        AdmissionOutcome::Refused(AdmissionRefusal::OperationCollision {
            existing_sequence: 0
        })
    ));
    assert_eq!(runtime.journal().records().len(), 1);
    assert_eq!(runtime.execution().log().len(), 1);
    assert_eq!(harness.authority_calls.get(), 1);
    assert_eq!(harness.membership_calls.get(), 1);
}

#[derive(Clone)]
struct AcceptAnyNonemptySignature {
    calls: Rc<Cell<usize>>,
}

impl RequestVerifier for AcceptAnyNonemptySignature {
    fn verify(
        &self,
        input: VerificationInput<'_>,
    ) -> Result<VerificationAcceptance, VerificationRefusal> {
        self.calls.set(self.calls.get() + 1);
        if input.signature.is_empty() {
            Err(VerificationRefusal::BadSignature)
        } else {
            Ok(VerificationAcceptance::from_verifier_acceptance(input))
        }
    }
}

#[test]
fn fixed_runtime_scope_refuses_document_genesis_and_context_substitution() {
    let request = corpus::request("base", b"permissive-verifier-signature");
    for label in ["scope-document", "scope-genesis", "scope-context"] {
        let (runtime, _harness) = ordinary_runtime(label);
        let (mut scope, _, contexts, resolver, authority, membership, execution, journal) =
            runtime.into_parts();
        match label {
            "scope-document" => scope.document = vec![8, 8],
            "scope-genesis" => scope.genesis = vec![9, 9],
            "scope-context" => scope.context_commitment = vec![32, 33],
            _ => unreachable!(),
        }
        let mut scoped = AuthenticatedRuntime::new(
            scope,
            AcceptAnyNonemptySignature {
                calls: Rc::new(Cell::new(0)),
            },
            contexts,
            resolver,
            authority,
            membership,
            execution,
            journal,
        )
        .unwrap();
        assert!(matches!(
            scoped.admit(request.len(), &request),
            AdmissionOutcome::Refused(AdmissionRefusal::ContextMismatch)
        ));
        assert!(scoped.journal().records().is_empty());
        assert!(scoped.execution().log().is_empty());
    }
}

#[test]
fn construction_and_recovery_refuse_wrong_execution_binding() {
    let (runtime, _harness) = ordinary_runtime("wrong-binding-new");
    let (mut scope, verifier, contexts, resolver, authority, membership, execution, journal) =
        runtime.into_parts();
    scope.execution_binding[0] ^= 1;
    assert!(matches!(
        AuthenticatedRuntime::new(
            scope, verifier, contexts, resolver, authority, membership, execution, journal,
        ),
        Err(RuntimeConstructionError::ExecutionBindingMismatch)
    ));

    let fixture = keyed_fixture("base");
    let (mut runtime, _harness) = ordinary_runtime("wrong-binding-recovery");
    admitted(runtime.admit(fixture.canonical_request.len(), &fixture.canonical_request));
    let (mut scope, verifier, contexts, resolver, authority, membership, _, journal) =
        runtime.into_parts();
    let (execution, _substrate) = execution_and_substrate();
    scope.execution_binding[0] ^= 1;
    assert!(matches!(
        AuthenticatedRuntime::recover(
            fixture.canonical_request.len(),
            scope,
            verifier,
            contexts,
            resolver,
            authority,
            membership,
            execution,
            journal,
        ),
        Err(RuntimeRecoveryError::ExecutionBindingMismatch)
    ));
}

#[test]
fn alternate_valid_signature_is_retry_only_after_reverification() {
    let first = corpus::request("base", b"first-valid-signature");
    let alternate = corpus::request("base", b"alternate-valid-signature");
    let (runtime, harness) = ordinary_runtime("alternate-signature");
    let (scope, _, contexts, resolver, authority, membership, execution, journal) =
        runtime.into_parts();
    let verification_calls = Rc::new(Cell::new(0));
    let mut runtime = AuthenticatedRuntime::new(
        scope,
        AcceptAnyNonemptySignature {
            calls: verification_calls.clone(),
        },
        contexts,
        resolver,
        authority,
        membership,
        execution,
        journal,
    )
    .unwrap();
    assert_eq!(
        admitted(runtime.admit(first.len(), &first)).disposition,
        AdmissionDisposition::Appended
    );
    assert_eq!(
        admitted(runtime.admit(alternate.len(), &alternate)).disposition,
        AdmissionDisposition::Retry
    );
    assert_eq!(runtime.journal().records().len(), 1);
    assert_eq!(runtime.execution().log().len(), 1);
    assert_eq!(verification_calls.get(), 2, "retry must be reverified");
    assert_eq!(harness.authority_calls.get(), 1);
    assert_eq!(harness.membership_calls.get(), 1);
}

#[test]
fn resolver_authority_membership_and_storage_refusals_never_commit() {
    let fixture = keyed_fixture("base");
    let cases = [
        (
            "resolver-mismatch",
            TestResolver {
                index_delta: 1,
                mode: Ok(()),
            },
            PolicyMode::Permit,
            PolicyMode::Permit,
        ),
        (
            "authority-denied",
            TestResolver {
                index_delta: 0,
                mode: Ok(()),
            },
            PolicyMode::Deny,
            PolicyMode::Permit,
        ),
        (
            "membership-denied",
            TestResolver {
                index_delta: 0,
                mode: Ok(()),
            },
            PolicyMode::Permit,
            PolicyMode::Deny,
        ),
        (
            "authority-unavailable",
            TestResolver {
                index_delta: 0,
                mode: Ok(()),
            },
            PolicyMode::Unavailable,
            PolicyMode::Permit,
        ),
        (
            "membership-unavailable",
            TestResolver {
                index_delta: 0,
                mode: Ok(()),
            },
            PolicyMode::Permit,
            PolicyMode::Unavailable,
        ),
    ];
    for (label, resolver, authority, membership) in cases {
        let (mut runtime, _harness) =
            runtime(label, Ok(()), resolver, authority, membership, 1 << 20);
        let outcome = runtime.admit(fixture.canonical_request.len(), &fixture.canonical_request);
        match label {
            "resolver-mismatch" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::StableIndexMismatch {
                    signed: 3,
                    resolved: 4
                })
            )),
            "authority-denied" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::AuthorityDenied)
            )),
            "membership-denied" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::MembershipDenied)
            )),
            "authority-unavailable" => assert!(matches!(
                outcome,
                AdmissionOutcome::Unavailable(
                    uwueave::auth_runtime::AdmissionUnavailable::Authority
                )
            )),
            "membership-unavailable" => assert!(matches!(
                outcome,
                AdmissionOutcome::Unavailable(
                    uwueave::auth_runtime::AdmissionUnavailable::Membership
                )
            )),
            _ => unreachable!(),
        }
        assert!(runtime.journal().records().is_empty(), "case {label}");
        assert!(runtime.execution().log().is_empty(), "case {label}");
    }

    let (mut bounded, _harness) = runtime(
        "append-refusal",
        Ok(()),
        TestResolver {
            index_delta: 0,
            mode: Ok(()),
        },
        PolicyMode::Permit,
        PolicyMode::Permit,
        1,
    );
    assert!(matches!(
        bounded.admit(fixture.canonical_request.len(), &fixture.canonical_request),
        AdmissionOutcome::StorageRefused(_)
    ));
    assert!(bounded.journal().records().is_empty());
    assert!(bounded.execution().log().is_empty());
}
