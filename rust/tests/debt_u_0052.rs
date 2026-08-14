//! Immutable implementation evidence for debt U-0052.
//!
//! The exact kind-3 request fixtures are embedded byte-for-byte from the
//! Lean-owned admission corpus; this target contains no UWV4 request encoder.
//! Fresh admission, alternate-signature retry, pinned recovery, and separating
//! mutations are exercised at the public shipping runtime surfaces.

use std::cell::Cell;
use std::fs;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::auth::{
    check_runtime_auth_v4_admission_trace, project_runtime_auth_v4_admission,
    RuntimeAuthV4AdmissionOutcome, RuntimeAuthV4AdmissionTraceRefusal, MAX_ADMISSION_TRACE_BYTES,
};
use uwueave::auth_runtime::{
    AdmissionCertificate, AdmissionContextProvider, AdmissionDisposition, AdmissionOutcome,
    AdmissionRefusal, AuthenticatedRuntime, AuthorityAcceptance, AuthorityInput, AuthorityRefusal,
    ContextGrantHolderAuthority, ContextRefusal, GrantHolderBindings, GrantHolderContext,
    LeanMoveExecution, MembershipInput, MembershipRefusal, MoveAuthority, MoveMembership,
    PinnedAdmissionContext, ResolvedNode, ResolverRefusal, RuntimeRecoveryError, RuntimeScope,
    StableIdResolver,
};
use uwueave::auth_verifier::{
    RequestVerifier, VerificationAcceptance, VerificationInput, VerificationRefusal,
};
use uwueave::persistence::{
    AuthenticatedMoveJournal, JournalOptions, RecoveryExpectation, SyncPolicy, TornTailPolicy,
};
use uwueave::{CausalWeave, Grant, MoveLog, MoveOp, NodeId};

const CONTEXT: &[u8] = &[30, 31];
const DOCUMENT: &[u8] = &[1, 2];
const GENESIS: &[u8] = &[3, 4];
const ISSUER: u64 = 17;
const MAX_BYTES: usize = 1 << 20;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempPath(PathBuf);

impl TempPath {
    fn new(label: &str, extension: &str) -> Self {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-auth-trace-{label}-{}-{nonce}.{extension}",
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

const BASE_REQUEST_HEX: &str = "55575634040361510101000102520101000304530154010101010101010101010101010101010100550101005601010005065741010015420101010101010101010043310101000a0b32010101004401310101000c0d320101010100450101010101010100580101001e1f6201010101010101010101010101010101010101010101010100696d6d757461626c652d75303035322d666978747572650a";
const ALTERNATE_REQUEST_HEX: &str = "55575634040361510101000102520101000304530154010101010101010101010101010101010100550101005601010005065741010015420101010101010101010043310101000a0b32010101004401310101000c0d320101010100450101010101010100580101001e1f62010101010101010101010101010101010101010101010101010100696d6d757461626c652d75303035322d616c7465726e6174650a";
const DUPLICATE_MOVE_REQUEST_HEX: &str = "55575634040361510101000102520101000304530154010101010101010101010101010101010100550101005601010005075741010016420101010101010101010043310101000a0b32010101004401310101000c0d320101010100450101010101010100580101001e1f6201010101010101010101010101010101010101010101010100696d6d757461626c652d75303035322d666978747572650a";
const CITE_ZERO_REQUEST_HEX: &str = "55575634040361510101000102520101000304530154010101010101010101010101010101010100550101005601010005065741010015420101010101010101010043310101000a0b32010101004401310101000c0d3201010101004500580101001e1f6201010101010101010101010101010101010101010101010100696d6d757461626c652d75303035322d666978747572650a";

fn decode_fixture(hex: &str) -> Vec<u8> {
    assert_eq!(hex.len() % 2, 0);
    hex.as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16)
                .expect("fixture is lowercase hexadecimal")
        })
        .collect()
}

fn request(case: &str, signature: &[u8]) -> Vec<u8> {
    let fixture = match (case, signature) {
        ("base", b"alternate-valid-signature") => ALTERNATE_REQUEST_HEX,
        ("base", _) => BASE_REQUEST_HEX,
        ("duplicate_move", _) => DUPLICATE_MOVE_REQUEST_HEX,
        ("cite0", _) => CITE_ZERO_REQUEST_HEX,
        _ => panic!("unknown immutable request fixture: {case}"),
    };
    decode_fixture(fixture)
}

fn options_with_max(max_record_bytes: u64) -> JournalOptions {
    JournalOptions {
        torn_tail: TornTailPolicy::Refuse,
        sync: SyncPolicy::Buffered,
        max_record_bytes,
    }
}

fn options() -> JournalOptions {
    options_with_max(1 << 24)
}

#[derive(Debug, Clone, Copy)]
enum ReceiptMode {
    Accept,
    Refuse,
    Mismatch,
}

#[derive(Clone)]
struct TestVerifier {
    mode: ReceiptMode,
    calls: Rc<Cell<usize>>,
}

impl RequestVerifier for TestVerifier {
    fn verify(
        &self,
        input: VerificationInput<'_>,
    ) -> Result<VerificationAcceptance, VerificationRefusal> {
        self.calls.set(self.calls.get() + 1);
        match self.mode {
            ReceiptMode::Accept if !input.signature.is_empty() => {
                Ok(VerificationAcceptance::from_verifier_acceptance(input))
            }
            ReceiptMode::Accept | ReceiptMode::Refuse => Err(VerificationRefusal::BadSignature),
            ReceiptMode::Mismatch => {
                let mismatched = VerificationInput {
                    issuer: input.issuer.wrapping_add(1),
                    ..input
                };
                Ok(VerificationAcceptance::from_verifier_acceptance(mismatched))
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ContextMode {
    Accept,
    Unknown,
    Mismatch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TestSubstrate {
    child: NodeId,
    destination: NodeId,
    execution_binding: [u8; 32],
    holders: GrantHolderBindings,
}

impl GrantHolderContext for TestSubstrate {
    fn holds_grant(&self, issuer: u64, cite: u64) -> bool {
        self.holders.holds(issuer, cite)
    }
}

#[derive(Clone)]
struct TestContexts {
    mode: ContextMode,
    substrate: TestSubstrate,
}

impl AdmissionContextProvider for TestContexts {
    type Context = TestSubstrate;

    fn pin(
        &self,
        commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
    ) -> Result<PinnedAdmissionContext<Self::Context>, ContextRefusal> {
        match self.mode {
            ContextMode::Unknown => return Err(ContextRefusal::Unknown),
            ContextMode::Accept | ContextMode::Mismatch => {}
        }
        let returned_commitment = match self.mode {
            ContextMode::Mismatch => vec![99],
            ContextMode::Accept | ContextMode::Unknown => commitment.to_vec(),
        };
        Ok(PinnedAdmissionContext {
            commitment: returned_commitment,
            document: document.to_vec(),
            genesis: genesis.to_vec(),
            execution_binding: self.substrate.execution_binding,
            resolver_policy: 11,
            authority_policy: 12,
            membership_policy: 13,
            substrate: self.substrate.clone(),
        })
    }
}

#[derive(Clone)]
struct TestResolver {
    mode: ReceiptMode,
}

impl StableIdResolver<TestSubstrate> for TestResolver {
    fn resolve(
        &self,
        context: &PinnedAdmissionContext<TestSubstrate>,
        stable_id: &[u8],
    ) -> Result<ResolvedNode, ResolverRefusal> {
        if matches!(self.mode, ReceiptMode::Refuse) {
            return Err(ResolverRefusal::Missing);
        }
        let (node_id, index) = match stable_id {
            [10, 11] => (context.substrate.child, 3),
            [12, 13] => (context.substrate.destination, 4),
            _ => return Err(ResolverRefusal::Missing),
        };
        Ok(ResolvedNode {
            node_id,
            kernel_index: if matches!(self.mode, ReceiptMode::Mismatch) {
                index + 1
            } else {
                index
            },
        })
    }
}

#[derive(Clone)]
struct TestAuthority {
    mode: ReceiptMode,
    calls: Rc<Cell<usize>>,
}

impl MoveAuthority<TestSubstrate> for TestAuthority {
    fn authorize(
        &self,
        context: &PinnedAdmissionContext<TestSubstrate>,
        input: AuthorityInput<'_>,
    ) -> Result<AuthorityAcceptance, AuthorityRefusal> {
        self.calls.set(self.calls.get() + 1);
        match self.mode {
            ReceiptMode::Accept => ContextGrantHolderAuthority.authorize(context, input),
            ReceiptMode::Refuse => Err(AuthorityRefusal::Denied),
            ReceiptMode::Mismatch => {
                let mismatched = AuthorityInput {
                    authority_policy: input.authority_policy.wrapping_add(1),
                    ..input
                };
                Ok(AuthorityAcceptance::from_authority_acceptance(mismatched))
            }
        }
    }
}

#[derive(Clone)]
struct TestMembership {
    mode: ReceiptMode,
    calls: Rc<Cell<usize>>,
}

impl MoveMembership<TestSubstrate> for TestMembership {
    fn allows_move(
        &self,
        _context: &PinnedAdmissionContext<TestSubstrate>,
        _issuer: u64,
        _operation: &MoveOp,
    ) -> Result<(), MembershipRefusal> {
        self.calls.set(self.calls.get() + 1);
        match self.mode {
            ReceiptMode::Accept => Ok(()),
            ReceiptMode::Refuse | ReceiptMode::Mismatch => Err(MembershipRefusal::Denied),
        }
    }
}

#[derive(Clone, Copy)]
struct Modes {
    verifier: ReceiptMode,
    context: ContextMode,
    resolver: ReceiptMode,
    authority: ReceiptMode,
    membership: ReceiptMode,
}

impl Modes {
    const ACCEPT: Self = Self {
        verifier: ReceiptMode::Accept,
        context: ContextMode::Accept,
        resolver: ReceiptMode::Accept,
        authority: ReceiptMode::Accept,
        membership: ReceiptMode::Accept,
    };
}

struct Harness {
    path: TempPath,
    verifier_calls: Rc<Cell<usize>>,
    authority_calls: Rc<Cell<usize>>,
    membership_calls: Rc<Cell<usize>>,
}

type Runtime = AuthenticatedRuntime<
    TestVerifier,
    TestContexts,
    TestResolver,
    TestAuthority,
    TestMembership,
    Vec<u8>,
>;

fn root_weave() -> CausalWeave<Vec<u8>> {
    let mut weave = CausalWeave::new();
    for index in 0..5 {
        weave
            .insert(vec![], format!("trace-root-{index}").into_bytes())
            .unwrap();
    }
    weave
}

fn cycle_weave() -> CausalWeave<Vec<u8>> {
    for candidate in 0u64..100_000 {
        let mut weave = CausalWeave::new();
        for index in 0..3 {
            weave
                .insert(vec![], format!("trace-cycle-filler-{index}").into_bytes())
                .unwrap();
        }
        let child = weave
            .insert(
                vec![],
                format!("trace-cycle-child-{candidate}").into_bytes(),
            )
            .unwrap();
        let destination = weave
            .insert(
                vec![child],
                format!("trace-cycle-destination-{candidate}").into_bytes(),
            )
            .unwrap();
        let ordered: Vec<_> = weave.nodes().map(|node| node.id()).collect();
        if ordered[3] == child && ordered[4] == destination {
            return weave;
        }
    }
    panic!("could not construct deterministic index-3/index-4 cycle witness")
}

fn execution(cycle: bool, grant_id: u64) -> (LeanMoveExecution<Vec<u8>>, TestSubstrate) {
    let weave = if cycle { cycle_weave() } else { root_weave() };
    let ordered: Vec<_> = weave.nodes().map(|node| node.id()).collect();
    let mut holders = GrantHolderBindings::new();
    if grant_id != 0 {
        holders.bind(ISSUER, grant_id).unwrap();
    }
    let mut log = MoveLog::new();
    log.issue(Grant::universal(grant_id));
    let execution = LeanMoveExecution::new(log, weave);
    let substrate = TestSubstrate {
        child: ordered[3],
        destination: ordered[4],
        execution_binding: execution.base_binding(),
        holders,
    };
    (execution, substrate)
}

fn runtime(label: &str, modes: Modes, cycle: bool, grant_id: u64) -> (Runtime, Harness) {
    runtime_with_record_bound(label, modes, cycle, grant_id, 1 << 24)
}

fn runtime_with_record_bound(
    label: &str,
    modes: Modes,
    cycle: bool,
    grant_id: u64,
    max_record_bytes: u64,
) -> (Runtime, Harness) {
    let path = TempPath::new(label, "journal");
    let journal = AuthenticatedMoveJournal::open_pinned(
        &path.0,
        options_with_max(max_record_bytes),
        RecoveryExpectation::EMPTY,
    )
    .unwrap();
    let (execution, substrate) = execution(cycle, grant_id);
    let scope = RuntimeScope {
        document: DOCUMENT.to_vec(),
        genesis: GENESIS.to_vec(),
        context_commitment: CONTEXT.to_vec(),
        execution_binding: execution.base_binding(),
    };
    let verifier_calls = Rc::new(Cell::new(0));
    let authority_calls = Rc::new(Cell::new(0));
    let membership_calls = Rc::new(Cell::new(0));
    let runtime = AuthenticatedRuntime::new(
        scope,
        TestVerifier {
            mode: modes.verifier,
            calls: verifier_calls.clone(),
        },
        TestContexts {
            mode: modes.context,
            substrate,
        },
        TestResolver {
            mode: modes.resolver,
        },
        TestAuthority {
            mode: modes.authority,
            calls: authority_calls.clone(),
        },
        TestMembership {
            mode: modes.membership,
            calls: membership_calls.clone(),
        },
        execution,
        journal,
    )
    .unwrap();
    (
        runtime,
        Harness {
            path,
            verifier_calls,
            authority_calls,
            membership_calls,
        },
    )
}

fn accepted(outcome: AdmissionOutcome) -> uwueave::auth_runtime::AdmissionReceipt {
    match outcome {
        AdmissionOutcome::Accepted(receipt) => receipt,
        other => panic!("expected accepted admission, got {other:?}"),
    }
}

fn projection(request: &[u8]) -> uwueave::auth::RuntimeAuthV4AdmissionProjection {
    match project_runtime_auth_v4_admission(request.len(), request) {
        RuntimeAuthV4AdmissionOutcome::Accepted(projection) => projection,
        other => panic!("expected accepted projection, got {other:?}"),
    }
}

fn fresh_applied_exact_retry_and_pinned_recovery_keep_distinct_evidence() {
    let first_request = request("base", b"first-valid-signature");
    let retry_request = request("base", b"alternate-valid-signature");
    let retry_projection = projection(&retry_request);
    let (mut runtime, harness) = runtime("positive-retry-recovery", Modes::ACCEPT, false, 7);

    let fresh = accepted(runtime.admit(MAX_BYTES, &first_request));
    assert_eq!(fresh.sequence, 0);
    assert_eq!(fresh.disposition, AdmissionDisposition::Appended);
    let (fresh_trace, fresh_verification, fresh_authority, fresh_membership) =
        match &fresh.certificate {
            AdmissionCertificate::Fresh {
                trace,
                verification,
                authority,
                membership,
            } => (trace, verification, authority, membership),
            other => panic!("fresh append returned weaker evidence: {other:?}"),
        };
    assert_eq!(
        check_runtime_auth_v4_admission_trace(fresh_trace.certificate_bytes()).unwrap(),
        *fresh_trace
    );
    let first_projection = projection(&first_request);
    assert!(fresh_verification.matches_input(VerificationInput {
        context_commitment: &first_projection.context_commitment,
        document: &first_projection.document,
        genesis: &first_projection.genesis,
        algorithm: first_projection.signature_algorithm,
        issuer: first_projection.issuer,
        key_epoch: first_projection.key_epoch,
        signing_bytes: &first_projection.signing_bytes,
        signature: &first_projection.signature,
    }));
    let operation = *runtime
        .execution()
        .log()
        .ops()
        .next()
        .expect("fresh admission committed one exact operation");
    assert!(fresh_authority.matches_input(AuthorityInput {
        context_commitment: CONTEXT,
        authority_policy: 12,
        issuer: ISSUER,
        cite: 7,
        operation: &operation,
    }));
    assert!(fresh_membership.matches_input(MembershipInput {
        context_commitment: CONTEXT,
        membership_policy: 13,
        issuer: ISSUER,
        operation: &operation,
    }));
    assert_eq!(
        runtime.journal().records()[0]
            .admission()
            .certificate_bytes(),
        fresh_trace.certificate_bytes()
    );

    let retry = accepted(runtime.admit(MAX_BYTES, &retry_request));
    assert_eq!(retry.sequence, 0);
    assert_eq!(retry.disposition, AdmissionDisposition::Retry);
    match retry.certificate {
        AdmissionCertificate::VerifiedRetry {
            prior_sequence,
            prior_commitment,
            prior_certificate,
            current_verification,
            current_projection,
        } => {
            assert_eq!(prior_sequence, fresh.sequence);
            assert_eq!(prior_commitment, fresh.head_commitment);
            assert_eq!(prior_certificate, *fresh_trace);
            assert_eq!(current_projection, retry_projection);
            assert!(current_verification.matches_input(VerificationInput {
                context_commitment: &retry_projection.context_commitment,
                document: &retry_projection.document,
                genesis: &retry_projection.genesis,
                algorithm: retry_projection.signature_algorithm,
                issuer: retry_projection.issuer,
                key_epoch: retry_projection.key_epoch,
                signing_bytes: &retry_projection.signing_bytes,
                signature: &retry_projection.signature,
            }));
        }
        other => panic!("retry manufactured a fresh trace: {other:?}"),
    }
    assert_eq!(runtime.journal().records().len(), 1);
    assert_eq!(runtime.execution().log().len(), 1);
    assert_eq!(harness.verifier_calls.get(), 2);
    assert_eq!(harness.authority_calls.get(), 1);
    assert_eq!(harness.membership_calls.get(), 1);

    let expectation = runtime.journal().recovery_expectation();
    drop(runtime);
    let journal = AuthenticatedMoveJournal::open_pinned(&harness.path.0, options(), expectation)
        .expect("reopen exact pinned authenticated journal");
    let (execution, substrate) = execution(false, 7);
    let recovered_verifier_calls = Rc::new(Cell::new(0));
    let recovered_authority_calls = Rc::new(Cell::new(0));
    let recovered_membership_calls = Rc::new(Cell::new(0));
    let recovered = AuthenticatedRuntime::recover(
        MAX_BYTES,
        RuntimeScope {
            document: DOCUMENT.to_vec(),
            genesis: GENESIS.to_vec(),
            context_commitment: CONTEXT.to_vec(),
            execution_binding: execution.base_binding(),
        },
        TestVerifier {
            mode: ReceiptMode::Accept,
            calls: recovered_verifier_calls.clone(),
        },
        TestContexts {
            mode: ContextMode::Accept,
            substrate,
        },
        TestResolver {
            mode: ReceiptMode::Accept,
        },
        TestAuthority {
            mode: ReceiptMode::Accept,
            calls: recovered_authority_calls.clone(),
        },
        TestMembership {
            mode: ReceiptMode::Accept,
            calls: recovered_membership_calls.clone(),
        },
        execution,
        journal,
    )
    .expect("pinned recovery rechecks Lean certificate and rebuilds exact record");
    assert_eq!(recovered.execution().log().len(), 1);
    assert_eq!(recovered.validated_records().len(), 1);
    assert_eq!(recovered.validated_records()[0].sequence, 0);
    assert_eq!(recovered.validated_records()[0].certificate, *fresh_trace);
    assert_eq!(recovered_verifier_calls.get(), 1);
    assert_eq!(recovered_authority_calls.get(), 1);
    assert_eq!(recovered_membership_calls.get(), 1);
}

fn fresh_cycle_skip_is_a_lean_validated_positive_trace() {
    let request = request("base", b"cycle-valid-signature");
    let (mut runtime, _harness) = runtime("positive-cycle", Modes::ACCEPT, true, 7);
    let receipt = accepted(runtime.admit(MAX_BYTES, &request));
    assert_eq!(
        receipt.kernel_observation,
        uwueave::persistence::KernelAdmissionObservation::SkippedCycle
    );
    let AdmissionCertificate::Fresh { trace, .. } = receipt.certificate else {
        panic!("cycle-skipped fresh admission lacked a fresh certificate")
    };
    assert!(check_runtime_auth_v4_admission_trace(trace.certificate_bytes()).is_ok());
    assert_eq!(runtime.journal().records().len(), 1);
    assert_eq!(runtime.execution().log().len(), 1);
}

fn distinct_signed_identity_can_certify_an_idempotent_resolved_move() {
    let base = request("base", b"first-resolved-move-signature");
    let duplicate = request("duplicate_move", b"second-resolved-move-signature");
    let (mut runtime, harness) = runtime("operation-was-not-new", Modes::ACCEPT, false, 7);

    let first = accepted(runtime.admit(MAX_BYTES, &base));
    assert_eq!(first.disposition, AdmissionDisposition::Appended);
    assert!(runtime.journal().records()[0]
        .admission()
        .trace()
        .operation_was_new());

    let second = accepted(runtime.admit(MAX_BYTES, &duplicate));
    assert_eq!(second.sequence, 1);
    assert_eq!(second.disposition, AdmissionDisposition::Appended);
    let AdmissionCertificate::Fresh { trace, .. } = second.certificate else {
        panic!("distinct signed identity did not receive a fresh trace")
    };
    assert!(check_runtime_auth_v4_admission_trace(trace.certificate_bytes()).is_ok());
    let second_trace = trace.clone();
    assert!(!runtime.journal().records()[1]
        .admission()
        .trace()
        .operation_was_new());
    assert_eq!(runtime.journal().records().len(), 2);
    assert_eq!(
        runtime.execution().log().len(),
        1,
        "the grow-only MoveOp set absorbs the duplicate resolved value"
    );
    assert_eq!(harness.verifier_calls.get(), 2);
    assert_eq!(harness.authority_calls.get(), 2);
    assert_eq!(harness.membership_calls.get(), 2);

    let expectation = runtime.journal().recovery_expectation();
    drop(runtime);
    let journal = AuthenticatedMoveJournal::open_pinned(&harness.path.0, options(), expectation)
        .expect("reopen two-record operation-newness journal");
    let (execution, substrate) = execution(false, 7);
    let recovered = AuthenticatedRuntime::recover(
        MAX_BYTES,
        RuntimeScope {
            document: DOCUMENT.to_vec(),
            genesis: GENESIS.to_vec(),
            context_commitment: CONTEXT.to_vec(),
            execution_binding: execution.base_binding(),
        },
        TestVerifier {
            mode: ReceiptMode::Accept,
            calls: Rc::new(Cell::new(0)),
        },
        TestContexts {
            mode: ContextMode::Accept,
            substrate,
        },
        TestResolver {
            mode: ReceiptMode::Accept,
        },
        TestAuthority {
            mode: ReceiptMode::Accept,
            calls: Rc::new(Cell::new(0)),
        },
        TestMembership {
            mode: ReceiptMode::Accept,
            calls: Rc::new(Cell::new(0)),
        },
        execution,
        journal,
    )
    .expect("recovery exactly rebuilds true then false operation-newness traces");
    assert_eq!(recovered.validated_records().len(), 2);
    assert_eq!(recovered.validated_records()[1].certificate, second_trace);
    assert!(recovered.journal().records()[0]
        .admission()
        .trace()
        .operation_was_new());
    assert!(!recovered.journal().records()[1]
        .admission()
        .trace()
        .operation_was_new());
    assert_eq!(recovered.execution().log().len(), 1);
}

fn every_host_stage_refusal_prevents_trace_append_and_commit() {
    let request = request("base", b"stage-valid-signature");
    let cases = [
        (
            "signed-refusal",
            Modes {
                verifier: ReceiptMode::Refuse,
                ..Modes::ACCEPT
            },
        ),
        (
            "signed-receipt-mismatch",
            Modes {
                verifier: ReceiptMode::Mismatch,
                ..Modes::ACCEPT
            },
        ),
        (
            "context-unknown",
            Modes {
                context: ContextMode::Unknown,
                ..Modes::ACCEPT
            },
        ),
        (
            "context-mismatch",
            Modes {
                context: ContextMode::Mismatch,
                ..Modes::ACCEPT
            },
        ),
        (
            "resolution-missing",
            Modes {
                resolver: ReceiptMode::Refuse,
                ..Modes::ACCEPT
            },
        ),
        (
            "resolution-mismatch",
            Modes {
                resolver: ReceiptMode::Mismatch,
                ..Modes::ACCEPT
            },
        ),
        (
            "authority-denied",
            Modes {
                authority: ReceiptMode::Refuse,
                ..Modes::ACCEPT
            },
        ),
        (
            "authority-receipt-mismatch",
            Modes {
                authority: ReceiptMode::Mismatch,
                ..Modes::ACCEPT
            },
        ),
        (
            "membership-denied",
            Modes {
                membership: ReceiptMode::Refuse,
                ..Modes::ACCEPT
            },
        ),
    ];
    for (label, modes) in cases {
        let (mut runtime, _harness) = runtime(label, modes, false, 7);
        let outcome = runtime.admit(MAX_BYTES, &request);
        match label {
            "signed-refusal" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::Verification(
                    VerificationRefusal::BadSignature
                ))
            )),
            "signed-receipt-mismatch" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::VerificationReceiptMismatch)
            )),
            "context-unknown" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::UnknownContext)
            )),
            "context-mismatch" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::ContextMismatch)
            )),
            "resolution-missing" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::MissingStableId)
            )),
            "resolution-mismatch" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::StableIndexMismatch {
                    signed: 3,
                    resolved: 4,
                })
            )),
            "authority-denied" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::AuthorityDenied)
            )),
            "authority-receipt-mismatch" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::AuthorityReceiptMismatch)
            )),
            "membership-denied" => assert!(matches!(
                outcome,
                AdmissionOutcome::Refused(AdmissionRefusal::MembershipDenied)
            )),
            _ => unreachable!(),
        }
        assert!(runtime.journal().records().is_empty(), "case {label}");
        assert!(runtime.execution().log().is_empty(), "case {label}");
        assert!(runtime.validated_records().is_empty(), "case {label}");
    }
}

fn accepted_semantic_trace_is_not_exposed_when_append_refuses() {
    let request = request("base", b"append-refusal-valid-signature");
    let (mut runtime, harness) =
        runtime_with_record_bound("append-refusal", Modes::ACCEPT, false, 7, 1);
    assert!(matches!(
        runtime.admit(MAX_BYTES, &request),
        AdmissionOutcome::StorageRefused(_)
    ));
    assert_eq!(harness.verifier_calls.get(), 1);
    assert_eq!(harness.authority_calls.get(), 1);
    assert_eq!(harness.membership_calls.get(), 1);
    assert!(runtime.journal().records().is_empty());
    assert!(runtime.execution().log().is_empty());
    assert!(runtime.validated_records().is_empty());
}

fn live_zero_id_grant_cannot_turn_the_null_citation_into_a_trace() {
    let request = request("cite0", b"zero-citation-valid-signature");
    let (mut runtime, harness) = runtime("cite-zero", Modes::ACCEPT, false, 0);
    assert_eq!(
        runtime
            .execution()
            .log()
            .grants()
            .copied()
            .collect::<Vec<_>>(),
        vec![Grant::universal(0)]
    );
    assert!(matches!(
        runtime.admit(MAX_BYTES, &request),
        AdmissionOutcome::Refused(AdmissionRefusal::AuthorityDenied)
    ));
    assert_eq!(harness.verifier_calls.get(), 1);
    assert_eq!(harness.authority_calls.get(), 0);
    assert_eq!(harness.membership_calls.get(), 0);
    assert!(runtime.journal().records().is_empty());
    assert!(runtime.execution().log().is_empty());
    assert!(runtime.validated_records().is_empty());
}

fn assert_trace_refused(label: &str, certificate: Vec<u8>) {
    assert_eq!(
        check_runtime_auth_v4_admission_trace(&certificate),
        Err(RuntimeAuthV4AdmissionTraceRefusal::Refused),
        "mutation lane {label}"
    );
}

fn unique_offset(haystack: &[u8], needle: &[u8], label: &str) -> usize {
    assert!(!needle.is_empty(), "{label} needle is empty");
    let offsets: Vec<_> = haystack
        .windows(needle.len())
        .enumerate()
        .filter_map(|(at, window)| (window == needle).then_some(at))
        .collect();
    assert_eq!(offsets.len(), 1, "{label} is not unique in certificate");
    offsets[0]
}

fn trace_wire_truncation_and_trailing_bytes_fail_closed() {
    let request = request("base", b"mutation-valid-signature");
    let (mut runtime, _harness) = runtime("trace-wire-mutations", Modes::ACCEPT, false, 7);
    let receipt = accepted(runtime.admit(MAX_BYTES, &request));
    let AdmissionCertificate::Fresh { trace, .. } = receipt.certificate else {
        panic!("fresh admission lacked a fresh certificate")
    };
    let bytes = trace.certificate_bytes();
    assert!(bytes.len() > 1);
    assert_eq!(
        check_runtime_auth_v4_admission_trace(&[]),
        Err(RuntimeAuthV4AdmissionTraceRefusal::Refused)
    );
    for cut in 1..bytes.len() {
        assert_eq!(
            check_runtime_auth_v4_admission_trace(&bytes[..cut]),
            Err(RuntimeAuthV4AdmissionTraceRefusal::Refused),
            "strict truncation at {cut}"
        );
    }
    let mut trailing = bytes.to_vec();
    trailing.push(0);
    assert_eq!(
        check_runtime_auth_v4_admission_trace(&trailing),
        Err(RuntimeAuthV4AdmissionTraceRefusal::Refused)
    );
    assert_eq!(
        check_runtime_auth_v4_admission_trace(&vec![0; MAX_ADMISSION_TRACE_BYTES + 1]),
        Err(RuntimeAuthV4AdmissionTraceRefusal::TooLarge)
    );
}

fn signed_stage_and_replay_evidence_mutations_are_rejected_by_lean() {
    let request = request("base", b"semantic-mutation-valid-signature");
    let (mut runtime, _harness) = runtime("trace-semantic-mutations", Modes::ACCEPT, false, 7);
    let receipt = accepted(runtime.admit(MAX_BYTES, &request));
    let AdmissionCertificate::Fresh { trace, .. } = receipt.certificate else {
        panic!("fresh admission lacked a fresh certificate")
    };
    let stored = runtime.journal().records()[0].admission();
    let fields = stored.trace();
    let certificate = trace.certificate_bytes();

    // The first certificate field after version is the exact kind-3 request.
    // Mutating it while retaining the exact kind-4 projection response must
    // fail the checker's reprojection equality.
    let request_length = u64::from_le_bytes(certificate[1..9].try_into().unwrap()) as usize;
    assert_eq!(
        &certificate[9..9 + request_length],
        stored.canonical_request()
    );
    let mut signed = certificate.to_vec();
    signed[9 + request_length - 1] ^= 1;
    assert_trace_refused("signed-request/projection", signed);

    let projection_at = unique_offset(
        certificate,
        fields.projection_response(),
        "projection response",
    );
    let mut projection = certificate.to_vec();
    projection[projection_at + fields.projection_response().len() - 1] ^= 1;
    assert_trace_refused("projection response", projection);

    let observation = stored.observation();
    let execution_nodes: Vec<u8> = observation
        .execution_nodes()
        .iter()
        .flat_map(|node| node.iter().copied())
        .collect();
    let execution_nodes_at = unique_offset(certificate, &execution_nodes, "execution node vector");
    let child_index = usize::try_from(observation.child_index).unwrap();
    assert_eq!(
        observation.execution_nodes()[child_index],
        observation.resolved_move.child
    );
    let mut execution_node_binding = certificate.to_vec();
    execution_node_binding[execution_nodes_at + child_index * 32] ^= 1;
    assert_trace_refused("execution node/index binding", execution_node_binding);

    let request_at = unique_offset(certificate, fields.format_v3_request(), "FORMAT-v3 request");
    let mut replay_request = certificate.to_vec();
    let replay_word = |index: usize| {
        u64::from_le_bytes(
            fields.format_v3_request()[index * 8..index * 8 + 8]
                .try_into()
                .unwrap(),
        )
    };
    let node_count = replay_word(1) as usize;
    let selected_op_word = 5 + node_count + fields.selected_request_slot() as usize * 5;
    replay_request[request_at + (selected_op_word + 4) * 8] ^= 1;
    assert_trace_refused("FORMAT-v3 selected cite", replay_request);

    let response_at = unique_offset(
        certificate,
        fields.format_v3_response(),
        "FORMAT-v3 response",
    );
    let mut replay_response = certificate.to_vec();
    replay_response[response_at] ^= 1;
    assert_trace_refused("FORMAT-v3 replay response", replay_response);

    // Five nodes and one request slot means the final response word is the
    // exact selected operation status. Toggle only that status word.
    assert_eq!(fields.format_v3_response().len(), 6 * 8);
    let mut selected_status = certificate.to_vec();
    selected_status[response_at + fields.format_v3_response().len() - 8] ^= 1;
    assert_trace_refused("selected replay status", selected_status);

    // The slot word and `operation_was_new` byte immediately follow the
    // length-framed raw response.
    let selected_slot_at = response_at + fields.format_v3_response().len();
    assert_eq!(
        u64::from_le_bytes(
            certificate[selected_slot_at..selected_slot_at + 8]
                .try_into()
                .unwrap()
        ),
        fields.selected_request_slot()
    );
    let mut selected_slot = certificate.to_vec();
    selected_slot[selected_slot_at] ^= 1;
    assert_trace_refused("selected request slot", selected_slot);

    let operation_was_new_at = selected_slot_at + 8;
    assert_eq!(certificate[operation_was_new_at], 1);
    let mut operation_was_new = certificate.to_vec();
    operation_was_new[operation_was_new_at] = 2;
    assert_trace_refused("noncanonical operation-was-new", operation_was_new);

    // The five exact one-byte receipts are the final canonical fields. Each
    // host lane is independently load-bearing.
    let receipts = fields.stage_receipts();
    assert!(receipts.verification());
    assert!(receipts.context());
    assert!(receipts.resolution());
    assert!(receipts.authority());
    assert!(receipts.membership());
    for (offset, label) in [
        (4, "verification receipt"),
        (3, "context receipt"),
        (2, "resolution receipt"),
        (1, "authority receipt"),
        (0, "membership receipt"),
    ] {
        let mut receipt = certificate.to_vec();
        let at = receipt.len() - 1 - offset;
        assert_eq!(receipt[at], 1, "canonical {label}");
        receipt[at] = 0;
        assert_trace_refused(label, receipt);
    }
}

fn recovery_rejects_rebuilt_provider_trace_that_no_longer_matches_record() {
    let request = request("base", b"recovery-binding-signature");
    let (mut runtime, harness) = runtime("recovery-binding", Modes::ACCEPT, false, 7);
    accepted(runtime.admit(MAX_BYTES, &request));
    let expectation = runtime.journal().recovery_expectation();
    drop(runtime);
    let journal = AuthenticatedMoveJournal::open_pinned(&harness.path.0, options(), expectation)
        .expect("reopen pinned record before adversarial recovery");
    let (execution, mut substrate) = execution(false, 7);
    substrate.holders = GrantHolderBindings::new();
    let result = AuthenticatedRuntime::recover(
        MAX_BYTES,
        RuntimeScope {
            document: DOCUMENT.to_vec(),
            genesis: GENESIS.to_vec(),
            context_commitment: CONTEXT.to_vec(),
            execution_binding: execution.base_binding(),
        },
        TestVerifier {
            mode: ReceiptMode::Accept,
            calls: Rc::new(Cell::new(0)),
        },
        TestContexts {
            mode: ContextMode::Accept,
            substrate,
        },
        TestResolver {
            mode: ReceiptMode::Accept,
        },
        TestAuthority {
            mode: ReceiptMode::Accept,
            calls: Rc::new(Cell::new(0)),
        },
        TestMembership {
            mode: ReceiptMode::Accept,
            calls: Rc::new(Cell::new(0)),
        },
        execution,
        journal,
    );
    assert!(matches!(
        result,
        Err(RuntimeRecoveryError::Refused {
            sequence: 0,
            reason: AdmissionRefusal::AuthorityDenied,
        })
    ));
}

#[test]
fn debt_closure_u_0052() {
    fresh_applied_exact_retry_and_pinned_recovery_keep_distinct_evidence();
    fresh_cycle_skip_is_a_lean_validated_positive_trace();
    distinct_signed_identity_can_certify_an_idempotent_resolved_move();
    every_host_stage_refusal_prevents_trace_append_and_commit();
    accepted_semantic_trace_is_not_exposed_when_append_refuses();
    live_zero_id_grant_cannot_turn_the_null_citation_into_a_trace();
    trace_wire_truncation_and_trailing_bytes_fail_closed();
    signed_stage_and_replay_evidence_mutations_are_rejected_by_lean();
    recovery_rejects_rebuilt_provider_trace_that_no_longer_matches_record();
}
