//! Shared harness for the checkpoint-preflight tests.
//!
//! Every request comes from the Lean corpus emitter, and every provider accepts
//! exactly what the fixture's pinned context allows, so the only moving part
//! under test is the execution preflight and its journal records.

#![allow(dead_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::auth_runtime::{
    AdmissionContextProvider, AdmissionDisposition, AdmissionOutcome, AdmissionRefusal,
    AuthenticatedRuntime, ContextGrantHolderAuthority, ContextRefusal, ExecutionRefusal,
    GrantHolderBindings, GrantHolderContext, LeanMoveExecution, MembershipRefusal, MoveMembership,
    PinnedAdmissionContext, ResolvedNode, ResolverRefusal, RuntimeScope, StableIdResolver,
};
use uwueave::auth_verifier::{
    RequestVerifier, VerificationAcceptance, VerificationInput, VerificationRefusal,
};
use uwueave::persistence::{
    AuthenticatedMoveJournal, JournalOptions, KernelAdmissionObservation, RecoveryExpectation,
    SyncPolicy, TornTailPolicy,
};
use uwueave::{CausalWeave, Grant, MoveLog, MoveOp, NodeId, OpOutcome};

pub const MAX_BYTES: usize = 1 << 20;
pub const ISSUER: u64 = 17;
pub const LIVE_GRANT: u64 = 1;
pub const DELEGATED_GRANT: u64 = 2;
pub const REVOKED_GRANT: u64 = 3;
pub const NODES: usize = 16;
/// The delegated grant covers only node indices below this ceiling.
pub const DELEGATED_SCOPE: u64 = 8;

const DOCUMENT: &[u8] = &[1, 2];
const GENESIS: &[u8] = &[3, 4];
const CONTEXT: &[u8] = &[30, 31];

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

/// One move chosen by a test. Lean turns it into a signed canonical request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Row {
    pub lamport: u64,
    pub child: usize,
    pub dest: Option<usize>,
    pub cite: u64,
}

pub struct TempJournal(pub PathBuf);

impl TempJournal {
    pub fn new(label: &str) -> Self {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-incremental-{label}-{}-{nonce}.journal",
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

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("rust crate is directly below repository root")
        .to_path_buf()
}

/// Ask Lean for one canonical signed kind-3 request per row.
pub fn signed_requests(rows: &[Row]) -> Vec<Vec<u8>> {
    let spec = TempJournal::new("corpus-spec");
    let mut text = String::new();
    for row in rows {
        let dest = row.dest.map_or("-".to_string(), |dest| dest.to_string());
        text.push_str(&format!(
            "{} {} {} {}\n",
            row.lamport, row.child, dest, row.cite
        ));
    }
    fs::write(&spec.0, text).expect("write corpus spec");
    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "rust/tests/support/IncrementalPreflightCorpus.lean",
        ])
        .arg(&spec.0)
        .current_dir(repo())
        .output()
        .expect("launch Lean corpus emitter");
    assert!(
        output.status.success(),
        "corpus emitter failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut requests = Vec::with_capacity(rows.len());
    let mut rest = output.stdout.as_slice();
    while !rest.is_empty() {
        let (length, tail) = rest.split_at(8);
        let length = u64::from_le_bytes(length.try_into().unwrap()) as usize;
        let (request, tail) = tail.split_at(length);
        requests.push(request.to_vec());
        rest = tail;
    }
    assert_eq!(requests.len(), rows.len(), "one request per corpus row");
    requests
}

/// `count` moves in strictly increasing replay order whose Lamport clock
/// advances once per 120 moves. The signed UWV4 wire encodes numbers in unary,
/// so this isolates checkpointing from the request's own Lamport-sized bytes.
pub fn bounded_clock_rows(count: usize) -> Vec<Row> {
    (0..count)
        .map(|position| {
            let phase = position % 120;
            Row {
                lamport: 1 + (position / 120) as u64,
                child: 1 + phase / 8,
                dest: Some(phase % 8),
                cite: LIVE_GRANT,
            }
        })
        .collect()
}

/// `count` moves from one writer, in strictly increasing timestamp order, so
/// the Lamport clock equals the log length.
pub fn in_order_rows(count: usize) -> Vec<Row> {
    (0..count)
        .map(|position| {
            let child = 1 + position % (NODES - 1);
            Row {
                lamport: position as u64 + 1,
                child,
                dest: (position % 5 != 0).then_some((child - 1) / 2),
                cite: LIVE_GRANT,
            }
        })
        .collect()
}

/// A reproducible hostile schedule: in-order runs mixed with late arrivals,
/// re-signed duplicates of earlier moves, revoked citations, and scope misses.
pub fn adversarial_rows(count: usize, seed: u64) -> Vec<Row> {
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    let mut next = move |bound: u64| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state % bound
    };
    let mut clock = 1_000u64;
    let mut rows: Vec<Row> = Vec::with_capacity(count);
    for _ in 0..count {
        let choice = next(20);
        let child = next(NODES as u64) as usize;
        let dest = next(NODES as u64 + 1) as usize;
        let dest = (dest < NODES).then_some(dest);
        let row = match choice {
            0 | 1 if !rows.is_empty() => rows[next(rows.len() as u64) as usize],
            2..=4 => Row {
                lamport: clock.saturating_sub(1 + next(300)),
                child,
                dest,
                cite: LIVE_GRANT,
            },
            5 | 6 => {
                clock += 1;
                Row {
                    lamport: clock,
                    child,
                    dest,
                    cite: REVOKED_GRANT,
                }
            }
            7 | 8 => {
                clock += 1;
                Row {
                    lamport: clock,
                    child,
                    dest,
                    cite: DELEGATED_GRANT,
                }
            }
            _ => {
                clock += 1;
                Row {
                    lamport: clock,
                    child,
                    dest,
                    cite: LIVE_GRANT,
                }
            }
        };
        rows.push(row);
    }
    rows
}

pub fn weave() -> CausalWeave<Vec<u8>> {
    let mut weave = CausalWeave::new();
    let root = weave
        .insert(vec![], b"incremental-root".to_vec())
        .expect("insert root");
    let mut inserted = vec![root];
    for label in 1..NODES {
        let parent = inserted[(label - 1) / 2];
        inserted.push(
            weave
                .insert(vec![parent], vec![label as u8])
                .expect("insert node"),
        );
    }
    weave
}

pub fn authority_log() -> MoveLog {
    let mut log = MoveLog::new();
    log.issue(Grant::universal(LIVE_GRANT));
    log.issue(Grant::delegate(
        DELEGATED_GRANT,
        LIVE_GRANT,
        DELEGATED_SCOPE,
    ));
    log.issue(Grant::universal(REVOKED_GRANT));
    log.revoke(REVOKED_GRANT);
    log
}

pub fn node_ids(weave: &CausalWeave<Vec<u8>>) -> Vec<NodeId> {
    weave.nodes().map(|node| node.id()).collect()
}

pub fn move_op(nodes: &[NodeId], row: Row) -> MoveOp {
    MoveOp {
        lamport: row.lamport,
        replica: ISSUER,
        child: nodes[row.child],
        dest: row.dest.map(|dest| nodes[dest]),
        cite: row.cite,
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Substrate {
    nodes: Vec<NodeId>,
    binding: [u8; 32],
    holders: GrantHolderBindings,
}

impl GrantHolderContext for Substrate {
    fn holds_grant(&self, issuer: u64, cite: u64) -> bool {
        self.holders.holds(issuer, cite)
    }
}

#[derive(Clone)]
pub struct Contexts(pub Substrate);

impl AdmissionContextProvider for Contexts {
    type Context = Substrate;

    fn pin(
        &self,
        commitment: &[u8],
        document: &[u8],
        genesis: &[u8],
    ) -> Result<PinnedAdmissionContext<Substrate>, ContextRefusal> {
        Ok(PinnedAdmissionContext {
            commitment: commitment.to_vec(),
            document: document.to_vec(),
            genesis: genesis.to_vec(),
            execution_binding: self.0.binding,
            resolver_policy: 11,
            authority_policy: 12,
            membership_policy: 13,
            substrate: self.0.clone(),
        })
    }
}

#[derive(Clone, Copy)]
pub struct Resolver;

impl StableIdResolver<Substrate> for Resolver {
    fn resolve(
        &self,
        context: &PinnedAdmissionContext<Substrate>,
        stable_id: &[u8],
    ) -> Result<ResolvedNode, ResolverRefusal> {
        let [100, index] = stable_id else {
            return Err(ResolverRefusal::Missing);
        };
        let node_id = *context
            .substrate
            .nodes
            .get(usize::from(*index))
            .ok_or(ResolverRefusal::Missing)?;
        Ok(ResolvedNode {
            node_id,
            kernel_index: u64::from(*index),
        })
    }
}

#[derive(Clone, Copy)]
pub struct Membership;

impl MoveMembership<Substrate> for Membership {
    fn allows_move(
        &self,
        _context: &PinnedAdmissionContext<Substrate>,
        _issuer: u64,
        _operation: &MoveOp,
    ) -> Result<(), MembershipRefusal> {
        Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct Verifier;

impl RequestVerifier for Verifier {
    fn verify(
        &self,
        input: VerificationInput<'_>,
    ) -> Result<VerificationAcceptance, VerificationRefusal> {
        Ok(VerificationAcceptance::from_verifier_acceptance(input))
    }
}

pub type Runtime = AuthenticatedRuntime<
    Verifier,
    Contexts,
    Resolver,
    ContextGrantHolderAuthority,
    Membership,
    Vec<u8>,
>;

pub fn journal_options(torn_tail: TornTailPolicy) -> JournalOptions {
    JournalOptions {
        torn_tail,
        sync: SyncPolicy::Buffered,
        max_record_bytes: 1 << 26,
    }
}

/// A fresh execution over the fixture weave and its pinned context substrate.
pub fn execution() -> (LeanMoveExecution<Vec<u8>>, Substrate) {
    let weave = weave();
    let nodes = node_ids(&weave);
    let mut holders = GrantHolderBindings::new();
    for grant in [LIVE_GRANT, DELEGATED_GRANT, REVOKED_GRANT] {
        holders.bind(ISSUER, grant).expect("bind holder");
    }
    let execution = LeanMoveExecution::new(authority_log(), weave);
    let substrate = Substrate {
        nodes,
        binding: execution.base_binding(),
        holders,
    };
    (execution, substrate)
}

pub fn scope(binding: [u8; 32]) -> RuntimeScope {
    RuntimeScope {
        document: DOCUMENT.to_vec(),
        genesis: GENESIS.to_vec(),
        context_commitment: CONTEXT.to_vec(),
        execution_binding: binding,
    }
}

pub fn new_runtime(path: &Path) -> Runtime {
    let journal = AuthenticatedMoveJournal::open_pinned(
        path,
        journal_options(TornTailPolicy::Refuse),
        RecoveryExpectation::EMPTY,
    )
    .expect("open empty journal");
    let (execution, substrate) = execution();
    let binding = execution.base_binding();
    AuthenticatedRuntime::new(
        scope(binding),
        Verifier,
        Contexts(substrate),
        Resolver,
        ContextGrantHolderAuthority,
        Membership,
        execution,
        journal,
    )
    .unwrap_or_else(|error| panic!("construct runtime: {error:?}"))
}

/// Reopen a journal against its external pin and revalidate every record.
pub fn recover_runtime(
    path: &Path,
    expectation: RecoveryExpectation,
    torn_tail: TornTailPolicy,
) -> Runtime {
    let journal =
        AuthenticatedMoveJournal::open_pinned(path, journal_options(torn_tail), expectation)
            .expect("reopen pinned journal");
    let (execution, substrate) = execution();
    let binding = execution.base_binding();
    AuthenticatedRuntime::recover(
        MAX_BYTES,
        scope(binding),
        Verifier,
        Contexts(substrate),
        Resolver,
        ContextGrantHolderAuthority,
        Membership,
        execution,
        journal,
    )
    .unwrap_or_else(|error| panic!("recover runtime: {error:?}"))
}

/// Admit one request and require the runtime's verdict to equal a full replay
/// of the shadow log from genesis.
pub fn admit_against_full_replay(
    runtime: &mut Runtime,
    shadow: &mut MoveLog,
    weave: &CausalWeave<Vec<u8>>,
    operation: MoveOp,
    request: &[u8],
    label: &str,
) {
    let full = shadow.prospective_replay_certified(weave, operation);
    let expected = full
        .selected_status()
        .expect("fixture moves are resolvable");
    match (runtime.admit(MAX_BYTES, request), expected) {
        (AdmissionOutcome::Accepted(receipt), OpOutcome::Applied) => {
            assert_eq!(
                receipt.disposition,
                AdmissionDisposition::Appended,
                "{label}"
            );
            assert_eq!(
                receipt.kernel_observation,
                KernelAdmissionObservation::Applied,
                "{label}"
            );
            shadow.record(operation);
        }
        (AdmissionOutcome::Accepted(receipt), OpOutcome::SkippedCycle) => {
            assert_eq!(
                receipt.disposition,
                AdmissionDisposition::Appended,
                "{label}"
            );
            assert_eq!(
                receipt.kernel_observation,
                KernelAdmissionObservation::SkippedCycle,
                "{label}"
            );
            shadow.record(operation);
        }
        (
            AdmissionOutcome::Refused(AdmissionRefusal::Execution(
                ExecutionRefusal::SkippedUnauthorised,
            )),
            OpOutcome::SkippedUnauthorised,
        ) => {}
        (outcome, expected) => {
            panic!("{label}: runtime answered {outcome:?}, full replay says {expected:?}")
        }
    }
}
