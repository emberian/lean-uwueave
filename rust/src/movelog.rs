//! Node moving as a derived view over a grow-only operation log — with the
//! replay semantics **authored in Lean and called through FFI**, not
//! re-implemented here.
//!
//! `Uwueave/Move.lean` in one paragraph: reparenting cannot be a direct
//! CRDT mutation (`acyclicity_not_iconfluent`), so **replicate the monotone
//! thing** — the set of move operations ever issued, a trivial grow-only set —
//! **and derive the invariant-bearing thing**: replay the ops in total
//! timestamp order, skipping any op whose application would close a cycle.
//! `derived_view_sec` gives order-independence, redelivery-immunity and
//! by-construction acyclicity; `view_not_stable` is the priced anomaly, which
//! this module's docs and tests keep in view rather than hiding: **an older
//! remote op can retroactively skip a move you already saw applied.**
//!
//! What this Rust file actually does is deliberately dumb: it keeps the op
//! set (a `BTreeSet` — union merge), maps content-address ids to dense
//! indices, assembles typed parent/op/grant records, and asks Lean's exported
//! `encodeRequest` adapter to produce the canonical request bytes before
//! handing them to `uwueave_replay_kernel` (compiled to C by lake, linked by
//! `build.rs`). Request layout, byte order, replay order, and the cycle-skip
//! decision all live in Lean, in one place, next to their abstract model.
//!
//! **Wire format v3** (see `Exec.lean`'s contract header): the request now
//! carries an *authority substrate* — grants and revocations — and each op
//! cites the grant it exercises; the kernel filters unauthorised ops ahead of
//! its sort and reports them with a fourth status code. So this module keeps
//! three grow-only sets (ops, grants, revocations), all merged by union, and
//! sends all three. The gate itself — "is this grant active, and does its
//! scope cover the moved node" — is `Uwueave/Exec.lean`'s `permittedOp`,
//! proved in `Uwueave/Gated.lean` §5 to agree with the abstract model's gate.
//! No authorization decision is taken here.
//!
//! Request: magic, `n`, `m`, `ng`, `nr`, the parent block, `m × 5` op words
//! (lamport, replica, child, dest, cite), `ng × 3` grant words
//! (id, parent, scope), `nr` revocation words. Response: `n` override words
//! then `m` per-op status words in request order (0 = applied, 1 = skipped by
//! the cycle rule, 2 = skipped as invalid, 3 = skipped as **unauthorised**).
//! The request description is a decoder contract, not a Rust encoder: only
//! `Uwueave.Exec.encodeRequest` constructs those bytes.
//! [`MoveLog::replay`] keeps its classic view-only shape;
//! [`MoveLog::replay_traced`] surfaces the trace, which is `view_not_stable`
//! made observable — a UI can show *which* op an older remote edit
//! retroactively skipped, and *which* move an authority change removed. The
//! decode refuses (panics) on any response that is not exactly `n + m` words:
//! a length mismatch means the two sides disagree about the format — and a v2
//! request gets an empty response from a v3 kernel, so the flag day fires
//! here rather than being reinterpreted.
//!
//! ⚠ **Scope is a ceiling in the REQUEST's node-index space**, not over
//! content addresses: a grant of scope `σ` covers the ops whose child index
//! is `< σ`, and this crate's indexing is a function of the weave (dense,
//! ascending by [`NodeId`]). Two replicas therefore agree about coverage
//! exactly when their weaves agree — which is the same condition under which
//! they agree about anything else here — but a grant minted against one
//! replica's indexing does not mean the same thing against another's until
//! the weaves converge. [`Grant::universal`] is the honest "no attenuation"
//! grant for callers that do not want that coupling.

use crate::causal::{CausalWeave, NodeId};
use crate::ffi;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::ops::Bound;

/// Interval between retained historical snapshots and maximum replay batch.
pub(crate) const CHECKPOINT_INTERVAL: usize = 64;

/// Checkpoints retained for operations arriving out of timestamp order. An
/// operation older than every retained checkpoint rebuilds its preceding prefix.
pub(crate) const MAX_RETAINED_CHECKPOINTS: usize = 16;

/// A delegation grant — `Uwueave/Authority.lean`'s `(id, parent, scope)`
/// triple. `parent == 0` means "issued by the root authority"; `0` is never a
/// valid grant id (well-formedness forces `parent < id`), so it doubles as
/// the null citation an op that names no grant carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Grant {
    pub id: u64,
    pub parent: u64,
    pub scope: u64,
}

impl Grant {
    /// A root-issued grant of the given scope.
    pub fn root(id: u64, scope: u64) -> Self {
        Self {
            id,
            parent: 0,
            scope,
        }
    }

    /// A root-issued grant covering every node index — attenuation waived,
    /// and the only scope whose meaning does not depend on the replica's
    /// weave (see the module header's ⚠).
    pub fn universal(id: u64) -> Self {
        Self {
            id,
            parent: 0,
            scope: u64::MAX,
        }
    }

    /// Delegate under `parent`, narrowing to `scope`.
    pub fn delegate(id: u64, parent: u64, scope: u64) -> Self {
        Self { id, parent, scope }
    }
}

/// A reparenting operation. Total order =
/// `(lamport, replica, child, dest, cite)`, so replay order is deterministic
/// across replicas — the arbitration is the timestamp, exactly and only.
/// `cite` is the id of the grant whose authority this op exercises; `0`
/// cites nothing and is therefore never authorised.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MoveOp {
    pub lamport: u64,
    pub replica: u64,
    pub child: NodeId,
    /// `None` = move to root (clear the override).
    pub dest: Option<NodeId>,
    pub cite: u64,
}

/// The fate of one op in a replay: the kernel's v3 status block, decoded,
/// plus the one Rust-side case (an op this replica cannot yet encode).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpOutcome {
    /// The op set its child's override.
    Applied,
    /// Skipped by the kernel's cycle rule — the `view_not_stable` anomaly,
    /// attributed to the exact op it dropped.
    SkippedCycle,
    /// Refused by the kernel as malformed (child or destination index out of
    /// range). This encoder only produces in-range indices, so seeing this
    /// outcome indicates an encoder bug — it is decoded, not hidden.
    SkippedInvalid,
    /// Refused by the kernel's **gate**: the op's cited grant is not active
    /// (absent, revoked, revoked upstream, or off a chain that reaches the
    /// root) or its scope does not cover the moved node. This is the move
    /// authority removed, named — `Uwueave/Gated.lean`'s `gatedOps` decided
    /// inside the kernel.
    ///
    /// ⚠ It does not follow that the view lost a move: dropping an op can
    /// un-block one the cycle rule had been skipping
    /// (`Exec.applied_set_not_antitone`). What holds is that this op was not
    /// replayed, and that revoking more never un-refuses it
    /// (`Exec.gated_unauthorised_is_forever`).
    SkippedUnauthorised,
    /// Not sent to the kernel: the op names a node this replica has not seen
    /// yet. It re-enters the replay when its nodes arrive — the view is
    /// always a function of the current (log, weave) pair.
    OmittedUnknownNode,
}

/// A replay view together with the per-op trace (format v3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TracedReplay {
    /// The effective parent-override map — identical to [`MoveLog::replay`]'s
    /// return for the same (log, weave).
    pub view: BTreeMap<NodeId, Option<NodeId>>,
    /// Exactly one outcome per op in the log, in log (`BTreeSet`) order.
    pub outcomes: Vec<(MoveOp, OpOutcome)>,
}

/// One exact correspondence between a resolvable log operation and the slot
/// it occupied in the canonical FORMAT-v3 replay request.
///
/// The request slot is this value's index in
/// [`CertifiedReplay::request_slots`]. `log_index` names the operation's
/// position in [`MoveLog::ops`] at the time of replay. Keeping both sides of
/// that correspondence prevents a caller from reconstructing it by sorting
/// or filtering independently of the bytes Lean actually encoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplayRequestSlot {
    pub log_index: usize,
    pub operation: MoveOp,
}

/// A replay result plus the exact production evidence that produced it.
///
/// `canonical_request` is returned by Lean's canonical FORMAT-v3 encoder and
/// `raw_response` is returned verbatim by the Lean replay kernel. The request
/// slots and statuses are aligned: status `j` is the decoded status for
/// request slot `j`. All fields are private so the correspondence cannot be
/// mutated after construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedReplay {
    traced: TracedReplay,
    canonical_request: Vec<u8>,
    raw_response: Vec<u8>,
    request_slots: Vec<ReplayRequestSlot>,
    statuses: Vec<OpOutcome>,
}

impl CertifiedReplay {
    pub fn traced(&self) -> &TracedReplay {
        &self.traced
    }

    pub fn canonical_request(&self) -> &[u8] {
        &self.canonical_request
    }

    pub fn raw_response(&self) -> &[u8] {
        &self.raw_response
    }

    pub fn request_slots(&self) -> &[ReplayRequestSlot] {
        &self.request_slots
    }

    pub fn statuses(&self) -> &[OpOutcome] {
        &self.statuses
    }

    /// Locate an exact operation in the resolvable request. This returns the
    /// actual encoded request slot, not its position in the full log.
    pub fn request_slot(&self, operation: &MoveOp) -> Option<usize> {
        self.request_slots
            .binary_search_by_key(operation, |slot| slot.operation)
            .ok()
    }

    pub fn status(&self, request_slot: usize) -> Option<OpOutcome> {
        self.statuses.get(request_slot).copied()
    }

    pub fn into_traced(self) -> TracedReplay {
        self.traced
    }
}

/// Exact certified evidence for replaying a log after prospectively recording
/// one operation. This names whether the grow-only set insertion changed the
/// log and, independently, the operation's exact request slot when it was
/// resolvable against the current weave.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProspectiveCertifiedReplay {
    replay: CertifiedReplay,
    operation_was_new: bool,
    selected_request_slot: Option<usize>,
}

impl ProspectiveCertifiedReplay {
    pub fn replay(&self) -> &CertifiedReplay {
        &self.replay
    }

    pub fn operation_was_new(&self) -> bool {
        self.operation_was_new
    }

    pub fn selected_request_slot(&self) -> Option<usize> {
        self.selected_request_slot
    }

    pub fn selected_status(&self) -> Option<OpOutcome> {
        self.selected_request_slot
            .and_then(|slot| self.replay.status(slot))
    }

    pub fn into_replay(self) -> CertifiedReplay {
        self.replay
    }
}

/// The grow-only move log **and its authority substrate** — three grow-only
/// sets (ops, grants, revocations), merged by union, exactly
/// `Uwueave/Gated.lean`'s `GatedState` (whose `MergeState` instance is the
/// product's, `inferInstance`, no new merge proofs). Nothing is ever deleted:
/// a gated-out op stays on record, which is the receipt half of the design.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MoveLog {
    ops: BTreeSet<MoveOp>,
    grants: BTreeSet<Grant>,
    revocations: BTreeSet<u64>,
}

impl MoveLog {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record(&mut self, op: MoveOp) {
        self.ops.insert(op);
    }

    /// Add a grant to the substrate. Grow-only: issuing is coordination-free
    /// (`Authority.wf_iconfluent`), and nothing here checks that the issuer
    /// holds `parent` — that is a signature, and signatures are a premise
    /// (`Gated.lean`'s honest boundary), not something this crate enforces.
    pub fn issue(&mut self, grant: Grant) {
        self.grants.insert(grant);
    }

    /// Revoke a grant id. Grow-only and fail-closed: a revocation, once
    /// issued anywhere, reaches everywhere and never leaves, and it kills the
    /// whole delegation subtree under the named grant.
    pub fn revoke(&mut self, grant_id: u64) {
        self.revocations.insert(grant_id);
    }

    /// The CRDT join. Infallible: unions cannot conflict.
    pub fn merge(&mut self, other: &Self) {
        self.ops.extend(other.ops.iter().copied());
        self.grants.extend(other.grants.iter().copied());
        self.revocations.extend(other.revocations.iter().copied());
    }

    pub fn len(&self) -> usize {
        self.ops.len()
    }
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// The recorded move operations, in replay's deterministic set order.
    ///
    /// This enumerates the replicated receipt substrate without invoking the
    /// Lean replay kernel. Whether each operation applies is still decided by
    /// [`MoveLog::replay_traced`]; an operation returned here may be gated out,
    /// cycle-skipped, or name a node this replica has not received yet.
    pub fn ops(&self) -> impl Iterator<Item = &MoveOp> {
        self.ops.iter()
    }

    /// The grant substrate, in wire (ascending) order.
    pub fn grants(&self) -> impl Iterator<Item = &Grant> {
        self.grants.iter()
    }

    /// The revoked grant ids, in wire (ascending) order.
    pub fn revocations(&self) -> impl Iterator<Item = &u64> {
        self.revocations.iter()
    }

    /// Replay via the Lean kernel: the effective parent-override map, derived
    /// deterministically from (log, weave). Ops naming nodes this replica has
    /// not yet seen are omitted from the request (they re-enter the replay
    /// when their nodes arrive — the view is always a function of the current
    /// (log, weave) pair).
    pub fn replay<T: AsRef<[u8]> + Clone + PartialEq>(
        &self,
        weave: &CausalWeave<T>,
    ) -> BTreeMap<NodeId, Option<NodeId>> {
        self.replay_traced(weave).view
    }

    /// [`MoveLog::replay`], plus the kernel's v3 per-op trace: exactly one
    /// [`OpOutcome`] for every op in the log. This is `view_not_stable` made
    /// operational — after an older remote op syncs in, the move it
    /// retroactively un-happened shows up here as [`OpOutcome::SkippedCycle`]
    /// — and authority made operational: a move the gate removed shows up as
    /// [`OpOutcome::SkippedUnauthorised`], distinctly, so a UI can say which
    /// of the two happened.
    pub fn replay_traced<T: AsRef<[u8]> + Clone + PartialEq>(
        &self,
        weave: &CausalWeave<T>,
    ) -> TracedReplay {
        self.replay_certified(weave).into_traced()
    }

    /// Replay through the same Lean-authored path as [`MoveLog::replay_traced`]
    /// while retaining the exact canonical request bytes, raw response bytes,
    /// request-slot mapping, and decoded request statuses.
    pub fn replay_certified<T: AsRef<[u8]> + Clone + PartialEq>(
        &self,
        weave: &CausalWeave<T>,
    ) -> CertifiedReplay {
        self.replay_sorted(weave, self.ops.iter())
    }

    fn replay_sorted<'a, T: AsRef<[u8]> + Clone + PartialEq>(
        &self,
        weave: &CausalWeave<T>,
        operations: impl Iterator<Item = &'a MoveOp>,
    ) -> CertifiedReplay {
        // Dense, deterministic indexing: BTreeMap iteration is sorted by id,
        // identical on every replica with the same weave.
        let ids: Vec<NodeId> = weave.nodes().map(|n| n.id()).collect();
        let index: BTreeMap<NodeId, u64> = ids
            .iter()
            .enumerate()
            .map(|(i, id)| (*id, i as u64))
            .collect();
        let n = ids.len();

        // Assemble the resolvable typed ops in log order, remembering which
        // log ops were sent: request slot j holds the j-th resolvable op, so
        // `request_slots[j]` maps that exact slot back to its log operation.
        // Lean, not this code, turns these values into FORMAT-v3 bytes.
        let mut request_slots: Vec<ReplayRequestSlot> = Vec::with_capacity(self.ops.len());
        let mut ops_encoded: Vec<ffi::ReplayOpInput> = Vec::with_capacity(self.ops.len());
        let mut outcomes = Vec::with_capacity(self.ops.len());
        for (li, op) in operations.enumerate() {
            outcomes.push((*op, OpOutcome::OmittedUnknownNode));
            let (child, dest) = match (
                index.get(&op.child),
                match op.dest {
                    None => Some(-1i64),
                    Some(d) => index.get(&d).map(|i| *i as i64),
                },
            ) {
                (Some(c), Some(d)) => (*c, d),
                _ => continue, // unseen node: omitted, reported below
            };
            request_slots.push(ReplayRequestSlot {
                log_index: li,
                operation: *op,
            });
            ops_encoded.push(ffi::ReplayOpInput {
                lamport: op.lamport,
                replica: op.replica,
                child,
                dest,
                cite: op.cite,
            });
        }
        let m = ops_encoded.len();
        let first_parent = grounded_first_parents(weave, &ids, &index);
        // BTreeSet order is a function of each authority set, so equal merged
        // substrates present the same typed values to Lean.
        let grants: Vec<ffi::ReplayGrantInput> = self
            .grants
            .iter()
            .map(|g| ffi::ReplayGrantInput {
                id: g.id,
                parent: g.parent,
                scope: g.scope,
            })
            .collect();
        let revocations: Vec<u64> = self.revocations.iter().copied().collect();

        // This is the only request-construction call. `encode_replay_request`
        // crosses a typed ABI; `Uwueave.Exec.encodeRequestKernel` then calls
        // the proved canonical encoder. Rust contains no FORMAT-v3 magic,
        // count, block-order, or endianness implementation.
        let bytes = ffi::encode_replay_request(&first_parent, &ops_encoded, &grants, &revocations);

        let out = ffi::replay_kernel(&bytes);

        // Format v3: exactly n override words then m status words. Anything
        // else means the two sides disagree about the wire format — refuse
        // rather than reinterpret. A kernel that does not speak v3 answers a
        // v3 request with garbage or (from `Exec.replay`'s magic guard, in the
        // other direction) nothing at all; either way this fires.
        assert_eq!(
            out.len(),
            8 * (n + m),
            "kernel response is not format v3 (expected n + m = {} words)",
            n + m
        );
        let (ov_bytes, st_bytes) = out.split_at(8 * n);

        let mut view = BTreeMap::new();
        for (i, chunk) in ov_bytes.chunks_exact(8).enumerate() {
            let v = i64::from_le_bytes(chunk.try_into().unwrap());
            match v {
                -2 => {}
                -1 => {
                    view.insert(ids[i], None);
                }
                d => {
                    view.insert(ids[i], Some(ids[d as usize]));
                }
            }
        }

        // Stitch the kernel's statuses (request order) back onto the log
        // (log order): ops we never sent are reported, not dropped.
        let statuses: Vec<OpOutcome> = st_bytes
            .chunks_exact(8)
            .map(|chunk| decode_status(i64::from_le_bytes(chunk.try_into().unwrap())))
            .collect();
        for (slot, &status) in request_slots.iter().zip(&statuses) {
            outcomes[slot.log_index].1 = status;
        }

        CertifiedReplay {
            traced: TracedReplay { view, outcomes },
            canonical_request: bytes,
            raw_response: out,
            request_slots,
            statuses,
        }
    }

    /// Produce exact replay evidence for the log that would result from
    /// recording `operation`, without mutating this log.
    ///
    /// A duplicate operation still selects its existing exact request slot
    /// while reporting `operation_was_new == false`. An operation naming an
    /// unseen node has no request slot or status.
    pub fn prospective_replay_certified<T: AsRef<[u8]> + Clone + PartialEq>(
        &self,
        weave: &CausalWeave<T>,
        operation: MoveOp,
    ) -> ProspectiveCertifiedReplay {
        let operation_was_new = !self.ops.contains(&operation);
        let operations = self
            .ops
            .range(..operation)
            .chain(std::iter::once(&operation))
            .chain(
                self.ops
                    .range((Bound::Excluded(operation), Bound::Unbounded)),
            );
        let replay = self.replay_sorted(weave, operations);
        let selected_request_slot = replay.request_slot(&operation);
        ProspectiveCertifiedReplay {
            replay,
            operation_was_new,
            selected_request_slot,
        }
    }
}

/// The structural first-parent block, indexed by the weave's dense node order.
fn grounded_first_parents<T: AsRef<[u8]> + Clone + PartialEq>(
    weave: &CausalWeave<T>,
    ids: &[NodeId],
    index: &BTreeMap<NodeId, u64>,
) -> Vec<i64> {
    let mut first_parent = Vec::with_capacity(ids.len());
    for id in ids {
        let node = weave
            .get(id)
            .expect("ids were just enumerated from this weave");
        let fp: i64 = match node.parents().first() {
            None => -1,
            Some(p) => {
                // ExecRefine's `GroundedBase` hypothesis, enforced where
                // Rust meets Lean: every acyclicity theorem about the
                // kernel (`absReplay_acyclic` and kin) assumes some rank
                // strictly descends along the encoded firstParent edges.
                // `CausalWeave` supplies exactly that rank (grounded by
                // construction at insert), so this can only fire on a
                // corrupted store or a refactor that breaks the
                // invariant — at which point the kernel's cycle verdicts
                // would be garbage (`Exec.lean` header's footgun), and
                // refusing loudly here is the theorem's precondition
                // speaking. Cost: one integer compare per node.
                let parent = weave
                    .get(p)
                    .expect("weave is causally closed: parents are present");
                assert!(
                    parent.rank() < node.rank(),
                    "non-grounded base: rank does not descend along firstParent \
                     ({} -> {}); the kernel's acyclicity theorem does not cover \
                     this input (GroundedBase, Uwueave/ExecRefine.lean)",
                    node.rank(),
                    parent.rank(),
                );
                *index.get(p).expect("parents are present, hence indexed") as i64
            }
        };
        first_parent.push(fp);
    }
    first_parent
}

fn decode_status(word: i64) -> OpOutcome {
    match word {
        0 => OpOutcome::Applied,
        1 => OpOutcome::SkippedCycle,
        2 => OpOutcome::SkippedInvalid,
        3 => OpOutcome::SkippedUnauthorised,
        v => panic!("unknown status word {v} — kernel speaks a newer format"),
    }
}

/// One operation in the kernel's carrier. Lexicographic tuple order is exactly
/// `Uwueave.Exec.opLt`: `(lamport, replica, child, dest, cite)`, with `-1` as
/// the move-to-root destination.
type KernelKey = (u64, u64, u64, i64, u64);

fn kernel_input(key: KernelKey) -> ffi::ReplayOpInput {
    ffi::ReplayOpInput {
        lamport: key.0,
        replica: key.1,
        child: key.2,
        dest: key.3,
        cite: key.4,
    }
}

/// `CheckpointedLogState` from `Uwueave/IncrementalCheckpointPreflight.lean`:
/// the effective-parent view after every operation at or below `clock`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReplayCheckpoint {
    clock: KernelKey,
    summarized: usize,
    base: Vec<i64>,
}

/// Exact kernel evidence for one bounded preflight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BoundedPreflight {
    pub(crate) canonical_request: Vec<u8>,
    pub(crate) raw_response: Vec<u8>,
    pub(crate) selected_request_slot: usize,
    pub(crate) checkpoint: ReplayCheckpoint,
    pub(crate) selected_status: OpOutcome,
    pub(crate) operation_was_new: bool,
}

/// Live node index and replay checkpoints for one fixed weave and authority
/// substrate.
///
/// A preflight is a pure read: it asks the unchanged Lean kernel to replay the
/// operations after the newest checkpoint strictly below the candidate, on a
/// first-parent block rebased to that checkpoint. A refused candidate therefore
/// leaves nothing to roll back. `checkpoint_suffix_preflight_eq_full_replay`
/// proves the verdict equals full replay whenever the suffix lies strictly
/// above the checkpoint's clock, which is the invariant [`Self::commit`] keeps
/// by discarding every checkpoint a late-arriving operation sorts beneath.
///
/// In-order replay takes one kernel step on the fixed node/authority base.
/// Ordered-set membership and insertion still cost O(log N). A late move may
/// rebuild every predecessor in bounded batches.
#[derive(Debug, Clone)]
pub(crate) struct IncrementalPreflight {
    ids: Vec<NodeId>,
    index: BTreeMap<NodeId, u64>,
    first_parent: Vec<i64>,
    grants: Vec<ffi::ReplayGrantInput>,
    revocations: Vec<u64>,
    ops: BTreeSet<KernelKey>,
    checkpoints: Vec<ReplayCheckpoint>,
    tip: Option<ReplayCheckpoint>,
}

impl IncrementalPreflight {
    pub(crate) fn new<T: AsRef<[u8]> + Clone + PartialEq>(
        log: &MoveLog,
        weave: &CausalWeave<T>,
    ) -> Self {
        let ids: Vec<NodeId> = weave.nodes().map(|node| node.id()).collect();
        let index: BTreeMap<NodeId, u64> = ids
            .iter()
            .enumerate()
            .map(|(position, id)| (*id, position as u64))
            .collect();
        let first_parent = grounded_first_parents(weave, &ids, &index);
        let grants = log
            .grants
            .iter()
            .map(|grant| ffi::ReplayGrantInput {
                id: grant.id,
                parent: grant.parent,
                scope: grant.scope,
            })
            .collect();
        let revocations = log.revocations.iter().copied().collect();
        let mut incremental = Self {
            ids,
            index,
            first_parent,
            grants,
            revocations,
            ops: BTreeSet::new(),
            checkpoints: Vec::new(),
            tip: None,
        };
        let keys = log
            .ops
            .iter()
            .filter_map(|operation| incremental.key(operation))
            .collect();
        incremental.ops = keys;
        incremental
    }

    /// The dense execution node order used by every request.
    pub(crate) fn execution_nodes(&self) -> &[NodeId] {
        &self.ids
    }

    pub(crate) fn node_index(&self, node: &NodeId) -> Option<u64> {
        self.index.get(node).copied()
    }

    fn key(&self, operation: &MoveOp) -> Option<KernelKey> {
        let child = *self.index.get(&operation.child)?;
        let dest = match operation.dest {
            None => -1,
            Some(node) => *self.index.get(&node)? as i64,
        };
        Some((
            operation.lamport,
            operation.replica,
            child,
            dest,
            operation.cite,
        ))
    }

    /// Last valid snapshot strictly before the selected operation.
    fn start_for(&self, key: KernelKey) -> Option<&ReplayCheckpoint> {
        if let Some(tip) = self.tip.as_ref().filter(|tip| tip.clock < key) {
            return Some(tip);
        }
        let end = self.checkpoints.partition_point(|cp| cp.clock < key);
        self.checkpoints[..end].last()
    }

    fn replay_batch(&self, base: &[i64], ops: &[ffi::ReplayOpInput]) -> (Vec<u8>, Vec<u8>) {
        let request = ffi::encode_replay_request(base, ops, &self.grants, &self.revocations);
        let response = ffi::replay_kernel(&request);
        assert_eq!(
            response.len(),
            8 * (base.len() + ops.len()),
            "invalid FORMAT-v3 response"
        );
        (request, response)
    }

    fn apply_overrides(base: &mut [i64], response: &[u8]) {
        for (parent, word) in base.iter_mut().zip(response.chunks_exact(8)) {
            let value = i64::from_le_bytes(word.try_into().unwrap());
            if value != -2 {
                *parent = value;
            }
        }
    }

    /// The verdict at a sorted slot depends only on predecessors. Rebuild any
    /// missing prefix in bounded batches, then certify just the selected move
    /// on its exact effective-parent base. Thus checkpoint retention is a cache
    /// policy: evicting a snapshot never changes the certificate bytes.
    pub(crate) fn preflight(&self, operation: MoveOp) -> Option<BoundedPreflight> {
        let key = self.key(&operation)?;
        let start = self.start_for(key);
        let mut base = start.map_or(&self.first_parent, |cp| &cp.base).clone();
        let lower = start.map_or(Bound::Unbounded, |cp| Bound::Excluded(cp.clock));
        let mut summarized = start.map_or(0, |cp| cp.summarized);
        let mut predecessors = self.ops.range((lower, Bound::Excluded(key)));
        let mut batch = Vec::new();
        loop {
            batch.extend(
                predecessors
                    .by_ref()
                    .take(CHECKPOINT_INTERVAL)
                    .copied()
                    .map(kernel_input),
            );
            if batch.is_empty() {
                break;
            }
            let (_, response) = self.replay_batch(&base, &batch);
            Self::apply_overrides(&mut base, &response);
            summarized += batch.len();
            batch.clear();
        }
        let (canonical_request, raw_response) = self.replay_batch(&base, &[kernel_input(key)]);
        let at = 8 * base.len();
        let status = i64::from_le_bytes(raw_response[at..].try_into().unwrap());
        Self::apply_overrides(&mut base, &raw_response);
        Some(BoundedPreflight {
            canonical_request,
            raw_response,
            selected_request_slot: 0,
            selected_status: decode_status(status),
            operation_was_new: !self.ops.contains(&key),
            checkpoint: ReplayCheckpoint {
                clock: key,
                summarized: summarized + 1,
                base,
            },
        })
    }

    /// Install the kernel result only after durable append. A late insertion
    /// invalidates later snapshots. Later operations stay in the ordered set.
    pub(crate) fn commit(&mut self, checkpoint: ReplayCheckpoint) {
        if !self.ops.insert(checkpoint.clock) {
            return;
        }
        let end = self
            .checkpoints
            .partition_point(|cp| cp.clock < checkpoint.clock);
        self.checkpoints.truncate(end);
        let previous = self.checkpoints.last().map_or(0, |cp| cp.summarized);
        if checkpoint.summarized - previous >= CHECKPOINT_INTERVAL {
            if self.checkpoints.len() == MAX_RETAINED_CHECKPOINTS {
                self.checkpoints.remove(0);
            }
            self.checkpoints.push(checkpoint.clone());
        }
        self.tip = Some(checkpoint);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two root nodes, and a log whose substrate holds one root-issued grant
    /// (id 1) covering everything — the "no attenuation" setup every test
    /// that is not *about* the gate wants. Format v3 has no ungated path: an
    /// op citing no grant is refused, so a log with no grants replays nothing.
    fn two_nodes() -> (CausalWeave<Vec<u8>>, NodeId, NodeId, MoveLog) {
        let mut w = CausalWeave::new();
        let n0 = w.insert(vec![], b"n0".to_vec()).unwrap();
        let n1 = w.insert(vec![], b"n1".to_vec()).unwrap();
        let mut log = MoveLog::new();
        log.issue(Grant::universal(1));
        (w, n0, n1, log)
    }

    fn op(lamport: u64, replica: u64, child: NodeId, dest: Option<NodeId>) -> MoveOp {
        MoveOp {
            lamport,
            replica,
            child,
            dest,
            cite: 1,
        }
    }

    #[test]
    fn lean_encoder_produces_the_canonical_replay_request() {
        let ops = [ffi::ReplayOpInput {
            lamport: u64::MAX,
            replica: 9,
            child: 0,
            dest: 1,
            cite: 7,
        }];
        let grants = [ffi::ReplayGrantInput {
            id: 7,
            parent: 0,
            scope: u64::MAX,
        }];
        let bytes = ffi::encode_replay_request(&[-1, -1], &ops, &grants, &[]);

        assert!(
            ffi::request_canonical(&bytes),
            "the typed export must return `Exec.encodeRequest`'s canonical bytes"
        );
        let out = ffi::replay_kernel(&bytes);
        let words: Vec<i64> = out
            .chunks_exact(8)
            .map(|chunk| i64::from_le_bytes(chunk.try_into().unwrap()))
            .collect();
        assert_eq!(
            words,
            vec![1, -2, 0],
            "typed fields survive the ABI and reach replay"
        );
    }

    /// Scenario mirror of `Uwueave.Move.view_not_stable` — o₁ (t=2) moves
    /// n₀ under n₁; the *older* o₂ (t=1) moves n₁ under n₀. With o₁ alone the
    /// view shows the move; after o₂ arrives, replay applies o₂ first and
    /// skips o₁ as cycle-creating: the already-seen move is un-happened.
    /// (This test now exercises the Lean kernel end-to-end.)
    #[test]
    fn lean_witness_view_not_stable() {
        let (w, n0, n1, mut log) = two_nodes();
        let o1 = op(2, 0, n0, Some(n1));
        let o2 = op(1, 1, n1, Some(n0));

        log.record(o1);
        assert_eq!(log.replay(&w).get(&n0), Some(&Some(n1)), "o1 applied");

        log.record(o2); // older op arrives late
        let view = log.replay(&w);
        assert_eq!(view.get(&n1), Some(&Some(n0)), "o2 (older) wins");
        assert_eq!(view.get(&n0), None, "o1 retroactively skipped");
    }

    /// Delivery order and duplication don't matter (`derived_view_sec` (1),(2)).
    #[test]
    fn replay_order_independent() {
        let (w, n0, n1, log) = two_nodes();
        let o1 = op(2, 0, n0, Some(n1));
        let o2 = op(1, 1, n1, Some(n0));

        let mut a = log.clone();
        a.record(o1);
        a.record(o2);
        let mut b = log.clone();
        b.record(o2);
        b.record(o1);
        b.record(o1); // redelivery
        assert_eq!(a, b);
        assert_eq!(a.replay(&w), b.replay(&w));
    }

    /// The view is acyclic whatever the log holds (`miniInterp_acyclic`,
    /// exercised through the kernel on the mirror scenario).
    #[test]
    fn view_acyclic() {
        let (w, n0, n1, mut log) = two_nodes();
        log.record(op(2, 0, n0, Some(n1)));
        log.record(op(1, 1, n1, Some(n0)));
        let view = log.replay(&w);
        let p0 = view.get(&n0).copied().flatten();
        let p1 = view.get(&n1).copied().flatten();
        assert!(
            !(p0 == Some(n1) && p1 == Some(n0)),
            "no 2-cycle in the view"
        );
    }

    /// The v3 trace on the `view_not_stable` scenario: o₂ applied, o₁
    /// skipped-by-cycle — the Lean-side `absReplayFull_both_statuses`
    /// (`Move.lean` §3), observed through the real kernel.
    #[test]
    fn lean_witness_trace_shows_the_skip() {
        let (w, n0, n1, mut log) = two_nodes();
        let o1 = op(2, 0, n0, Some(n1));
        let o2 = op(1, 1, n1, Some(n0));
        log.record(o1);
        log.record(o2);
        let traced = log.replay_traced(&w);
        assert_eq!(traced.view, log.replay(&w), "traced view = plain view");
        let outcome = |op: &MoveOp| {
            traced
                .outcomes
                .iter()
                .find(|(o, _)| o == op)
                .map(|(_, s)| *s)
        };
        assert_eq!(
            outcome(&o1),
            Some(OpOutcome::SkippedCycle),
            "the skip is named"
        );
        assert_eq!(outcome(&o2), Some(OpOutcome::Applied));
    }

    #[test]
    fn certified_replay_retains_exact_kernel_evidence_and_slot_mapping() {
        let (w, n0, n1, mut log) = two_nodes();
        let later = op(2, 0, n0, Some(n1));
        let earlier = op(1, 1, n1, Some(n0));
        log.record(later);
        log.record(earlier);

        let certified = log.replay_certified(&w);
        assert!(
            ffi::request_canonical(certified.canonical_request()),
            "the retained request is exactly Lean's canonical encoding"
        );
        assert_eq!(
            certified.raw_response(),
            ffi::replay_kernel(certified.canonical_request()),
            "the retained response is the kernel's exact bytes"
        );
        assert_eq!(
            certified.request_slots(),
            [
                ReplayRequestSlot {
                    log_index: 0,
                    operation: earlier,
                },
                ReplayRequestSlot {
                    log_index: 1,
                    operation: later,
                },
            ]
        );
        assert_eq!(
            certified.statuses(),
            [OpOutcome::Applied, OpOutcome::SkippedCycle]
        );
        assert_eq!(certified.request_slot(&earlier), Some(0));
        assert_eq!(certified.request_slot(&later), Some(1));
        assert_eq!(certified.status(1), Some(OpOutcome::SkippedCycle));
        assert_eq!(certified.traced(), &log.replay_traced(&w));
    }

    #[test]
    fn prospective_certified_replay_distinguishes_new_and_duplicate_ops() {
        let (w, n0, n1, mut log) = two_nodes();
        let existing = op(1, 0, n0, Some(n1));
        log.record(existing);

        let duplicate = log.prospective_replay_certified(&w, existing);
        assert!(!duplicate.operation_was_new());
        assert_eq!(duplicate.selected_request_slot(), Some(0));
        assert_eq!(duplicate.selected_status(), Some(OpOutcome::Applied));
        assert_eq!(
            duplicate.replay().request_slots()[0].operation,
            existing,
            "a duplicate selects its already encoded exact slot"
        );

        let fresh = op(2, 0, n1, None);
        let inserted = log.prospective_replay_certified(&w, fresh);
        assert!(inserted.operation_was_new());
        let slot = inserted
            .selected_request_slot()
            .expect("a resolvable fresh operation has a request slot");
        assert_eq!(inserted.replay().request_slots()[slot].operation, fresh);
        assert_eq!(inserted.selected_status(), Some(OpOutcome::Applied));
        assert_eq!(log.len(), 1, "prospective replay does not mutate the log");
    }

    /// Move-to-root is an override too, distinct from "no override".
    #[test]
    fn move_to_root() {
        let (w, n0, n1, mut log) = two_nodes();
        log.record(op(1, 0, n0, Some(n1)));
        log.record(op(2, 0, n0, None));
        let view = log.replay(&w);
        assert_eq!(view.get(&n0), Some(&None), "explicitly at root");
    }

    /// **The gate, end to end.** An op citing a grant nobody issued is
    /// refused and *named* — `OpOutcome::SkippedUnauthorised`, not silently
    /// dropped and not confused with a cycle skip. Fail-closed is the default:
    /// no grant, no move.
    #[test]
    fn uncited_op_is_refused_and_named() {
        let (w, n0, n1, mut log) = two_nodes();
        let stranger = MoveOp {
            lamport: 1,
            replica: 0,
            child: n0,
            dest: Some(n1),
            cite: 7,
        };
        log.record(stranger);
        let traced = log.replay_traced(&w);
        assert_eq!(traced.outcomes.len(), 1);
        assert_eq!(traced.outcomes[0].1, OpOutcome::SkippedUnauthorised);
        assert!(traced.view.is_empty(), "an unauthorised op moves nothing");
    }

    /// **Revocation, end to end** — `Gated.story_fail_closed` through the
    /// real kernel: the move is in the view, a revocation of the grant it
    /// cites syncs in, and the move is gone from the view *and* named in the
    /// trace as the one authority removed.
    #[test]
    fn revocation_removes_the_move_and_says_so() {
        let (w, n0, n1, mut log) = two_nodes();
        let o = op(1, 0, n0, Some(n1));
        log.record(o);
        assert_eq!(
            log.replay(&w).get(&n0),
            Some(&Some(n1)),
            "authorised, applied"
        );

        log.revoke(1);
        let traced = log.replay_traced(&w);
        assert_eq!(traced.outcomes[0].1, OpOutcome::SkippedUnauthorised);
        assert_eq!(traced.view.get(&n0), None, "the move un-happened");
    }

    /// Revocation cascades down the delegation chain: grant 2 is delegated
    /// under grant 1, and revoking the ISSUER kills the delegate's move
    /// although id 2 sits in no revocation set — `Authority.demo_cascade_revoked`
    /// and `Gated.story_cascade`, decided inside the kernel.
    #[test]
    fn revoking_the_issuer_cascades() {
        let (w, n0, n1, mut log) = two_nodes();
        log.issue(Grant::delegate(2, 1, u64::MAX));
        let delegated = MoveOp {
            lamport: 1,
            replica: 0,
            child: n0,
            dest: Some(n1),
            cite: 2,
        };
        log.record(delegated);
        assert_eq!(
            log.replay(&w).get(&n0),
            Some(&Some(n1)),
            "delegate may move"
        );

        log.revoke(1); // the issuer, not the delegate
        let traced = log.replay_traced(&w);
        assert_eq!(traced.outcomes[0].1, OpOutcome::SkippedUnauthorised);
        assert_eq!(
            traced.view.get(&n0),
            None,
            "the whole subtree loses its moves"
        );
    }

    /// Attenuation bites: a grant of scope 1 covers node index 0 only, so a
    /// move of node index 1 citing it is refused while a move of node index 0
    /// stands. (Indices here are the weave's ascending-`NodeId` order — the
    /// module header's ⚠ about scope living in index space.)
    #[test]
    fn scope_ceiling_refuses_the_uncovered_node() {
        let mut w = CausalWeave::new();
        let a = w.insert(vec![], b"a".to_vec()).unwrap();
        let b = w.insert(vec![], b"b".to_vec()).unwrap();
        let (lo, hi) = if a < b { (a, b) } else { (b, a) };

        let mut log = MoveLog::new();
        log.issue(Grant::root(1, 1)); // covers index 0 only
        let covered = MoveOp {
            lamport: 1,
            replica: 0,
            child: lo,
            dest: None,
            cite: 1,
        };
        let uncovered = MoveOp {
            lamport: 2,
            replica: 0,
            child: hi,
            dest: None,
            cite: 1,
        };
        log.record(covered);
        log.record(uncovered);

        let traced = log.replay_traced(&w);
        let outcome = |op: &MoveOp| {
            traced
                .outcomes
                .iter()
                .find(|(o, _)| o == op)
                .map(|(_, s)| *s)
        };
        assert_eq!(outcome(&covered), Some(OpOutcome::Applied));
        assert_eq!(outcome(&uncovered), Some(OpOutcome::SkippedUnauthorised));
    }

    /// The substrate merges like everything else: unions of grants and
    /// revocations, and a peer's revocation reaches this replica's view.
    #[test]
    fn substrate_merges_by_union() {
        let (w, n0, n1, mut log) = two_nodes();
        log.record(op(1, 0, n0, Some(n1)));

        let mut peer = MoveLog::new();
        peer.revoke(1);
        log.merge(&peer);

        assert_eq!(log.grants().count(), 1);
        assert_eq!(log.revocations().copied().collect::<Vec<_>>(), vec![1]);
        assert_eq!(
            log.replay(&w).get(&n0),
            None,
            "the peer's revocation applies"
        );
    }

    /// A small deterministic generator, so a failure reproduces from its seed.
    struct Lfsr(u64);

    impl Lfsr {
        fn below(&mut self, bound: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % bound
        }
    }

    fn differential_weave() -> (CausalWeave<Vec<u8>>, Vec<NodeId>) {
        let mut weave = CausalWeave::new();
        let root = weave.insert(vec![], b"root".to_vec()).unwrap();
        let mut inserted = vec![root];
        for label in 0..11u8 {
            let parent = inserted[usize::from(label) / 2];
            inserted.push(weave.insert(vec![parent], vec![label]).unwrap());
        }
        let ids = weave.nodes().map(|node| node.id()).collect();
        (weave, ids)
    }

    fn differential_log() -> MoveLog {
        let mut log = MoveLog::new();
        log.issue(Grant::universal(1));
        log.issue(Grant::delegate(2, 1, 8));
        log.issue(Grant::universal(3));
        log.issue(Grant::delegate(4, 3, u64::MAX));
        log.revoke(3);
        log
    }

    /// Every bounded preflight must equal the full-history replay it replaces:
    /// the verdict, newness, and, after commit, the whole view. The schedule
    /// mixes in-order runs with late arrivals, redeliveries, cycles, scope
    /// refusals, and revoked citations across several checkpoint intervals.
    #[test]
    fn bounded_preflight_is_full_replay_on_adversarial_schedules() {
        let (weave, ids) = differential_weave();
        for seed in 1..=6u64 {
            let mut random = Lfsr(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut log = differential_log();
            let mut incremental = IncrementalPreflight::new(&log, &weave);
            let mut clock = 1_000u64;
            let mut history: Vec<MoveOp> = Vec::new();
            for step in 0..420 {
                let operation = match random.below(10) {
                    0 if !history.is_empty() => {
                        history[random.below(history.len() as u64) as usize]
                    }
                    1 | 2 => MoveOp {
                        lamport: clock.saturating_sub(1 + random.below(300)),
                        replica: random.below(3),
                        child: ids[random.below(ids.len() as u64) as usize],
                        dest: Some(ids[random.below(ids.len() as u64) as usize]),
                        cite: 1 + random.below(5),
                    },
                    _ => {
                        clock += 1;
                        let dest = random.below(ids.len() as u64 + 1) as usize;
                        MoveOp {
                            lamport: clock,
                            replica: random.below(3),
                            child: ids[random.below(ids.len() as u64) as usize],
                            dest: ids.get(dest).copied(),
                            cite: 1 + random.below(5),
                        }
                    }
                };
                let bounded = incremental.preflight(operation).expect("resolvable");
                let full = log.prospective_replay_certified(&weave, operation);
                assert_eq!(
                    Some(bounded.selected_status),
                    full.selected_status(),
                    "seed {seed} step {step}: verdict"
                );
                assert_eq!(
                    bounded.operation_was_new,
                    full.operation_was_new(),
                    "seed {seed} step {step}: newness"
                );
                assert_eq!(bounded.selected_request_slot, 0);
                if step % 3 == 0 {
                    // A refused candidate leaves no trace in either structure.
                    continue;
                }
                log.record(operation);
                incremental.commit(bounded.checkpoint);
                history.push(operation);
                assert_checkpoints_are_exact(&incremental, &log, &weave, seed, step);
            }
            assert!(
                incremental
                    .tip
                    .as_ref()
                    .is_some_and(|cp| cp.summarized >= CHECKPOINT_INTERVAL),
                "seed {seed}: the schedule must exercise real checkpoints"
            );
        }
    }

    fn response_words(bytes: &[u8]) -> Vec<i64> {
        bytes
            .chunks_exact(8)
            .map(|chunk| i64::from_le_bytes(chunk.try_into().unwrap()))
            .collect()
    }

    /// Each retained checkpoint must be byte-for-byte the override block of a
    /// genesis replay over exactly the operations at or below its clock.
    fn assert_checkpoints_are_exact(
        incremental: &IncrementalPreflight,
        log: &MoveLog,
        weave: &CausalWeave<Vec<u8>>,
        seed: u64,
        step: usize,
    ) {
        for checkpoint in incremental.checkpoints.iter().chain(&incremental.tip) {
            let mut prefix = MoveLog::new();
            log.grants().for_each(|grant| prefix.issue(*grant));
            log.revocations().for_each(|id| prefix.revoke(*id));
            for operation in log.ops() {
                if incremental.key(operation).expect("resolvable") <= checkpoint.clock {
                    prefix.record(*operation);
                }
            }
            assert_eq!(
                prefix.len(),
                checkpoint.summarized,
                "seed {seed} step {step}"
            );
            let replayed = prefix.replay_certified(weave);
            let words = response_words(&replayed.raw_response()[..8 * incremental.ids.len()]);
            let parents: Vec<_> = words
                .iter()
                .zip(&incremental.first_parent)
                .map(|(&word, &parent)| if word == -2 { parent } else { word })
                .collect();
            assert_eq!(parents, checkpoint.base, "seed {seed} step {step}");
        }
    }

    /// Dropping all derived state changes work, never durable evidence.
    #[test]
    fn eviction_preserves_certificate_bytes_for_late_moves() {
        let (weave, ids) = differential_weave();
        let mut log = differential_log();
        let mut incremental = IncrementalPreflight::new(&log, &weave);
        for lamport in 1..=1200 {
            let operation = MoveOp {
                lamport,
                replica: 0,
                child: ids[1],
                dest: None,
                cite: 1,
            };
            let bounded = incremental.preflight(operation).unwrap();
            incremental.commit(bounded.checkpoint);
            log.record(operation);
        }
        let cold = IncrementalPreflight::new(&log, &weave);
        for lamport in [1, 300, 923, 1201] {
            let late = MoveOp {
                lamport,
                replica: 1,
                child: ids[2],
                dest: Some(ids[1]),
                cite: 1,
            };
            let hot = incremental.preflight(late).unwrap();
            assert_eq!(hot, cold.preflight(late).unwrap());
            assert_eq!(
                hot.selected_status,
                log.prospective_replay_certified(&weave, late)
                    .selected_status()
                    .unwrap()
            );
            assert_eq!(
                hot.canonical_request.len(),
                8 * (5 + ids.len() + 5 + 3 * 4 + 1)
            );
        }
    }

    /// In-order admission certifies one operation, however long the log.
    #[test]
    fn in_order_request_size_is_independent_of_log_length() {
        let (weave, ids) = differential_weave();
        let log = differential_log();
        let mut incremental = IncrementalPreflight::new(&log, &weave);
        let mut largest = 0;
        for offset in 0..(CHECKPOINT_INTERVAL as u64 * 12) {
            let operation = MoveOp {
                lamport: 10 + offset,
                replica: 0,
                child: ids[1 + offset as usize % (ids.len() - 1)],
                dest: None,
                cite: 1,
            };
            let bounded = incremental.preflight(operation).unwrap();
            largest = largest.max(bounded.canonical_request.len());
            incremental.commit(bounded.checkpoint);
        }
        let words = 5 + ids.len() + 3 * 4 + 1 + 5;
        assert_eq!(largest, 8 * words);
        assert!(incremental.checkpoints.len() <= MAX_RETAINED_CHECKPOINTS);
    }
}
