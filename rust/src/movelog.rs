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
        // `sent` maps slot j to its position in log order for attribution.
        // Lean, not this code, turns these values into FORMAT-v3 bytes.
        let mut sent: Vec<usize> = Vec::with_capacity(self.ops.len());
        let mut ops_encoded: Vec<ffi::ReplayOpInput> = Vec::with_capacity(self.ops.len());
        for (li, op) in self.ops.iter().enumerate() {
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
            sent.push(li);
            ops_encoded.push(ffi::ReplayOpInput {
                lamport: op.lamport,
                replica: op.replica,
                child,
                dest,
                cite: op.cite,
            });
        }
        let m = ops_encoded.len();
        let mut first_parent = Vec::with_capacity(n);
        for id in &ids {
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
            .map(
                |chunk| match i64::from_le_bytes(chunk.try_into().unwrap()) {
                    0 => OpOutcome::Applied,
                    1 => OpOutcome::SkippedCycle,
                    2 => OpOutcome::SkippedInvalid,
                    3 => OpOutcome::SkippedUnauthorised,
                    v => panic!("unknown status word {v} — kernel speaks a newer format"),
                },
            )
            .collect();
        let mut outcomes = Vec::with_capacity(self.ops.len());
        let mut sent_cursor = sent.iter().zip(statuses).peekable();
        for (li, op) in self.ops.iter().enumerate() {
            let outcome = match sent_cursor.peek() {
                Some(&(&sli, st)) if sli == li => {
                    sent_cursor.next();
                    st
                }
                _ => OpOutcome::OmittedUnknownNode,
            };
            outcomes.push((*op, outcome));
        }

        TracedReplay { view, outcomes }
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
}
