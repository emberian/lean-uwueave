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
//! indices, encodes the request bytes, and hands them to
//! `Uwueave/Exec.lean`'s `uwueave_replay_kernel` (compiled to C by lake,
//! linked by `build.rs`). The ordering rule and the cycle-skip decision — the
//! parts that must be *right* — live in Lean, in one place, next to their
//! abstract model.
//!
//! **Wire format v2** (see `Exec.lean`'s contract header): the kernel's
//! response is `n` override words followed by `m` per-op status words in
//! request order (0 = applied, 1 = skipped by the cycle rule, 2 = skipped as
//! invalid). [`MoveLog::replay`] keeps its classic view-only shape;
//! [`MoveLog::replay_traced`] surfaces the trace, which is `view_not_stable`
//! made observable — a UI can show *which* op an older remote edit
//! retroactively skipped. The decode refuses (panics) on any response that
//! is not exactly `n + m` words: a length mismatch means the two sides
//! disagree about the format, and reinterpreting would be silent corruption.

use crate::causal::{CausalWeave, NodeId};
use crate::ffi;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

/// A reparenting operation. Total order = `(lamport, replica, child, dest)`,
/// so replay order is deterministic across replicas — the arbitration is the
/// timestamp, exactly and only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct MoveOp {
    pub lamport: u64,
    pub replica: u64,
    pub child: NodeId,
    /// `None` = move to root (clear the override).
    pub dest: Option<NodeId>,
}

/// The fate of one op in a replay: the kernel's v2 status block, decoded,
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
    /// Not sent to the kernel: the op names a node this replica has not seen
    /// yet. It re-enters the replay when its nodes arrive — the view is
    /// always a function of the current (log, weave) pair.
    OmittedUnknownNode,
}

/// A replay view together with the per-op trace (format v2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TracedReplay {
    /// The effective parent-override map — identical to [`MoveLog::replay`]'s
    /// return for the same (log, weave).
    pub view: BTreeMap<NodeId, Option<NodeId>>,
    /// Exactly one outcome per op in the log, in log (`BTreeSet`) order.
    pub outcomes: Vec<(MoveOp, OpOutcome)>,
}

/// The grow-only move log. Merge is set union — the whole point.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MoveLog {
    ops: BTreeSet<MoveOp>,
}

impl MoveLog {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record(&mut self, op: MoveOp) {
        self.ops.insert(op);
    }

    /// The CRDT join. Infallible: unions cannot conflict.
    pub fn merge(&mut self, other: &Self) {
        self.ops.extend(other.ops.iter().copied());
    }

    pub fn len(&self) -> usize {
        self.ops.len()
    }
    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
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

    /// [`MoveLog::replay`], plus the kernel's v2 per-op trace: exactly one
    /// [`OpOutcome`] for every op in the log. This is `view_not_stable` made
    /// operational — after an older remote op syncs in, the move it
    /// retroactively un-happened shows up here as [`OpOutcome::SkippedCycle`].
    pub fn replay_traced<T: AsRef<[u8]> + Clone + PartialEq>(
        &self,
        weave: &CausalWeave<T>,
    ) -> TracedReplay {
        // Dense, deterministic indexing: BTreeMap iteration is sorted by id,
        // identical on every replica with the same weave.
        let ids: Vec<NodeId> = weave.nodes().map(|n| n.id()).collect();
        let index: BTreeMap<NodeId, u64> =
            ids.iter().enumerate().map(|(i, id)| (*id, i as u64)).collect();
        let n = ids.len();

        let mut words: Vec<u64> = Vec::with_capacity(2 + n + self.ops.len() * 4);
        words.push(n as u64);
        // Encode the resolvable ops in log order, remembering which log ops
        // were sent: request slot j holds the j-th resolvable op, so `sent`
        // maps slot j to its position in log order for trace attribution.
        let mut sent: Vec<usize> = Vec::with_capacity(self.ops.len());
        let mut ops_encoded: Vec<[u64; 4]> = Vec::with_capacity(self.ops.len());
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
            ops_encoded.push([op.lamport, op.replica, child, dest as u64]);
        }
        let m = ops_encoded.len();
        words.push(m as u64);
        for id in &ids {
            let node = weave.get(id).expect("ids were just enumerated from this weave");
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
            words.push(fp as u64);
        }
        for op in &ops_encoded {
            words.extend_from_slice(op);
        }
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();

        // Marshaller self-differential (debug builds): the Lean side proves
        // decode ∘ encodeRequest = id, so asking the kernel "are these bytes
        // canonical?" checks this encoder byte-for-byte against the *proven*
        // canonical encoder — on every request, hence on every property-suite
        // case. Test evidence, not proof (Rust has no formal semantics), but
        // the strongest closure available for the one unverified codec step.
        debug_assert!(
            ffi::request_canonical(&bytes),
            "request encoder disagrees with the proven canonical `Exec.encodeRequest`"
        );

        let out = ffi::replay_kernel(&bytes);

        // Format v2: exactly n override words then m status words. Anything
        // else means the two sides disagree about the wire format — refuse
        // rather than reinterpret.
        assert_eq!(
            out.len(),
            8 * (n + m),
            "kernel response is not format v2 (expected n + m = {} words)",
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
            .map(|chunk| match i64::from_le_bytes(chunk.try_into().unwrap()) {
                0 => OpOutcome::Applied,
                1 => OpOutcome::SkippedCycle,
                2 => OpOutcome::SkippedInvalid,
                v => panic!("unknown status word {v} — kernel speaks a newer format"),
            })
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

    fn two_nodes() -> (CausalWeave<Vec<u8>>, NodeId, NodeId) {
        let mut w = CausalWeave::new();
        let n0 = w.insert(vec![], b"n0".to_vec()).unwrap();
        let n1 = w.insert(vec![], b"n1".to_vec()).unwrap();
        (w, n0, n1)
    }

    /// Scenario mirror of `Uwueave.Move.view_not_stable` — o₁ (t=2) moves
    /// n₀ under n₁; the *older* o₂ (t=1) moves n₁ under n₀. With o₁ alone the
    /// view shows the move; after o₂ arrives, replay applies o₂ first and
    /// skips o₁ as cycle-creating: the already-seen move is un-happened.
    /// (This test now exercises the Lean kernel end-to-end.)
    #[test]
    fn lean_witness_view_not_stable() {
        let (w, n0, n1) = two_nodes();
        let o1 = MoveOp { lamport: 2, replica: 0, child: n0, dest: Some(n1) };
        let o2 = MoveOp { lamport: 1, replica: 1, child: n1, dest: Some(n0) };

        let mut log = MoveLog::new();
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
        let (w, n0, n1) = two_nodes();
        let o1 = MoveOp { lamport: 2, replica: 0, child: n0, dest: Some(n1) };
        let o2 = MoveOp { lamport: 1, replica: 1, child: n1, dest: Some(n0) };

        let mut a = MoveLog::new();
        a.record(o1);
        a.record(o2);
        let mut b = MoveLog::new();
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
        let (w, n0, n1) = two_nodes();
        let mut log = MoveLog::new();
        log.record(MoveOp { lamport: 2, replica: 0, child: n0, dest: Some(n1) });
        log.record(MoveOp { lamport: 1, replica: 1, child: n1, dest: Some(n0) });
        let view = log.replay(&w);
        let p0 = view.get(&n0).copied().flatten();
        let p1 = view.get(&n1).copied().flatten();
        assert!(!(p0 == Some(n1) && p1 == Some(n0)), "no 2-cycle in the view");
    }

    /// The v2 trace on the `view_not_stable` scenario: o₂ applied, o₁
    /// skipped-by-cycle — the Lean-side `absReplayFull_both_statuses`
    /// (`Move.lean` §3), observed through the real kernel.
    #[test]
    fn lean_witness_trace_shows_the_skip() {
        let (w, n0, n1) = two_nodes();
        let o1 = MoveOp { lamport: 2, replica: 0, child: n0, dest: Some(n1) };
        let o2 = MoveOp { lamport: 1, replica: 1, child: n1, dest: Some(n0) };
        let mut log = MoveLog::new();
        log.record(o1);
        log.record(o2);
        let traced = log.replay_traced(&w);
        assert_eq!(traced.view, log.replay(&w), "traced view = plain view");
        let outcome = |op: &MoveOp| {
            traced.outcomes.iter().find(|(o, _)| o == op).map(|(_, s)| *s)
        };
        assert_eq!(outcome(&o1), Some(OpOutcome::SkippedCycle), "the skip is named");
        assert_eq!(outcome(&o2), Some(OpOutcome::Applied));
    }

    /// Move-to-root is an override too, distinct from "no override".
    #[test]
    fn move_to_root() {
        let (w, n0, n1) = two_nodes();
        let mut log = MoveLog::new();
        log.record(MoveOp { lamport: 1, replica: 0, child: n0, dest: Some(n1) });
        log.record(MoveOp { lamport: 2, replica: 0, child: n0, dest: None });
        let view = log.replay(&w);
        assert_eq!(view.get(&n0), Some(&None), "explicitly at root");
    }
}
