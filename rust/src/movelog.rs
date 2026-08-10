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
        // Dense, deterministic indexing: BTreeMap iteration is sorted by id,
        // identical on every replica with the same weave.
        let ids: Vec<NodeId> = weave.nodes().map(|n| n.id()).collect();
        let index: BTreeMap<NodeId, u64> =
            ids.iter().enumerate().map(|(i, id)| (*id, i as u64)).collect();

        let mut words: Vec<u64> = Vec::with_capacity(2 + ids.len() + self.ops.len() * 4);
        words.push(ids.len() as u64);
        let ops_encoded: Vec<[u64; 4]> = self
            .ops
            .iter()
            .filter_map(|op| {
                let child = *index.get(&op.child)?;
                let dest: i64 = match op.dest {
                    None => -1,
                    Some(d) => *index.get(&d)? as i64,
                };
                Some([op.lamport, op.replica, child, dest as u64])
            })
            .collect();
        words.push(ops_encoded.len() as u64);
        for id in &ids {
            let fp: i64 = weave
                .get(id)
                .and_then(|n| n.parents().first())
                .and_then(|p| index.get(p))
                .map(|i| *i as i64)
                .unwrap_or(-1);
            words.push(fp as u64);
        }
        for op in &ops_encoded {
            words.extend_from_slice(op);
        }
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();

        let out = ffi::replay_kernel(&bytes);

        let mut view = BTreeMap::new();
        for (i, chunk) in out.chunks_exact(8).enumerate() {
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
        view
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
