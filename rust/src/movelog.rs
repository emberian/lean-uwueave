//! Node moving as a derived view over a grow-only operation log.
//!
//! `Leanuweave/Move.lean` in one paragraph: reparenting cannot be a direct
//! CRDT mutation (`acyclicity_not_iconfluent`), so **replicate the monotone
//! thing** — the set of move operations ever issued, a trivial grow-only set —
//! **and derive the invariant-bearing thing**: replay the ops in total
//! timestamp order, skipping any op whose application would close a cycle.
//! `derived_view_sec` gives order-independence, redelivery-immunity and
//! by-construction acyclicity; `view_not_stable` is the priced anomaly, which
//! this module's docs and tests keep in view rather than hiding: **an older
//! remote op can retroactively skip a move you already saw applied.** UIs
//! should treat the effective parent map as watchable derived state, not as
//! something edits append to.

use crate::causal::{CausalWeave, NodeId};
use std::collections::{BTreeMap, BTreeSet};

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

    /// Replay: the effective parent-override map, derived deterministically
    /// from (log, weave). An op is **skipped** iff its destination's effective
    /// ancestor chain (at that point in the replay) passes through its child —
    /// the Kleppmann cycle rule. Equal logs ⇒ equal views; the view is acyclic
    /// by construction.
    pub fn replay<T: AsRef<[u8]> + Clone + PartialEq>(
        &self,
        weave: &CausalWeave<T>,
    ) -> BTreeMap<NodeId, Option<NodeId>> {
        let mut overrides: BTreeMap<NodeId, Option<NodeId>> = BTreeMap::new();
        // BTreeSet iteration is already the total (lamport, replica, …) order.
        for op in &self.ops {
            if !weave.contains(&op.child) {
                continue; // op about a node this replica hasn't seen yet
            }
            match op.dest {
                None => {
                    overrides.insert(op.child, None);
                }
                Some(dest) => {
                    if !weave.contains(&dest) {
                        continue;
                    }
                    if Self::chain_passes_through(weave, &overrides, dest, op.child) {
                        continue; // would close a cycle: SKIP (the arbitration)
                    }
                    overrides.insert(op.child, Some(dest));
                }
            }
        }
        overrides
    }

    /// Effective parent of `n`: override if present, else first weave parent.
    fn effective_parent<T: AsRef<[u8]> + Clone + PartialEq>(
        weave: &CausalWeave<T>,
        overrides: &BTreeMap<NodeId, Option<NodeId>>,
        n: NodeId,
    ) -> Option<NodeId> {
        match overrides.get(&n) {
            Some(o) => *o,
            None => weave.get(&n).and_then(|node| node.parents().first().copied()),
        }
    }

    fn chain_passes_through<T: AsRef<[u8]> + Clone + PartialEq>(
        weave: &CausalWeave<T>,
        overrides: &BTreeMap<NodeId, Option<NodeId>>,
        from: NodeId,
        needle: NodeId,
    ) -> bool {
        let mut cur = Some(from);
        let mut seen = BTreeSet::new();
        while let Some(n) = cur {
            if n == needle {
                return true;
            }
            if !seen.insert(n) {
                return false; // defensive: view should be acyclic already
            }
            cur = Self::effective_parent(weave, overrides, n);
        }
        false
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

    /// Scenario mirror of `Leanuweave.Move.view_not_stable` — o₁ (t=2) moves
    /// n₀ under n₁; the *older* o₂ (t=1) moves n₁ under n₀. With o₁ alone the
    /// view shows the move; after o₂ arrives, replay applies o₂ first and
    /// skips o₁ as cycle-creating: the already-seen move is un-happened.
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
    /// generalized as a property exercised on the mirror scenario).
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
}
