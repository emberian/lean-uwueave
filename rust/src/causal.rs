//! The append-only, content-addressed causal DAG — the free fragment.
//!
//! A node's identity is `blake3(parent ids ‖ contents)`, so parents are fixed
//! at creation and must exist before the child can even be named. Rank
//! (`1 + max parent rank`) therefore strictly descends along every edge — the
//! `Grounded` invariant of `Uwueave/Acyclicity.lean` — and by
//! `grounded_acyclic` the store can never hold a cycle, while by
//! `grounded_iconfluent` a merge of any two well-formed stores is well-formed
//! with **no cycle check and no coordination**. That is the entire reason this
//! type gets to have an infallible-by-design union merge where a mutable graph
//! could not (`acyclicity_not_iconfluent`).
//!
//! The one seam the theorems name: convergence assumes an id resolves to the
//! same node everywhere. Content-addressing makes that a collision-resistance
//! premise, so a same-id-different-bytes encounter is treated as **corruption
//! and refused loudly** ([`MergeError::IdCollision`]), never deduplicated
//! silently.

use std::collections::{BTreeMap, BTreeSet};

/// Content address of a node.
pub type NodeId = [u8; 32];

/// One node of the weave. Parents are fixed at creation — this is what keeps
/// the structure on the free side of the dichotomy. Reparenting is *not* a
/// mutation of this type; it lives in [`crate::movelog`] as derived state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CausalNode<T> {
    id: NodeId,
    parents: Vec<NodeId>,
    /// `1 + max(parent ranks)`; `0` for roots. The `Grounded` witness.
    rank: u64,
    contents: T,
}

impl<T> CausalNode<T> {
    pub fn id(&self) -> NodeId {
        self.id
    }
    pub fn parents(&self) -> &[NodeId] {
        &self.parents
    }
    pub fn rank(&self) -> u64 {
        self.rank
    }
    pub fn contents(&self) -> &T {
        &self.contents
    }
}

fn node_id(parents: &[NodeId], contents: &[u8]) -> NodeId {
    let mut h = blake3::Hasher::new();
    h.update(b"uwueave.causal.v1");
    h.update(&(parents.len() as u64).to_le_bytes());
    for p in parents {
        h.update(p);
    }
    h.update(&(contents.len() as u64).to_le_bytes());
    h.update(contents);
    *h.finalize().as_bytes()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InsertError {
    /// A named parent is not present. Unknown-parent insertion is exactly the
    /// arbitrary-edge freedom that `acyclicity_not_iconfluent` refutes; the
    /// refusal is the design, not a limitation.
    MissingParent(NodeId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MergeError {
    /// The same id resolves to different nodes in the two stores — a
    /// collision-resistance failure or corruption. The whole merge is refused:
    /// after this, *no* convergence statement holds, so proceeding would
    /// manufacture silent divergence.
    IdCollision(NodeId),
    /// The other store contains a node whose parent it does not contain —
    /// it was not causally closed, i.e. not produced by this API.
    NotCausallyClosed { node: NodeId, missing_parent: NodeId },
}

/// Statistics from a merge, mostly for tests and telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct MergeStats {
    pub inserted: usize,
    pub already_present: usize,
}

/// The append-only weave store. `merge` is a set union keyed by content
/// address (skip-if-present), which the Lean development shows is a genuine
/// join-semilattice on the id-keyset — commutative, associative, idempotent —
/// so gossip may repeat, reorder and batch deltas freely.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CausalWeave<T> {
    nodes: BTreeMap<NodeId, CausalNode<T>>,
    /// Derived: parent id → child ids. A pure function of `nodes`, maintained
    /// incrementally; never merged, only re-derived.
    children: BTreeMap<NodeId, BTreeSet<NodeId>>,
    /// Derived: nodes with no parents.
    roots: BTreeSet<NodeId>,
}

impl<T: AsRef<[u8]> + Clone + PartialEq> CausalWeave<T> {
    pub fn new() -> Self {
        Self { nodes: BTreeMap::new(), children: BTreeMap::new(), roots: BTreeSet::new() }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
    pub fn get(&self, id: &NodeId) -> Option<&CausalNode<T>> {
        self.nodes.get(id)
    }
    pub fn contains(&self, id: &NodeId) -> bool {
        self.nodes.contains_key(id)
    }
    pub fn roots(&self) -> impl Iterator<Item = &NodeId> {
        self.roots.iter()
    }
    pub fn children(&self, id: &NodeId) -> impl Iterator<Item = &NodeId> {
        self.children.get(id).into_iter().flatten()
    }
    pub fn nodes(&self) -> impl Iterator<Item = &CausalNode<T>> {
        self.nodes.values()
    }

    /// Append a node. Parents must already be present; the returned id is the
    /// content address. Grounded-by-construction: `rank = 1 + max parent rank`.
    pub fn insert(&mut self, parents: Vec<NodeId>, contents: T) -> Result<NodeId, InsertError> {
        let mut rank = 0u64;
        for p in &parents {
            match self.nodes.get(p) {
                None => return Err(InsertError::MissingParent(*p)),
                Some(pn) => rank = rank.max(pn.rank + 1),
            }
        }
        let id = node_id(&parents, contents.as_ref());
        if self.nodes.contains_key(&id) {
            // Same parents + same bytes ⇒ same node: idempotent re-insert.
            return Ok(id);
        }
        self.index_node(CausalNode { id, parents, rank, contents });
        Ok(id)
    }

    fn index_node(&mut self, node: CausalNode<T>) {
        if node.parents.is_empty() {
            self.roots.insert(node.id);
        }
        for p in &node.parents {
            self.children.entry(*p).or_default().insert(node.id);
        }
        self.nodes.insert(node.id, node);
    }

    /// The CRDT join: union by id, skip-if-present, verify-on-collision.
    /// Inserts in rank order so causal closure of `other` implies every
    /// parent is present by the time its child lands.
    pub fn merge(&mut self, other: &Self) -> Result<MergeStats, MergeError> {
        // Validate before mutating: refuse wholesale rather than half-apply.
        for node in other.nodes.values() {
            if let Some(mine) = self.nodes.get(&node.id) {
                if mine.parents != node.parents || mine.contents != node.contents {
                    return Err(MergeError::IdCollision(node.id));
                }
            }
            for p in &node.parents {
                if !other.nodes.contains_key(p) {
                    return Err(MergeError::NotCausallyClosed {
                        node: node.id,
                        missing_parent: *p,
                    });
                }
            }
        }
        let mut stats = MergeStats::default();
        let mut incoming: Vec<&CausalNode<T>> = other.nodes.values().collect();
        incoming.sort_by_key(|n| n.rank);
        for node in incoming {
            if self.nodes.contains_key(&node.id) {
                stats.already_present += 1;
            } else {
                self.index_node(node.clone());
                stats.inserted += 1;
            }
        }
        Ok(stats)
    }

    /// Check the `Grounded` invariant directly (test/audit affordance; the
    /// API cannot construct a violation, which is the point).
    pub fn grounded(&self) -> bool {
        self.nodes.values().all(|n| {
            n.parents
                .iter()
                .all(|p| self.nodes.get(p).map(|pn| pn.rank < n.rank).unwrap_or(false))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn weave_with(chunks: &[&[u8]]) -> (CausalWeave<Vec<u8>>, Vec<NodeId>) {
        // A chain: each chunk is a child of the previous one.
        let mut w = CausalWeave::new();
        let mut ids = Vec::new();
        let mut parent: Vec<NodeId> = vec![];
        for c in chunks {
            let id = w.insert(parent.clone(), c.to_vec()).unwrap();
            ids.push(id);
            parent = vec![id];
        }
        (w, ids)
    }

    /// Mirror of `acyclicity_not_iconfluent`'s clashing pair — here the pair
    /// is *unrepresentable*: an edge to an absent node refuses at insert, so
    /// the `{0→1}` / `{1→0}` replicas cannot be built to begin with.
    #[test]
    fn lean_witness_cycle_pair_unrepresentable() {
        let mut w: CausalWeave<Vec<u8>> = CausalWeave::new();
        let ghost = [7u8; 32];
        assert_eq!(w.insert(vec![ghost], b"child of nothing".to_vec()), Err(InsertError::MissingParent(ghost)));
    }

    /// Merge is commutative, associative, idempotent on the id-keyset
    /// (`LaceMerge`-shaped laws; unit-level replay of the Lean lattice laws).
    #[test]
    fn merge_laws() {
        let (a, _) = weave_with(&[b"g", b"a1", b"a2"]);
        let (b, _) = weave_with(&[b"g", b"b1"]);
        let (c, _) = weave_with(&[b"g", b"c1", b"c2", b"c3"]);

        let mut ab = a.clone();
        ab.merge(&b).unwrap();
        let mut ba = b.clone();
        ba.merge(&a).unwrap();
        assert_eq!(ab, ba, "comm");

        let mut ab_c = ab.clone();
        ab_c.merge(&c).unwrap();
        let mut bc = b.clone();
        bc.merge(&c).unwrap();
        let mut a_bc = a.clone();
        a_bc.merge(&bc).unwrap();
        assert_eq!(ab_c, a_bc, "assoc");

        let mut aa = a.clone();
        aa.merge(&a).unwrap();
        assert_eq!(aa, a, "idem");

        assert!(ab_c.grounded(), "grounded survives every merge");
    }

    /// Same id, different bytes → the merge refuses (CrossCanonical seam).
    #[test]
    fn id_collision_refused() {
        let (a, ids) = weave_with(&[b"g", b"x"]);
        let mut b = a.clone();
        // Forge: corrupt the stored contents behind an existing id.
        b.nodes.get_mut(&ids[1]).unwrap().contents = b"forged".to_vec();
        let mut target = a.clone();
        assert_eq!(target.merge(&b), Err(MergeError::IdCollision(ids[1])));
    }

    /// A non-causally-closed delta is refused wholesale.
    #[test]
    fn not_causally_closed_refused() {
        let (a, ids) = weave_with(&[b"g", b"x", b"y"]);
        let mut delta = a.clone();
        // Remove the middle node: `y`'s parent is now absent from the delta.
        delta.nodes.remove(&ids[1]);
        let mut target: CausalWeave<Vec<u8>> = CausalWeave::new();
        match target.merge(&delta) {
            Err(MergeError::NotCausallyClosed { .. }) => {}
            other => panic!("expected NotCausallyClosed, got {other:?}"),
        }
    }
}
