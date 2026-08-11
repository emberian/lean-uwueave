//! An RGA-style sequence CRDT with tombstones — with the linearization
//! **authored in Lean and called through FFI**, not re-implemented here.
//!
//! `Uwueave/Sequence.lean` in one paragraph: anchored insertion is
//! coordination-free — the replicated state is a grow-only set of
//! `(element, anchor)` facts, its well-formedness is I-confluent
//! (`wf_iconfluent`), and the visible text is a deterministic derived view
//! (`sequence_view_sec`). What the model leaves as *named* honesty:
//! sibling order is id arbitration no user chose (`run_order_by_id`), and
//! concurrent runs can interleave (`interleaving_anomaly` — reproduced
//! through the real kernel in this module's tests). Deletion, which the
//! model calls future work, is implemented here the classic RGA way: a
//! grow-only tombstone flag; deleted elements leave the visible text but
//! keep their position in the anchor forest, so anchoring under them keeps
//! working (`SeqKernel.linearizeK_sublist_emitAll` is the Lean-side
//! statement that tombstones only ever *filter* the document order).
//!
//! What this Rust file actually does is deliberately dumb: it keeps the
//! element set (a `BTreeMap` keyed by content address — union merge with
//! tombstone-OR), maps ids to dense indices in id order, encodes the request
//! bytes, and hands them to `Uwueave/SeqKernel.lean`'s `uwueave_seq_kernel`
//! (compiled to C by lake, linked by `build.rs`). The order decision — DFS,
//! descending-id sibling arbitration, tombstone filtering — lives in Lean,
//! in one place, next to its abstract model.
//!
//! ## Identity, and what content-addressing buys and costs
//!
//! An element's id is `blake3("uwueave.seq.v1" ‖ anchor ‖ contents)`. That
//! discharges `Sequence.lean`'s `UniqueAnchor` hypothesis cryptographically
//! (one id carries two anchors only via a hash collision — exactly the
//! discharge the model's docs name), and it makes `insert` idempotent: the
//! same contents at the same anchor *is* the same element. The cost is
//! honest and documented: inserting equal contents at the same anchor twice
//! yields one element, and re-inserting a deleted element does **not**
//! resurrect it (the tombstone is grow-only). Distinct occurrences of the
//! same text are distinct elements only when their anchors differ — which
//! is what sequential typing produces anyway (each character anchors to the
//! previous one).
//!
//! ## The groundedness seam
//!
//! `SeqKernel.lean`'s completeness and no-duplication theorems assume `WFK`:
//! anchors in range, and *some rank strictly descending along anchor edges*.
//! The dense index order (id order = hash order) is NOT such a rank — an
//! anchor's hash may exceed its child's. The rank that is: creation rank
//! (`rank = anchor.rank + 1`), grounded by construction because an anchor
//! must exist before anything can anchor to it — `causal.rs`'s argument
//! verbatim. The encoder asserts rank descent on every request, exactly as
//! `movelog.rs` asserts `GroundedBase`: a violation means a corrupted store,
//! and the kernel's theorems would not cover the input, so refusing loudly
//! is the theorem's precondition speaking.

use crate::causal::NodeId;
use crate::ffi;
use std::collections::BTreeMap;

/// One element of the sequence. Anchor and contents are fixed at creation
/// (they are the id's preimage); `deleted` is the one mutable bit, and it
/// only ever goes `false → true`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SeqElem {
    anchor: Option<NodeId>,
    /// `1 + anchor rank`; `0` for root-anchored. The `WFK.grounded` witness
    /// (`Uwueave/SeqKernel.lean`) — a pure function of the anchor DAG, so
    /// every replica derives the same value.
    rank: u64,
    deleted: bool,
    contents: Vec<u8>,
}

fn elem_id(anchor: Option<&NodeId>, contents: &[u8]) -> NodeId {
    let mut h = blake3::Hasher::new();
    h.update(b"uwueave.seq.v1");
    match anchor {
        None => {
            h.update(&[0u8]);
        }
        Some(a) => {
            h.update(&[1u8]);
            h.update(a);
        }
    }
    h.update(&(contents.len() as u64).to_le_bytes());
    h.update(contents);
    *h.finalize().as_bytes()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqInsertError {
    /// The named anchor is not present. Anchoring to the unknown is exactly
    /// the freedom the grounded discipline refuses (`causal.rs`'s
    /// `MissingParent`, same design).
    MissingAnchor(NodeId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqDeleteError {
    /// The element to tombstone is not present.
    UnknownElement(NodeId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeqMergeError {
    /// The same id resolves to different `(anchor, contents)` in the two
    /// states — a collision-resistance failure or corruption. Refused
    /// wholesale (`causal.rs`'s `IdCollision`, same shape): after this no
    /// convergence statement holds, so proceeding would manufacture silent
    /// divergence. Tombstone flags are *not* compared — they are the
    /// monotone payload, merged by OR.
    IdCollision(NodeId),
    /// The other state contains an element whose anchor it does not contain —
    /// it was not anchor-closed, i.e. not produced by this API.
    NotAnchorClosed { element: NodeId, missing_anchor: NodeId },
}

/// Statistics from a merge, mostly for tests and telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SeqMergeStats {
    pub inserted: usize,
    pub already_present: usize,
    /// Elements present on both sides where the other side's tombstone was
    /// news (remove-wins OR flipped our flag).
    pub tombstones_learned: usize,
}

/// The sequence CRDT: a grow-only, content-addressed element set with
/// grow-only tombstones. `merge` is union-by-id plus tombstone-OR; the
/// visible text is derived by the Lean kernel, never stored.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SeqCrdt {
    elems: BTreeMap<NodeId, SeqElem>,
}

impl SeqCrdt {
    pub fn new() -> Self {
        Self { elems: BTreeMap::new() }
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }
    pub fn is_empty(&self) -> bool {
        self.elems.is_empty()
    }
    pub fn contains(&self, id: &NodeId) -> bool {
        self.elems.contains_key(id)
    }
    pub fn is_deleted(&self, id: &NodeId) -> Option<bool> {
        self.elems.get(id).map(|e| e.deleted)
    }
    pub fn contents(&self, id: &NodeId) -> Option<&[u8]> {
        self.elems.get(id).map(|e| e.contents.as_slice())
    }

    /// Insert an element after `anchor` (`None` = at the start of the
    /// document). The anchor must already be present; the returned id is the
    /// content address. Idempotent: the same `(anchor, contents)` pair is the
    /// same element, and re-inserting it does not resurrect a tombstone.
    pub fn insert(
        &mut self,
        anchor: Option<NodeId>,
        contents: &[u8],
    ) -> Result<NodeId, SeqInsertError> {
        let rank = match &anchor {
            None => 0,
            Some(a) => match self.elems.get(a) {
                None => return Err(SeqInsertError::MissingAnchor(*a)),
                Some(el) => el.rank + 1,
            },
        };
        let id = elem_id(anchor.as_ref(), contents);
        if self.elems.contains_key(&id) {
            // Same anchor + same contents ⇒ same element (see module docs).
            return Ok(id);
        }
        self.elems.insert(id, SeqElem { anchor, rank, deleted: false, contents: contents.to_vec() });
        Ok(id)
    }

    /// Tombstone an element. Grow-only: there is no un-delete, and merge
    /// ORs the flags (remove wins). The element stays in the forest, so
    /// everything anchored under it keeps its position — and new insertions
    /// may still anchor to it.
    pub fn delete(&mut self, id: &NodeId) -> Result<(), SeqDeleteError> {
        match self.elems.get_mut(id) {
            None => Err(SeqDeleteError::UnknownElement(*id)),
            Some(el) => {
                el.deleted = true;
                Ok(())
            }
        }
    }

    /// The CRDT join: union by id (skip-if-present, verify-on-collision,
    /// `causal.rs` shape) plus tombstone-OR. Validates before mutating:
    /// refuses wholesale rather than half-applying.
    pub fn merge(&mut self, other: &Self) -> Result<SeqMergeStats, SeqMergeError> {
        for (id, el) in &other.elems {
            if let Some(mine) = self.elems.get(id) {
                if mine.anchor != el.anchor || mine.contents != el.contents {
                    return Err(SeqMergeError::IdCollision(*id));
                }
            }
            if let Some(a) = &el.anchor {
                if !other.elems.contains_key(a) {
                    return Err(SeqMergeError::NotAnchorClosed {
                        element: *id,
                        missing_anchor: *a,
                    });
                }
            }
        }
        let mut stats = SeqMergeStats::default();
        // Insert in rank order so anchor-closure of `other` implies every
        // anchor is present (with its rank) by the time its child lands.
        let mut incoming: Vec<(&NodeId, &SeqElem)> = other.elems.iter().collect();
        incoming.sort_by_key(|(_, e)| e.rank);
        for (id, el) in incoming {
            match self.elems.get_mut(id) {
                Some(mine) => {
                    debug_assert_eq!(
                        mine.rank, el.rank,
                        "rank is a pure function of the anchor DAG; divergence is corruption"
                    );
                    stats.already_present += 1;
                    if el.deleted && !mine.deleted {
                        mine.deleted = true; // remove wins
                        stats.tombstones_learned += 1;
                    }
                }
                None => {
                    self.elems.insert(*id, el.clone());
                    stats.inserted += 1;
                }
            }
        }
        Ok(stats)
    }

    /// The visible document, as element ids in document order — derived by
    /// the Lean kernel (`Uwueave/SeqKernel.lean`, SEQ FORMAT v1): dense
    /// id-sorted indices in, visible linearization out. Deterministic and
    /// replica-independent for equal states (the dense order is the id
    /// order, and `linearizeK` is a pure function).
    pub fn visible(&self) -> Vec<NodeId> {
        // Dense, deterministic indexing: BTreeMap iteration is sorted by id,
        // identical on every replica with the same element set. The index
        // order is the kernel's sibling-arbitration order.
        let ids: Vec<NodeId> = self.elems.keys().copied().collect();
        let index: BTreeMap<NodeId, u64> =
            ids.iter().enumerate().map(|(i, id)| (*id, i as u64)).collect();
        let n = ids.len();

        let mut words: Vec<u64> = Vec::with_capacity(1 + 2 * n);
        words.push(n as u64);
        for (_, el) in &self.elems {
            let a: i64 = match &el.anchor {
                None => -1,
                Some(a) => {
                    // `WFK`'s grounded hypothesis, enforced where Rust meets
                    // Lean (mirror of movelog.rs's GroundedBase assert): the
                    // kernel's completeness and no-duplication theorems
                    // assume some rank strictly descends along anchor edges.
                    // Creation rank is that rank, by construction — this can
                    // only fire on a corrupted store, at which point the
                    // kernel's verdicts would be garbage, and refusing loudly
                    // is the theorem's precondition speaking.
                    let anchor_el = self
                        .elems
                        .get(a)
                        .expect("state is anchor-closed: insert/merge refuse otherwise");
                    assert!(
                        anchor_el.rank < el.rank,
                        "non-grounded anchor forest: rank does not descend along an \
                         anchor edge ({} -> {}); the kernel's WFK theorems do not \
                         cover this input (Uwueave/SeqKernel.lean)",
                        el.rank,
                        anchor_el.rank,
                    );
                    *index.get(a).expect("anchors are present, hence indexed") as i64
                }
            };
            words.push(a as u64);
        }
        for (_, el) in &self.elems {
            words.push(if el.deleted { 1 } else { 0 });
        }
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();

        let out = ffi::seq_kernel(&bytes);

        // SEQ FORMAT v1 response: one length word, then exactly that many
        // index words. Anything else means the two sides disagree about the
        // wire format — refuse rather than reinterpret.
        assert!(
            out.len() >= 8 && out.len() % 8 == 0,
            "kernel response is not whole words"
        );
        let mut w = out.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap()));
        let k = w.next().expect("length word") as usize;
        assert_eq!(
            out.len(),
            8 * (1 + k),
            "kernel response is not seq format v1 (expected 1 + k = {} words)",
            1 + k
        );
        w.map(|idx| {
            let idx = idx as usize;
            assert!(idx < n, "kernel emitted an out-of-range index {idx} (n = {n})");
            ids[idx]
        })
        .collect()
    }

    /// The visible document, as bytes: the concatenated contents of
    /// `visible()`.
    pub fn text(&self) -> Vec<u8> {
        self.visible()
            .iter()
            .flat_map(|id| self.elems[id].contents.iter().copied())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two replicas insert concurrently (each locally valid); after both
    /// exchange, states and visible documents agree — `sequence_view_sec`'s
    /// convergence, through the real kernel.
    #[test]
    fn two_replica_concurrent_inserts_converge() {
        let mut a = SeqCrdt::new();
        let ha = a.insert(None, b"hello ").unwrap();
        let _ = a.insert(Some(ha), b"world").unwrap();

        let mut b = a.clone();
        let _ = a.insert(Some(ha), b"cruel ").unwrap();
        let _ = b.insert(None, b"oh, ").unwrap();

        let mut ab = a.clone();
        ab.merge(&b).unwrap();
        let mut ba = b.clone();
        ba.merge(&a).unwrap();
        assert_eq!(ab, ba, "states converge");
        assert_eq!(ab.visible(), ba.visible(), "documents converge");
        assert_eq!(ab.visible().len(), 4, "all four elements visible");
    }

    /// Remove-wins on the flag: a tombstone learned from either side
    /// survives the merge in both directions, and re-inserting the same
    /// element does not resurrect it.
    #[test]
    fn delete_survives_merge() {
        let mut a = SeqCrdt::new();
        let x = a.insert(None, b"x").unwrap();
        let mut b = a.clone();

        a.delete(&x).unwrap();
        assert_eq!(a.visible(), Vec::<NodeId>::new(), "locally deleted");

        // The replica that never saw the delete merges it in…
        b.merge(&a).unwrap();
        assert_eq!(b.is_deleted(&x), Some(true), "tombstone-OR: remove wins");
        assert_eq!(b.visible(), Vec::<NodeId>::new());

        // …and merging the stale replica back cannot resurrect.
        let mut fresh = SeqCrdt::new();
        let x2 = fresh.insert(None, b"x").unwrap();
        assert_eq!(x, x2, "content address is deterministic");
        a.merge(&fresh).unwrap();
        assert_eq!(a.is_deleted(&x), Some(true), "merge cannot resurrect");

        // Neither can a local re-insert of the same (anchor, contents).
        let x3 = a.insert(None, b"x").unwrap();
        assert_eq!(x, x3);
        assert_eq!(a.is_deleted(&x), Some(true), "re-insert cannot resurrect");
    }

    /// The RGA tombstone rule: a deleted element leaves the text but keeps
    /// its position in the forest — its descendants stay visible, and *new*
    /// insertions may still anchor to it (`linearizeK_sublist_emitAll` /
    /// the `emitK`-takes-no-tombstones construction, exercised end-to-end).
    #[test]
    fn anchoring_under_deleted_element_works() {
        let mut s = SeqCrdt::new();
        let a = s.insert(None, b"a").unwrap();
        let b = s.insert(Some(a), b"b").unwrap();
        assert_eq!(s.text(), b"ab");

        s.delete(&a).unwrap();
        assert_eq!(s.visible(), vec![b], "descendant of a tombstone survives");
        assert_eq!(s.text(), b"b");

        // Anchor a NEW element under the tombstone: it lands where 'a's
        // subtree lives, even though 'a' itself is invisible.
        let c = s.insert(Some(a), b"c").unwrap();
        let vis = s.visible();
        assert_eq!(vis.len(), 2);
        assert!(vis.contains(&b) && vis.contains(&c), "both children visible");
        assert!(!vis.contains(&a), "the tombstone itself stays invisible");

        // And deleting the anchor of a whole run leaves the run intact.
        let d = s.insert(Some(b), b"d").unwrap();
        s.delete(&b).unwrap();
        let vis = s.visible();
        assert!(vis.contains(&d), "grandchild of a tombstone survives");
        assert!(!vis.contains(&b));
    }

    /// `Uwueave.Sequence.interleaving_anomaly`, reproduced through the real
    /// kernel. The Lean witness: two replicas each insert a two-element run
    /// at the head of the document ([3,1] and [4,2] there); each run is
    /// contiguous on its own screen; the merged document is [4,3,2,1] — the
    /// runs strictly alternated, an order neither user wrote. Here ids are
    /// hashes, so we search a nonce until the four ids arbitrate
    /// alternately (the anomaly is a property of the *arbitration order*,
    /// which for this crate is hash order), then replay the scenario.
    #[test]
    fn interleaving_anomaly_through_the_kernel() {
        for nonce in 0u32.. {
            let nb = nonce.to_le_bytes();
            let mk = |tag: &[u8]| -> Vec<u8> {
                let mut v = tag.to_vec();
                v.extend_from_slice(&nb);
                v
            };
            // Replica X inserts two elements at the root (head-insert
            // pattern), replica Y likewise, concurrently.
            let mut x = SeqCrdt::new();
            let x1 = x.insert(None, &mk(b"x1")).unwrap();
            let x2 = x.insert(None, &mk(b"x2")).unwrap();
            let mut y = SeqCrdt::new();
            let y1 = y.insert(None, &mk(b"y1")).unwrap();
            let y2 = y.insert(None, &mk(b"y2")).unwrap();

            // Each replica's local document is its own run, contiguous
            // (trivially — it holds nothing else), in descending id order.
            let mut xs = vec![x1, x2];
            xs.sort();
            xs.reverse();
            assert_eq!(x.visible(), xs, "X's local run, newest-id first");
            let mut ys = vec![y1, y2];
            ys.sort();
            ys.reverse();
            assert_eq!(y.visible(), ys, "Y's local run, newest-id first");

            // Merged: all four at the root, in descending id order — pure
            // arbitration (`run_order_by_id`). Search for a nonce where that
            // order strictly alternates ownership, i.e. the [4,3,2,1] shape.
            let mut all = vec![x1, x2, y1, y2];
            all.sort();
            all.reverse();
            let owners: Vec<bool> = all.iter().map(|id| xs.contains(id)).collect();
            if !owners.windows(2).all(|w| w[0] != w[1]) {
                continue; // this nonce's hash order doesn't alternate; try the next
            }

            let mut merged = x.clone();
            merged.merge(&y).unwrap();
            let mut merged2 = y.clone();
            merged2.merge(&x).unwrap();
            assert_eq!(merged, merged2, "convergence held");
            assert_eq!(
                merged.visible(),
                all,
                "merged document is the id-arbitrated order"
            );
            // The anomaly, concretely: ownership strictly alternates, so
            // neither replica's contiguous run survived — the Lean
            // [4,3,2,1] witness, through the shipping kernel.
            let owners: Vec<bool> =
                merged.visible().iter().map(|id| xs.contains(id)).collect();
            assert!(
                owners.windows(2).all(|w| w[0] != w[1]),
                "the two runs came out strictly alternated (interleaving_anomaly)"
            );
            return;
        }
        unreachable!("some nonce yields an alternating hash order");
    }
}
