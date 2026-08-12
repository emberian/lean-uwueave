/-
# Uwueave.Weave — universal-weave's feature list, classified.

This file walks `universal-weave`'s README feature list (v0.4.3) and pins each
feature to its verdict under the judgement of this library. One feature gets a
new theorem here (the active path — it is loom-specific and the refutation is
instructive); the rest are instances of catalog results, cited by name so the
mapping is checkable rather than vibes.

## The classification

**Nodes / insertion** (parents fixed at creation, ids content-derived):
  FREE — `Acyclicity.causal_dag_free`. Append-only node insertion into a
  hash-linked weave needs no cycle check and no coordination at any scale.
  DAG-ness is structural. This covers the whole "embedded DAG" milestone's
  data layer and the multiplayer one's, if ids stay content-derived.

**Bookmarking**:
  FREE as a set — `Catalog.gset_mem_iconfluent` (2P/OR flavors for
  un-bookmarking: `gset_notmem_iconfluent` and the tombstone remark). Any
  *cap* on bookmarks is `gset_atMostOne_not_iconfluent`-shaped: per-device
  caps are free by escrow (`escrow_local_bound_iconfluent`); a shared global
  cap escalates.

**Activation / deactivation — the active path**:
  * per-user (each participant has their own view position): FREE — it is a
    keyed register map, `pi_iconfluent` over LWW.
  * shared-and-replicated ("the document's one active path"): NOT FREE —
    `active_path_not_iconfluent` below. Two users activate sibling branches;
    the merged flag-set activates both, which is no longer a path. A
    multiplayer loom must either scope activation per-user (recommended; it
    is also the better UX) or accept LWW arbitration on the whole path
    (one user's navigation silently wins).

**Editing (node contents)**:
  single register per node: FREE per node (`lww_every_invariant_iconfluent`),
  with the cross-field caveat `lww_cross_field_not_iconfluent` — any invariant
  *relating* two nodes' contents (a summary node that must match its source,
  a length field mirrored in a parent) is at risk at merge. Concurrent
  *intra-text* editing is the sequence-CRDT problem — that is what loro is
  for; nothing here replaces it.

**Splitting / merging / deduplication (of nodes)**:
  These rewrite node *identity* — nonmonotonic, and worse than moves (a move
  re-points an edge; a split/merge re-points the namespace). The workable
  shape is `Move.derived_view_sec`: replicate "split/merge happened" as ops,
  derive the presented weave, with `Move.view_not_stable` as the UX warning —
  a peer's older op can re-split what you merged. Content-hash dedup has a
  sharper corner: if ids are content-derived, an *edit* changes the id, which
  is a delete+insert at the identity layer; dedup-as-view (canonical
  representative chosen deterministically at read) is free, dedup-as-mutation
  is an op.

**Node moving (the DAG weave's `moving` feature)**:
  NOT FREE as direct state mutation — `Acyclicity.acyclicity_not_iconfluent`
  is exactly this feature. FREE as an op-log with cycle-skip replay —
  `Move.derived_view_sec` — at the price of `Move.view_not_stable`.

**Serialization robustness ("robust to untrusted inputs")**:
  Orthogonal to merge, with one seam worth naming: convergence proofs here
  assume ids resolve identically across replicas. Content-addressing makes
  that a collision-resistance premise; an attacker-supplied weave that reuses
  an id for different contents is the `CrossCanonical` failure — two replicas
  with equal id-sets and different documents. Deserializers must reject id
  collisions *as corruption*, not dedup them silently. (universal-weave's
  "hash collision resistance is not supported with rkyv" note is this exact
  seam, honestly labeled.)

## Reading the verdicts

FREE here means: the *merge* preserves the invariant, proved, coordination
never required for it. It does not mean an *operation* cannot violate it
locally (op-validation is the application's job), and it does not price
metadata growth (tombstones, op logs — engineering, not semantics).
-/
import Uwueave.Spec
import Uwueave.Tactics.Core

namespace Uwueave.Weave

open Uwueave Uwueave.Catalog

/-- Active-node flags as a replicated set (node ids; `true` = active on this
replica). The miniature world: root `0`, sibling children `1` and `2`. -/
abbrev ActiveSet := GSet Nat

/-- "The active set is one root-to-leaf path" in the miniature: the root is
active and exactly one of the two siblings is. -/
def IsActivePath (s : ActiveSet) : Prop :=
  s 0 = true ∧ ((s 1 = true ∧ s 2 = false) ∨ (s 2 = true ∧ s 1 = false))

/-- ⚠ **A shared replicated active path is not a CRDT.** Replica A reads branch
1, replica B reads branch 2; each state is a legal path; the merged flag-set
lights both branches. The exact disjunction-trap shape of
`Catalog.or_breaks_iconfluence`, arising from a real loom feature.

Design consequence, not workaround: make activation *per-user* state (a keyed
map, free by `pi_iconfluent`) — which multiplayer looms want anyway, because
"whose cursor wins" is not a question a merge should answer. -/
theorem active_path_not_iconfluent : ¬ IConfluent (S := ActiveSet) IsActivePath := by
  classify

/-- The positive half of the recommendation: per-user activation is free —
whatever per-user invariant you keep, keyed independence lifts it. Stated for
an arbitrary per-user invariant family over LWW-flagged nodes. -/
theorem per_user_activation_free {User : Type} {J : User → Invariant (Nat → LWW)}
    (h : ∀ u, IConfluent (J u)) :
    IConfluent (S := User → Nat → LWW) (fun f => ∀ u, J u (f u)) :=
  pi_iconfluent h

end Uwueave.Weave
