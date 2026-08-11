/-
# Uwueave.ORMap — the observed-remove map: documents are maps, and maps are the hard part.

A loom document is map-shaped: keys to nested values. The classical removable,
re-addable map is the OR-Set construction applied to *keys*, with a value
register riding along per (key, tag) pair — the one-level core of the
Kleppmann–Beresford JSON CRDT map (IEEE TPDS 2017), the map in Automerge /
Riak / AntidoteDB, and the exact place where those systems' semantics
genuinely diverge from one another.

## The state, and why this shape

    ORMap α τ  :=  GSet (α × τ) × GSet (α × τ) × ((α × τ) → LWW)

observed adds, observed removes (tombstones), and one value register per
(key, tag). Two deliberate choices:

  * **Key presence IS the OR-Set** — not an analogue: `present_iff_orset` is
    `Iff.rfl`, and the presence projection commutes with merge (`proj_merge`,
    also `rfl`). Set-level guarantees and set-level anomalies both transfer by
    projection — `ormap_present_not_iconfluent` below is *derived from*
    `orset_present_not_iconfluent`, not re-proved.
  * **Registers are a total function.** At pairs never added the register is
    junk that every view masks; a partial map would need a merge on
    `Option LWW`, i.e. a new proof. The total encoding gets its `MergeState`
    entirely from the existing lifts — product × product × Pi-over-LWW —
    **zero new merge proofs**, which was the design goal and is the
    composition algebra doing its job.

## The results

  * `ormap_get_survives` — the add-wins guarantee at map level, correctly
    scoped: a key alive through a tag the other side has not tombstoned stays
    present *with a readable value* after merge.
  * `ormap_present_not_iconfluent` — unscoped key-presence escalates, inherited
    wholesale from the OR-Set's both-sides-tombstone anomaly.
  * `ormap_doomed_update` — the map-specific anomaly: a nested value update
    concurrent with the key's remove is lost with the tag, even though the
    write is sitting right there in the merged state.
  * `ormap_policy_divergence` — the centerpiece: the *same* merged state gives
    *different* values under the two standard read policies (remove-wins vs
    resurrect). The merge is policy-neutral; the choice lives in the view.

## Honesty notes

  * **Causal delivery**: as in `ORSet.lean`, the presence refutation's state
    pair may not be jointly reachable under causal delivery of operations. The
    doomed-update pair, by contrast, IS reachable under causal delivery — the
    update and the remove are genuinely concurrent, both causally after the
    add — which is why that one is a policy fork and not a delivery artifact.
  * **One level only.** The nested value is a single LWW register. Real
    documents nest maps in maps; that needs an inductive state whose merge is
    defined by recursion, and the composition algebra here is product/Pi only.
  * **No clear/reset operation.** "Remove every observed entry" is its own op
    with its own anomalies (clear vs concurrent insert); it is not modeled.
-/
import Uwueave.ORSet

namespace Uwueave.ORMap

open Uwueave Uwueave.Catalog

/-! ## §1. The state -/

/-- OR-Map state over keys `α` and tags `τ`: observed adds and observed
removes of (key, tag) pairs — exactly the OR-Set — plus one LWW value
register per (key, tag). The `MergeState` is product × product × Pi-over-LWW,
all inherited: zero new merge proofs. -/
abbrev ORMap (α τ : Type) := GSet (α × τ) × GSet (α × τ) × ((α × τ) → LWW)

example (α τ : Type) : MergeState (ORMap α τ) := inferInstance

/-- Key presence: some tag witnesses an add that no observed remove has
tombstoned — verbatim the OR-Set's `Present`, read through the projection. -/
def Present {α τ : Type} (s : ORMap α τ) (k : α) : Prop :=
  ∃ t : τ, s.1 (k, t) = true ∧ s.2.1 (k, t) = false

/-- The presence layer is *definitionally* the OR-Set: `Iff.rfl`. -/
theorem present_iff_orset {α τ : Type} (s : ORMap α τ) (k : α) :
    Present s k ↔ ORSet.Present ((s.1, s.2.1) : ORSet.ORSet α τ) k := Iff.rfl

/-- The presence projection commutes with merge — projecting then merging is
merging then projecting, definitionally. This is what lets set-level
refutations transfer to the map wholesale. -/
theorem proj_merge {α τ : Type} (x y : ORMap α τ) :
    (((x ⊔ y).1, (x ⊔ y).2.1) : ORSet.ORSet α τ) =
      (x.1, x.2.1) ⊔ (y.1, y.2.1) := rfl

/-! ## §2. The remove-wins read, and the scoped positive guarantee -/

/-- The remove-wins read *through one tag*: `some` the register's value iff
that tag is alive (added, un-tombstoned), `none` otherwise. This is the
per-tag primitive both key-level views below aggregate. -/
def getThrough {α τ : Type} (s : ORMap α τ) (k : α) (t : τ) : Option Nat :=
  if s.1 (k, t) = true ∧ s.2.1 (k, t) = false
  then some (s.2.2 (k, t)).val else none

/-- **The add-wins guarantee at map level, correctly scoped** (the map mirror
of `orset_present_survives`). If `x` holds key `k` alive through tag `t` and
`y` has not tombstoned `t`, then after merge the key is still present and the
read through `t` still answers — with one of the two replicas' register
values, the LWW join arbitrating *inside* the surviving tag
(`LWW.join_selects`). A remove can only tombstone tags it observed, so an add
concurrent with it survives, value and all. -/
theorem ormap_get_survives {α τ : Type} (x y : ORMap α τ) (k : α) (t : τ)
    (hadd : x.1 (k, t) = true) (hx : x.2.1 (k, t) = false)
    (hy : y.2.1 (k, t) = false) :
    Present (x ⊔ y) k ∧
    ∃ v : Nat, getThrough (x ⊔ y) k t = some v ∧
      (v = (x.2.2 (k, t)).val ∨ v = (y.2.2 (k, t)).val) := by
  have hcond : (x ⊔ y).1 (k, t) = true ∧ (x ⊔ y).2.1 (k, t) = false := by
    refine ⟨?_, ?_⟩
    · show (x.1 (k, t) || y.1 (k, t)) = true
      simp [hadd]
    · show (x.2.1 (k, t) || y.2.1 (k, t)) = false
      simp [hx, hy]
  refine ⟨⟨t, hcond.1, hcond.2⟩, ((x ⊔ y).2.2 (k, t)).val, ?_, ?_⟩
  · show (if (x ⊔ y).1 (k, t) = true ∧ (x ⊔ y).2.1 (k, t) = false
        then some ((x ⊔ y).2.2 (k, t)).val else none) =
        some ((x ⊔ y).2.2 (k, t)).val
    exact if_pos hcond
  · rcases LWW.join_selects (x.2.2 (k, t)) (y.2.2 (k, t)) with h | h
    · exact Or.inl (congrArg LWW.val h)
    · exact Or.inr (congrArg LWW.val h)

/-! ## §3. Unscoped key-presence escalates — inherited, not re-proved -/

/-- ⚠ **Unscoped key-presence is NOT I-confluent** — the OR-Set's
both-sides-tombstone anomaly, verbatim at map level. The proof is a
*derivation*: any counterexample-free map presence would project (via
`proj_merge`) to counterexample-free set presence, refuted by
`orset_present_not_iconfluent`. The inherited concrete clash: both replicas
know adds `{(k,t₁), (k,t₂)}`; `x` tombstoned `t₂`, `y` tombstoned `t₁`; each
holds the key, the merge holds a tombstone for every tag. Registers play no
part — trivial everywhere — which is the point: no value layer can rescue a
presence layer.

Reachability: same as `ORSet` — under tag-scoped rem-after-add the projected
clash is jointly causally reachable (`CausalReach.ormap_clash_joint`); **Live**
for that reading. Scoped `ormap_get_survives` remains the operational guarantee;
bare presence stability is not. -/
theorem ormap_present_not_iconfluent :
    ¬ IConfluent (S := ORMap Nat Nat) (fun s => Present s 0) := by
  intro h
  apply ORSet.orset_present_not_iconfluent
  intro u v hu hv
  exact h (u.1, u.2, fun _ => (⟨0, 0⟩ : LWW))
    (v.1, v.2, fun _ => (⟨0, 0⟩ : LWW)) hu hv

/-! ## §4. The doomed update — the map-specific anomaly -/

/-- Replica `x`: key `0` alive through tag `1`, and `x` has just *updated* the
nested value — a fresh write `⟨ts 2, val 99⟩` over the initial `⟨ts 1, 10⟩`. -/
def xUpd : ORMap Nat Nat :=
  (fun p => p == (0, 1), fun _ => false,
   fun p => if p == (0, 1) then ⟨2, 99⟩ else ⟨0, 0⟩)

/-- Replica `y`: observed the same add of tag `1` (register still at the
initial `⟨1, 10⟩` — it never saw `x`'s update) and removed the key,
tombstoning every tag it observed. -/
def yTomb : ORMap Nat Nat :=
  (fun p => p == (0, 1), fun p => p == (0, 1),
   fun p => if p == (0, 1) then ⟨1, 10⟩ else ⟨0, 0⟩)

/-- ⚠ **The doomed update.** `x` updates the value at `(k, t)`; concurrently
`y` removes the key, tombstoning `t`. Both are causally downstream of the add,
so — unlike §3's pair — causal delivery *cannot* rule this pair out: it is a
genuine policy fork, not a delivery artifact. Under remove-wins-per-tag
semantics the merge kills the update with its tag: `x` read its fresh `99`
locally, `y` read `none` locally, and the merged map answers `none` — while
conjunct five shows the `⟨2, 99⟩` write sitting *in the merged state*,
invisible to the view. The update is doomed, not dropped: state-layer merge
lost nothing, the read policy priced it at zero.

This is the anomaly every JSON-CRDT design must decide: Kleppmann–Beresford
(IEEE TPDS 2017) keep concurrent updates alive (their map favors updates over
removes); Kleppmann–Gomes–Mulligan–Beresford, "OpSets" (arXiv:1805.04263)
specify map semantics where exactly this choice point is made explicit; and
Da–Kleppmann (PaPoC 2024) meet it again when a move races the removal of the
key being moved into. §5 prices both answers on one state. -/
theorem ormap_doomed_update :
    getThrough xUpd 0 1 = some 99 ∧
    getThrough yTomb 0 1 = none ∧
    getThrough (xUpd ⊔ yTomb) 0 1 = none ∧
    ¬ Present (xUpd ⊔ yTomb) 0 ∧
    (xUpd ⊔ yTomb).2.2 (0, 1) = ⟨2, 99⟩ := by
  refine ⟨by decide, by decide, by decide, ?_, by decide⟩
  intro ⟨t, hadd, htomb⟩
  have ht : t = 1 := by
    simp [xUpd, yTomb, gset_mem_merge] at hadd
    omega
  subst ht
  exact absurd htomb (by decide)

/-! ## §5. The centerpiece: one merged state, two standard views, two answers.

The merge is policy-neutral — it is the same inherited lattice however you
read it. The remove/update race of §4 is decided by the *view*, and the two
standard policies answer it oppositely. Both are pure functions of the same
state, both ship in real systems (remove-wins and update-wins maps are both
offered by AntidoteDB; Automerge's map is update-flavored), and neither is
"the correct one" — they price the doomed update differently:

  * **remove-wins** (`RWVisible`): a register counts only while its own tag is
    alive. The doomed write is lost deterministically — the remover's intent
    is honored in full, the updater's write silently dies.
  * **resurrect** (`ResVisible`): a register counts as long as the *key*
    survives at all. The doomed write outlives the tag it was addressed
    through — the updater's intent is honored, and the remover watches a
    value it deleted come back through a sibling tag.

`ormap_policy_divergence` exhibits both verdicts on one merged state; the two
negative conjuncts make the disagreement exact, not a choice among ties.
`ormap_policies_agree_without_removes` bounds the blast radius: on keys no
remove has touched, the policies are the same view. -/

/-- Remove-wins view, key level: register `r` is the value of `k` iff `r`
sits at a live (added, un-tombstoned) tag and no live tag's register beats it
— the LWW-max across live tags, the aggregation of `getThrough`. -/
def RWVisible {α τ : Type} (s : ORMap α τ) (k : α) (r : LWW) : Prop :=
  (∃ t, s.1 (k, t) = true ∧ s.2.1 (k, t) = false ∧ s.2.2 (k, t) = r) ∧
  ∀ t, s.1 (k, t) = true → s.2.1 (k, t) = false → ¬ LWW.Lt r (s.2.2 (k, t))

/-- Resurrect (add-wins-flavored) view, key level: `k` is visible iff ANY
live tag exists, and its value is the LWW-max across *every added* tag's
register — a tombstone kills a contribution only by killing the whole key. -/
def ResVisible {α τ : Type} (s : ORMap α τ) (k : α) (r : LWW) : Prop :=
  Present s k ∧
  (∃ t, s.1 (k, t) = true ∧ s.2.2 (k, t) = r) ∧
  ∀ t, s.1 (k, t) = true → ¬ LWW.Lt r (s.2.2 (k, t))

/-- Replica `x` for the divergence: key `0` added twice (tags `1` and `2`,
both initially `⟨1, 10⟩`), and `x` has freshly written `⟨2, 99⟩` through
tag `2`'s slot. -/
def xWrite : ORMap Nat Nat :=
  (fun p => p == (0, 1) || p == (0, 2), fun _ => false,
   fun p => if p == (0, 2) then ⟨2, 99⟩
            else if p == (0, 1) then ⟨1, 10⟩ else ⟨0, 0⟩)

/-- Replica `y` for the divergence: same two adds, registers still initial,
and `y` has removed the tag-`2` instance — concurrently with `x`'s write,
which it never saw. -/
def yRemove : ORMap Nat Nat :=
  (fun p => p == (0, 1) || p == (0, 2), fun p => p == (0, 2),
   fun p => if p == (0, 1) || p == (0, 2) then ⟨1, 10⟩ else ⟨0, 0⟩)

/-- The merged state both §5 theorems read: adds `{(0,1), (0,2)}`, tombstone
`{(0,2)}`, registers `(0,1) ↦ ⟨1,10⟩` and `(0,2) ↦ ⟨2,99⟩`. -/
def mDiv : ORMap Nat Nat := xWrite ⊔ yRemove

private theorem mDiv_added {t : Nat} (h : mDiv.1 (0, t) = true) :
    t = 1 ∨ t = 2 := by
  simp [mDiv, xWrite, yRemove, gset_mem_merge] at h
  omega

/-- ⚠ **Policy divergence, exactly.** On the single merged state `mDiv`, the
remove-wins view shows `⟨1, 10⟩` and *refuses* `⟨2, 99⟩` (the fresh write
died with its tombstoned tag; the stale sibling survives it), while the
resurrect view shows `⟨2, 99⟩` and *refuses* `⟨1, 10⟩` (the fresh write
outlives its tag through the key's surviving sibling; the stale value is
beaten by it). Same state. Different value. The merge never chose — the view
did, and each policy is the other's anomaly: remove-wins loses a write the
user watched succeed, resurrect revives a value the user watched die. A map
CRDT does not dodge this choice by being "conflict-free"; it only decides
*where* the choice is made visible. -/
theorem ormap_policy_divergence :
    RWVisible mDiv 0 ⟨1, 10⟩ ∧ ¬ RWVisible mDiv 0 ⟨2, 99⟩ ∧
    ResVisible mDiv 0 ⟨2, 99⟩ ∧ ¬ ResVisible mDiv 0 ⟨1, 10⟩ := by
  refine ⟨⟨⟨1, by decide, by decide, by decide⟩, ?_⟩, ?_, ?_, ?_⟩
  · -- no live register beats ⟨1,10⟩: the only live tag is 1, holding ⟨1,10⟩.
    intro t hadd htomb
    rcases mDiv_added hadd with h | h
    · subst h; decide
    · subst h; exact absurd htomb (by decide)
  · -- remove-wins refuses ⟨2,99⟩: it sits at no live tag.
    intro ⟨⟨t, hadd, htomb, hreg⟩, _⟩
    rcases mDiv_added hadd with h | h
    · subst h; exact absurd hreg (by decide)
    · subst h; exact absurd htomb (by decide)
  · -- resurrect shows ⟨2,99⟩: key alive through tag 1, max over both registers.
    refine ⟨⟨1, by decide, by decide⟩, ⟨2, by decide, by decide⟩, ?_⟩
    intro t hadd
    rcases mDiv_added hadd with h | h <;> (subst h; decide)
  · -- resurrect refuses ⟨1,10⟩: the added register ⟨2,99⟩ beats it.
    intro ⟨_, _, hmax⟩
    exact hmax 2 (by decide) (by decide)

/-- **The divergence is confined to removal-touched keys.** On a key no
remove has ever tombstoned, live tags and added tags coincide, so the two
views are the *same* relation. The policy fork of `ormap_policy_divergence`
is exactly the price of the remove/update race — not a background disagreement
about ordinary reading. -/
theorem ormap_policies_agree_without_removes {α τ : Type} (s : ORMap α τ)
    (k : α) (hclean : ∀ t, s.2.1 (k, t) = false) (r : LWW) :
    RWVisible s k r ↔ ResVisible s k r := by
  constructor
  · intro ⟨⟨t, hadd, _, hreg⟩, hmax⟩
    exact ⟨⟨t, hadd, hclean t⟩, ⟨t, hadd, hreg⟩,
      fun t' hadd' => hmax t' hadd' (hclean t')⟩
  · intro ⟨_, ⟨t, hadd, hreg⟩, hmax⟩
    exact ⟨⟨t, hadd, hclean t, hreg⟩, fun t' hadd' _ => hmax t' hadd'⟩

end Uwueave.ORMap
