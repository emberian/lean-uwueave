/-
# Uwueave.ORSet — removable sets: observed-remove and causal-length.

The G-Set can only grow, and the 2P-Set can never re-add. The two standard
designs that give a *removable, re-addable* set are classified here:

  * the **OR-Set** (observed-remove, add-wins): every add carries a fresh tag;
    a remove tombstones exactly the tags it has *observed*. An add concurrent
    with a remove survives it — the remove could not have observed the new tag.
  * the **causal-length set** (Yu): membership is the *parity* of a per-element
    counter — odd = present. Add bumps even→odd, remove bumps odd→even; merge
    is pointwise max.

Both get their `MergeState` instances entirely from the lifts (a product of
G-Sets; a Pi of max-Nat) — zero new merge proofs, which is the composition
algebra doing its job. The theorems are about their *presence* invariants, and
they land on opposite sides in an instructive way:

  * OR-Set presence is **not** I-confluent (`orset_present_not_iconfluent`):
    two replicas can each hold the element alive through a different tag while
    tombstoning the other's — the merge is dead. Under tag-scoped rem-after-add
    that clash is causally Live (`CausalReach.orset_clash_joint`). The *scoped*
    guarantee that is actually true (and is what "add-wins" means) is
    `orset_present_survives`: presence through a tag the other side has not
    tombstoned survives.
  * CL-Set presence **is** I-confluent (`clset_present_iconfluent`) — because
    per-key max *selects* one replica's count, so per-key invariants are free
    (`selection_iconfluent`'s pointwise cousin). The arbitration got baked
    into the counter: whoever's causal length is longer wins that element.

Neither is "better"; they price the same square edit differently. OR-Set pays
in tag metadata and gives finer concurrent semantics; CL-Set pays in
arbitration (a longer remote history silently wins) and gives O(1) state per
element.
-/
import Uwueave.Catalog

namespace Uwueave.ORSet

open Uwueave Uwueave.Catalog

/-! ## §1. The OR-Set -/

/-- OR-Set state over elements `α` with tags `τ`: observed adds and observed
removes (tombstones), each a G-Set of (element, tag) pairs. The `MergeState`
is the product-of-GSets instance — inherited, not re-proved. -/
abbrev ORSet (α τ : Type) := GSet (α × τ) × GSet (α × τ)

example (α τ : Type) : MergeState (ORSet α τ) := inferInstance

/-- Presence: some tag witnesses an add that no observed remove has
tombstoned. -/
def Present {α τ : Type} (s : ORSet α τ) (a : α) : Prop :=
  ∃ t : τ, s.1 (a, t) = true ∧ s.2 (a, t) = false

/-- **The add-wins guarantee, correctly scoped.** If `x` holds `a` alive
through tag `t` and `y` has not tombstoned `t`, the merge holds `a` alive
(still through `t`). A remove can only tombstone tags it observed, so an add
concurrent with it survives — this is the theorem "add-wins" refers to. -/
theorem orset_present_survives {α τ : Type} (x y : ORSet α τ) (a : α) (t : τ)
    (hadd : x.1 (a, t) = true) (hx : x.2 (a, t) = false)
    (hy : y.2 (a, t) = false) :
    Present (x ⊔ y) a := by
  refine ⟨t, ?_, ?_⟩
  · show (x.1 (a, t) || y.1 (a, t)) = true
    simp [hadd]
  · show (x.2 (a, t) || y.2 (a, t)) = false
    simp [hx, hy]

/-- ⚠ **Unscoped presence is NOT I-confluent.** The clash: both replicas know
adds `{t₁, t₂}`; replica `x` has tombstoned `t₂` (alive through `t₁`), replica
`y` has tombstoned `t₁` (alive through `t₂`). Each is present; the merge
tombstones both tags and the element is gone.

Reachability (settled): under **tag-scoped rem-after-add** the clash pair *is*
jointly causally reachable — `CausalReach.orset_clash_joint` / `orset_clash_present`.
So this refutation is **Live** for that protocol reading, not LatticeOnly. An
element-wide "remove all observed tags" protocol is a different op shape and is
not modeled here; its causal story may differ. The judgement is still
state-based; op-based add-wins guarantees remain the scoped form
`orset_present_survives`, never bare presence stability. -/
theorem orset_present_not_iconfluent :
    ¬ IConfluent (S := ORSet Nat Nat) (fun s => Present s 0) := by
  intro h
  -- x: adds {(0,1),(0,2)}, tombs {(0,2)} — alive through tag 1.
  -- y: adds {(0,1),(0,2)}, tombs {(0,1)} — alive through tag 2.
  have hbad := h
    (fun p => p == (0, 1) || p == (0, 2), fun p => p == (0, 2))
    (fun p => p == (0, 1) || p == (0, 2), fun p => p == (0, 1))
    ⟨1, by decide, by decide⟩ ⟨2, by decide, by decide⟩
  obtain ⟨t, hadd, htomb⟩ := hbad
  -- The merged adds only contain tags 1 and 2 …
  have ht : t = 1 ∨ t = 2 := by
    simp [prod_merge_fst, gset_mem_merge] at hadd
    omega
  -- … and the merged tombstones contain both.
  cases ht with
  | inl h1 => subst h1; exact absurd htomb (by decide)
  | inr h2 => subst h2; exact absurd htomb (by decide)

/-! ## §2. The causal-length set -/

/-- Causal-length set: per-element causal length, odd = present. Merge is
pointwise max — the Pi-over-max instance, inherited. -/
abbrev CLSet (α : Type) := α → Nat

example (α : Type) : MergeState (CLSet α) := inferInstance

/-- Presence is parity. -/
def CLPresent {α : Type} (s : CLSet α) (a : α) : Prop := s a % 2 = 1

/-- **CL-Set presence IS I-confluent** — per-key max selects one side's count,
so the merged parity is one of the two replicas' parities, and both were odd.
(The pointwise cousin of `selection_iconfluent`.) The flip side is the
arbitration this bakes in: a *longer* remote history wins the element even
when your local history is more recent in wall-clock terms — causal length,
not time, is the tiebreak. -/
theorem clset_present_iconfluent {α : Type} (a : α) :
    IConfluent (S := CLSet α) (fun s => CLPresent s a) := by
  intro x y hx hy
  show Nat.max (x a) (y a) % 2 = 1
  rw [nat_max_def]
  split
  · exact hy
  · exact hx

/-- Absence is I-confluent by the same selection argument — the CL-Set has no
analogue of the OR-Set's both-sides-tombstone anomaly, because there is
nothing element-shaped to lose: the counter *is* the element's whole story. -/
theorem clset_absent_iconfluent {α : Type} (a : α) :
    IConfluent (S := CLSet α) (fun s => s a % 2 = 0) := by
  intro x y hx hy
  show Nat.max (x a) (y a) % 2 = 0
  rw [nat_max_def]
  split
  · exact hy
  · exact hx

/-- ⚠ But *cross-element* invariants fail exactly as they did for LWW pairs:
"if `0` is present then `1` is present" dies when the merge takes `0`'s longer
count from one replica and `1`'s from the other. Same lesson, third structure:
**selection lattices compose into non-selection lattices.** -/
theorem clset_cross_element_not_iconfluent :
    ¬ IConfluent (S := CLSet Nat)
      (fun s => s 0 % 2 = 1 → s 1 % 2 = 1) := by
  intro h
  -- x: {0 ↦ 3, 1 ↦ 1} — both present.  y: {0 ↦ 2, 1 ↦ 2} — both absent-or-even,
  -- invariant vacuously fine. merge: {0 ↦ max(3,2)=3 (odd, PRESENT),
  -- 1 ↦ max(1,2)=2 (even, absent)} — antecedent holds, consequent dies.
  have hbad := h (fun n => if n = 0 then 3 else 1) (fun n => if n = 0 then 2 else 2)
    (by intro _; decide) (by intro hc; simp at hc)
  have h0 : Nat.max 3 2 % 2 = 1 := by decide
  have h1 := hbad (by
    show Nat.max ((if (0:Nat) = 0 then 3 else 1)) ((if (0:Nat) = 0 then 2 else 2)) % 2 = 1
    decide)
  revert h1
  show ¬ (Nat.max ((if (1:Nat) = 0 then 3 else 1)) ((if (1:Nat) = 0 then 2 else 2)) % 2 = 1)
  decide

end Uwueave.ORSet
