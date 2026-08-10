/-
# Uwueave.Segmented — segmented I-confluence: coordination, but only at the seams.

`escalation_witness` is a verdict, not a death sentence. Whittaker–Hellerstein
("Interactive Checks for Coordination Avoidance", VLDB'19) refine the binary
judgement: an invariant that fails I-confluence globally may still hold it
**within segments** of the state space, so that replicas coordinate only to
*cross a segment boundary* and run free inside one. The escrow construction of
`Catalog.lean` §4 is the canonical instance — the segment is the quota
allocation — and this file makes that precise:

  * `SegmentedIConfluent σ I` — merges of same-segment states preserve `I`
    *and stay in the segment*. (The second conjunct is load-bearing: without
    it, one merge could silently teleport replicas across a seam and the
    free-running guarantee would evaporate after a single sync.)
  * `iconfluent_iff_trivially_segmented` — the refinement is conservative:
    plain I-confluence is exactly segmentation with one segment.
  * `budget_not_iconfluent` / `budget_segmented` — the punchline pair, one
    invariant, both verdicts: a budgeted-quota state fails I-confluence
    outright (two legal allocations merge into an over-budget one), yet is
    segmented-confluent over the allocation. Operationally: spends are free,
    re-allocation is the coordination point. That is the escrowed bounded
    counter, now with its budget *inside* the state and the seam *named*.

The design recipe this yields for a weave: when the DSL hands you a `clash`,
look for a `σ` — a projection your application can hold fixed between explicit
coordination events — such that the invariant is segmented over it. The clash
tells you coordination is needed *somewhere*; the segmentation tells you it is
needed *only there*.
-/
import Uwueave.Catalog

namespace Uwueave.Segmented

open Uwueave Uwueave.Catalog

universe u v

/-- **Segmented I-confluence.** Within a fiber of `σ`, merges preserve the
invariant *and the fiber*. Replicas that coordinate only when changing `σ`
therefore run coordination-free between such events — the fiber is closed
under every sync they can perform. -/
def SegmentedIConfluent {S : Type u} {Seg : Type v} [MergeState S]
    (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ x y : S, σ x = σ y → I x → I y → I (x ⊔ y) ∧ σ (x ⊔ y) = σ x

/-- Segmentation is a conservative refinement: with a single segment it *is*
I-confluence. (So every `free` verdict is a degenerate segmentation, and the
interesting content is always in a non-trivial `σ`.) -/
theorem iconfluent_iff_trivially_segmented {S : Type u} [MergeState S]
    (I : Invariant S) :
    IConfluent I ↔ SegmentedIConfluent (fun _ => ()) I := by
  constructor
  · intro h x y _ hx hy
    exact ⟨h x y hx hy, rfl⟩
  · intro h x y hx hy
    exact (h x y rfl hx hy).1

/-! ## The punchline pair: one invariant, both verdicts. -/

/-- Quota-plus-spend state for two devices: the current allocation, and the
per-device spend (both grow-only maps; the `MergeState` is inherited). -/
abbrev QuotaState := (Bool → Nat) × Escrow Bool

/-- The budgeted-escrow invariant: each device within its quota, and the
allocation sums to the budget `B`. (Spelled with explicit conjuncts over the
two devices so every concrete instance below is `decide`-able.) -/
def BudgetInv (B : Nat) : Invariant QuotaState := fun s =>
  (s.2 true ≤ s.1 true ∧ s.2 false ≤ s.1 false)
  ∧ (s.1 true + s.1 false = B)

/-- ⚠ **Globally, the budgeted invariant is not I-confluent** — merging two
*different* legal allocations (10+0 and 0+10 against budget 10) yields the
pointwise-max allocation 10+10, which busts the budget. Re-allocation cannot
be free; this is the seam. -/
theorem budget_not_iconfluent : ¬ IConfluent (BudgetInv 10) := by
  intro h
  exact absurd
    (h ((fun b => if b then 10 else 0), (fun b => if b then 10 else 0))
       ((fun b => if b then 0 else 10), (fun b => if b then 0 else 10))
       (by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide)
       (by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide))
    (fun hbad => by
      have := hbad.2
      revert this
      show ¬ (Nat.max 10 0 + Nat.max 0 10 = 10)
      decide)

/-- **Within an allocation, it is free.** Same invariant, segmented over
`σ = the allocation` (`Prod.fst`): same-quota replicas merge invariant-safely
and stay in the fiber. Spends never wait; only the re-allocation event
coordinates. This discharges the escrow *design* of `Catalog.lean` §4 at the
level Whittaker's framework asks for. -/
theorem budget_segmented (B : Nat) :
    SegmentedIConfluent (S := QuotaState) Prod.fst (BudgetInv B) := by
  intro x y hσ hx hy
  have hq : x.1 ⊔ y.1 = x.1 := by rw [← hσ, merge_idem]
  have ht := congrFun hσ true
  have hf := congrFun hσ false
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · show Nat.max (x.2 true) (y.2 true) ≤ (x.1 ⊔ y.1) true
    rw [hq]
    exact Nat.max_le.mpr ⟨hx.1.1, by have := hy.1.1; omega⟩
  · show Nat.max (x.2 false) (y.2 false) ≤ (x.1 ⊔ y.1) false
    rw [hq]
    exact Nat.max_le.mpr ⟨hx.1.2, by have := hy.1.2; omega⟩
  · show (x.1 ⊔ y.1) true + (x.1 ⊔ y.1) false = B
    rw [hq]
    exact hx.2
  · show x.1 ⊔ y.1 = x.1
    exact hq

end Uwueave.Segmented
