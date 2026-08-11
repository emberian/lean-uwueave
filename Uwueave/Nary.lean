/-
# Uwueave.Nary — n-ary carriers for the Catalog / Segmented Bool demos.

`Catalog.lean` and `Segmented.lean` state several keystone results over a
two-replica carrier (`ι = Bool`). Schema authors hit three-or-more devices
first; this file is the finite-enumeration generalisation those Bool theorems
instantiate from.

What is generalised, and how:

  * `net_enum enum c` — PN-counter net over an arbitrary enumeration of `ι`
    (list sum of increments minus list sum of decrements). Catalog's `net`
    is definitionally the case `enum = [true, false]` (`net_eq_net_enum`).
  * `pncounter_nonneg_not_iconfluent_enum` — non-negative balance is still
    not I-confluent whenever the enum contains two distinct keys; the Bool
    theorem is the instance at `true ≠ false` (`pncounter_nonneg_not_iconfluent_bool`).
  * `escrow_global_bound_enum` — sum of spends ≤ sum of quotas over an
    enumeration; Catalog's two-replica add is `enum = [true, false]`
    (`escrow_global_bound_of_enum`).
  * `BudgetInvN` / `QuotaStateN` — n-ary budgeted-escrow invariant
    (`∀ i, spend i ≤ alloc i` and `sum_enum alloc = B`), with the segmented
    positive result `budget_segmented_enum` and the global refutation
    `budget_not_iconfluent_enum`. The Segmented Bool pair falls out via
    `budgetInv_bool_iff` / `budget_segmented_bool`.

## What this file does NOT do

  * **No new `MergeState` proofs.** `GCounter ι`, `PNCounter ι`,
    `Escrow ι`, and `QuotaStateN ι` all inherit product / pi / `Nat.max`
    from `Confluence.lean` + `Catalog.lean`. The zero-new-merge-proofs
    discipline of the parent files is preserved.
  * **No infinite-carrier sums.** Every global quantity is a list fold over
    an explicit enumeration. Completeness (`∀ i, i ∈ enum`) and nodup are
    separate hypotheses; without them the sum is still well-defined but
    counts only the listed keys (with multiplicity if not nodup).
  * **No mathlib / Finset.** Same core-only substrate as Catalog.
  * **No re-proof of the Bool theorems inside Catalog / Segmented.** Those
    files are frozen; this module recovers them as specialisations.

Honest scope: this is the finite-support / enumerated-device generalisation,
not a theory of infinite replicas or measure-theoretic balance.
-/
import Uwueave.Catalog
import Uwueave.Segmented

namespace Uwueave.Nary

open Uwueave Uwueave.Catalog Uwueave.Segmented

/-! ## §0. Enumeration kit -/

/-- The standard two-replica enumeration. Complete and nodup for `Bool`. -/
def boolEnum : List Bool := [true, false]

theorem boolEnum_nodup : boolEnum.Nodup := by decide

theorem boolEnum_complete : ∀ b : Bool, b ∈ boolEnum := by
  intro b; cases b <;> decide

/-- Pointwise inequality of maps lifts through list-sum. -/
theorem sum_map_le_sum_map {ι : Type} (f g : ι → Nat) :
    ∀ (l : List ι), (∀ i ∈ l, f i ≤ g i) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp [List.map_nil, List.sum_nil]
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self)
      (sum_map_le_sum_map f g l (fun i hi => h i (List.mem_cons_of_mem a hi)))

/-! ## §1. PN-counter net over a finite enumeration -/

/-- Net value of a PN-counter summed over an enumeration of the carrier.
Increments minus decrements, in `Int` so overdraft is representable. When
`enum` is complete and nodup this is the global balance; otherwise it is the
balance restricted to the listed keys. -/
def net_enum {ι : Type} (enum : List ι) (c : PNCounter ι) : Int :=
  ((enum.map c.1).sum : Int) - ((enum.map c.2).sum : Int)

/-- Catalog's two-replica `net` is exactly `net_enum boolEnum`. -/
theorem net_eq_net_enum (c : PNCounter Bool) :
    net c = net_enum boolEnum c := by
  simp [net, net_enum, boolEnum, List.map, List.sum_cons, List.sum_nil]

/-- ⚠ **`net_enum ≥ 0` is NOT I-confluent whenever the enum has two distinct
keys.** Both replicas are credited 10 on key `i`; replica A spends 10 on `i`,
replica B spends 10 on `j`; each is individually legal (net 0); the merge has
spent 20 against 10 (net −10). Same Bailis square as
`Catalog.pncounter_nonneg_not_iconfluent`, now for any carrier with
`|support| ≥ 2`. -/
theorem pncounter_nonneg_not_iconfluent_enum {ι : Type} [DecidableEq ι]
    (i j : ι) (hne : i ≠ j) :
    ¬ IConfluent (S := PNCounter ι)
      (fun c => 0 ≤ net_enum [i, j] c) := by
  intro h
  have hji : j ≠ i := Ne.symm hne
  let p10 : ι → Nat := fun k => if k = i then 10 else 0
  let dA  : ι → Nat := fun k => if k = i then 10 else 0
  let dB  : ι → Nat := fun k => if k = j then 10 else 0
  let x : PNCounter ι := (p10, dA)
  let y : PNCounter ι := (p10, dB)
  have p10_i : p10 i = 10 := by simp [p10]
  have p10_j : p10 j = 0 := by simp [p10, hji]
  have dA_i : dA i = 10 := by simp [dA]
  have dA_j : dA j = 0 := by simp [dA, hji]
  have dB_i : dB i = 0 := by simp [dB, hne]
  have dB_j : dB j = 10 := by simp [dB]
  have hx : 0 ≤ net_enum [i, j] x := by
    simp only [net_enum, x, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      p10_i, p10_j, dA_i, dA_j]
    decide
  have hy : 0 ≤ net_enum [i, j] y := by
    simp only [net_enum, y, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      p10_i, p10_j, dB_i, dB_j]
    decide
  have hbad : ¬ 0 ≤ net_enum [i, j] (x ⊔ y) := by
    have max_i : Nat.max (dA i) (dB i) = 10 := by simp [dA_i, dB_i]
    have max_j : Nat.max (dA j) (dB j) = 10 := by simp [dA_j, dB_j]
    change ¬ 0 ≤
      ((Nat.max (p10 i) (p10 i) + (Nat.max (p10 j) (p10 j) + 0) : Nat) : Int) -
      ((Nat.max (dA i) (dB i) + (Nat.max (dA j) (dB j) + 0) : Nat) : Int)
    simp only [p10_i, p10_j, max_i, max_j, Nat.max_self]
    decide
  exact hbad (h x y hx hy)

/-- Catalog's `pncounter_nonneg_not_iconfluent`, recovered by specialising the
n-ary refutation at `true ≠ false` and rewriting through `net_eq_net_enum`. -/
theorem pncounter_nonneg_not_iconfluent_bool :
    ¬ IConfluent (S := PNCounter Bool) (fun c => 0 ≤ net c) := by
  have h := pncounter_nonneg_not_iconfluent_enum (ι := Bool) true false (by decide)
  intro H
  apply h
  intro x y hx hy
  have hx' : 0 ≤ net x := by
    show 0 ≤ net x
    rwa [net_eq_net_enum]
  have hy' : 0 ≤ net y := by
    show 0 ≤ net y
    rwa [net_eq_net_enum]
  have hm : 0 ≤ net (x ⊔ y) := H x y hx' hy'
  show 0 ≤ net_enum boolEnum (x ⊔ y)
  rwa [← net_eq_net_enum]

/-! ## §2. Escrow global bound over an enumeration -/

/-- **Global bound from local bounds, n-ary.** Sum of spends over `enum` is
≤ sum of quotas over `enum`, given a local bound on every listed key. This is
Catalog §4's "sum the quotas" step with the two-replica `+` replaced by a list
fold. -/
theorem escrow_global_bound_enum {ι : Type} (q : ι → Nat) (f : Escrow ι)
    (enum : List ι) (h : ∀ i ∈ enum, f i ≤ q i) :
    (enum.map f).sum ≤ (enum.map q).sum :=
  sum_map_le_sum_map f q enum h

/-- Catalog's `escrow_global_bound` is the enum theorem at `boolEnum`. -/
theorem escrow_global_bound_of_enum (q : Bool → Nat) (f : Escrow Bool)
    (h : ∀ i, f i ≤ q i) : f true + f false ≤ q true + q false := by
  simpa [boolEnum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] using
    (escrow_global_bound_enum q f boolEnum (fun i _ => h i))

/-! ## §3. N-ary budgeted escrow (Segmented generalisation) -/

/-- Quota-plus-spend state for an arbitrary device carrier. `MergeState` is the
product of two pointwise-`max` maps — free from Confluence. -/
abbrev QuotaStateN (ι : Type) := (ι → Nat) × Escrow ι

/-- N-ary budgeted-escrow invariant: every device within its quota, and the
allocation sums to budget `B` over the enumeration. -/
def BudgetInvN {ι : Type} (enum : List ι) (B : Nat) : Invariant (QuotaStateN ι) :=
  fun s => (∀ i, s.2 i ≤ s.1 i) ∧ (enum.map s.1).sum = B

/-- ⚠ **Globally, the n-ary budgeted invariant is not I-confluent** whenever
the enum has two distinct keys — merging two different legal allocations
(10 on `i` and 10 on `j` against budget 10) yields the pointwise-max
allocation whose enum-sum is 20. Re-allocation is the seam. -/
theorem budget_not_iconfluent_enum {ι : Type} [DecidableEq ι]
    (i j : ι) (hne : i ≠ j) :
    ¬ IConfluent (BudgetInvN (ι := ι) [i, j] 10) := by
  intro h
  have hji : j ≠ i := Ne.symm hne
  let aA : ι → Nat := fun k => if k = i then 10 else 0
  let aB : ι → Nat := fun k => if k = j then 10 else 0
  let sA : ι → Nat := fun k => if k = i then 10 else 0
  let sB : ι → Nat := fun k => if k = j then 10 else 0
  let x : QuotaStateN ι := (aA, sA)
  let y : QuotaStateN ι := (aB, sB)
  have aA_i : aA i = 10 := by simp [aA]
  have aA_j : aA j = 0 := by simp [aA, hji]
  have aB_i : aB i = 0 := by simp [aB, hne]
  have aB_j : aB j = 10 := by simp [aB]
  have hx : BudgetInvN [i, j] 10 x := by
    constructor
    · intro k
      change sA k ≤ aA k
      by_cases hk : k = i
      · subst hk; simp [sA, aA]
      · have hs : sA k = 0 := by simp [sA, hk]
        omega
    · simp only [x, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, aA_i, aA_j]
      decide
  have hy : BudgetInvN [i, j] 10 y := by
    constructor
    · intro k
      change sB k ≤ aB k
      by_cases hk : k = j
      · subst hk; simp [sB, aB]
      · have hs : sB k = 0 := by simp [sB, hk]
        omega
    · simp only [y, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, aB_i, aB_j]
      decide
  have hbad : ¬ BudgetInvN [i, j] 10 (x ⊔ y) := by
    intro ⟨_, hsum⟩
    change (List.map (fun k => Nat.max (aA k) (aB k)) [i, j]).sum = 10 at hsum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    have mi : Nat.max (aA i) (aB i) = 10 := by simp [aA_i, aB_i]
    have mj : Nat.max (aA j) (aB j) = 10 := by simp [aA_j, aB_j]
    simp only [mi, mj] at hsum
    exact absurd hsum (by decide)
  exact hbad (h x y hx hy)

/-- Bool instance of the n-ary budget refutation. -/
theorem budget_not_iconfluent_bool :
    ¬ IConfluent (BudgetInvN (ι := Bool) boolEnum 10) :=
  budget_not_iconfluent_enum true false (by decide)

/-- **Within an allocation, the n-ary budget is free.** Segmented over
`σ = Prod.fst` (the allocation): same-quota replicas merge invariant-safely
and stay in the fibre. Spends never wait; only re-allocation coordinates.
`MergeState` proofs are inherited — only the invariant argument is new. -/
theorem budget_segmented_enum {ι : Type} (enum : List ι) (B : Nat) :
    SegmentedIConfluent (S := QuotaStateN ι) Prod.fst (BudgetInvN enum B) := by
  intro x y hσ hx hy
  have hq : x.1 ⊔ y.1 = x.1 := by rw [← hσ, merge_idem]
  constructor
  · constructor
    · intro i
      show Nat.max (x.2 i) (y.2 i) ≤ (x.1 ⊔ y.1) i
      rw [hq]
      have hyi : y.2 i ≤ x.1 i := by
        have hle := hy.1 i
        have heq : y.1 i = x.1 i := congrFun hσ.symm i
        omega
      exact Nat.max_le.mpr ⟨hx.1 i, hyi⟩
    · show (enum.map (x.1 ⊔ y.1)).sum = B
      have : enum.map (x.1 ⊔ y.1) = enum.map x.1 := by rw [hq]
      rw [this]
      exact hx.2
  · exact hq

/-- Segmented's `BudgetInv` is propositionally `BudgetInvN boolEnum`. -/
theorem budgetInv_bool_iff (B : Nat) (s : QuotaState) :
    BudgetInv B s ↔ BudgetInvN boolEnum B s := by
  constructor
  · intro ⟨⟨ht, hf⟩, hsum⟩
    constructor
    · intro i; cases i <;> assumption
    · simpa [boolEnum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] using hsum
  · intro ⟨hloc, hsum⟩
    constructor
    · exact ⟨hloc true, hloc false⟩
    · simpa [boolEnum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] using hsum

/-- `Segmented.budget_segmented`, recovered: same `σ`, equivalent `I` at the
Bool enum. -/
theorem budget_segmented_bool (B : Nat) :
    SegmentedIConfluent (S := QuotaState) Prod.fst (BudgetInv B) := by
  intro x y hσ hx hy
  have hxN : BudgetInvN boolEnum B x := (budgetInv_bool_iff B x).mp hx
  have hyN : BudgetInvN boolEnum B y := (budgetInv_bool_iff B y).mp hy
  have ⟨hI, hσ'⟩ := budget_segmented_enum (ι := Bool) boolEnum B x y hσ hxN hyN
  exact ⟨(budgetInv_bool_iff B (x ⊔ y)).mpr hI, hσ'⟩

end Uwueave.Nary
