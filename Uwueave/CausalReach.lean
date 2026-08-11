/-
# Uwueave.CausalReach — op-based causal cuts (JOB 2, rewritten).

## Model

A **history** is a finite op type with a decidable happens-before preorder `hb`.
A **cut** is membership downward-closed under `hb`. **Joint reachability**: one
history, two cuts, an interpretation of cuts into datatype states.

Dual of `Necessity.ReachableClash` (join-sync local runs). Here state =
interpretation of a causal cut.

## Scope

  * No networks, Byzantine issuers, or fairness (`Liveness.lean`).
  * Content-addressing is **not** cut theory: it restricts which ops may be
    *issued* (id = hash(payload)). Uniqueness under CA is discharged elsewhere
    (collision extraction), not by a status enum here.

## Settlements

  * OR-Set catalog clash is jointly reachable under **tag-scoped rem-after-add**
    — the ORSet docstring's "may not under causal delivery" does not hold for
    that protocol reading (Live here). Element-wide remove-all-observed is a
    different protocol, not modeled.
  * Concurrent two-op clashes (at-most-one shape, edges, PN spends, budget) Live.
  * Free-id Sequence dup *fragments* jointly reachable; CA is out of band.
  * Illegal cuts (rem without add) rejected by downward-closure.

Clash states are **definitionally** cut interpretations — no parallel
encodings to drift. No status enums, no `rfl` of named constants as "theorems."
-/
import Uwueave.ORSet
import Uwueave.ORMap
import Uwueave.Acyclicity
import Uwueave.Segmented
import Uwueave.Catalog

namespace Uwueave.CausalReach

open Uwueave Uwueave.Catalog Uwueave.ORSet

/-! ## §1. Histories and cuts -/

structure FinHistory (Op : Type) where
  hb : Op → Op → Bool
  hb_refl : ∀ o, hb o o = true
  hb_trans : ∀ a b c, hb a b = true → hb b c = true → hb a c = true

structure Cut {Op : Type} (H : FinHistory Op) where
  mem : Op → Bool
  down : ∀ a b, mem b = true → H.hb a b = true → mem a = true

def Joint {Op σ : Type} (H : FinHistory Op) (interp : Cut H → σ) (s₁ s₂ : σ) : Prop :=
  ∃ c₁ c₂ : Cut H, interp c₁ = s₁ ∧ interp c₂ = s₂

/-- Fully concurrent history: `hb` is equality. -/
def eqHistory (Op : Type) [DecidableEq Op] : FinHistory Op where
  hb := fun a b => a == b
  hb_refl := fun _ => by simp
  hb_trans := fun a b c h1 h2 => by
    simp only [beq_iff_eq] at h1 h2 ⊢
    exact h1.trans h2

theorem eqHistory_down (Op : Type) [DecidableEq Op] (mem : Op → Bool) :
    ∀ a b : Op, mem b = true → (eqHistory Op).hb a b = true → mem a = true := by
  intro a b hm hh
  simp only [eqHistory, beq_iff_eq] at hh
  exact hh ▸ hm

/-! ## §2. OR-Set presence clash -/

inductive OR4 | a1 | a2 | r1 | r2
  deriving DecidableEq, Repr

def or4hb (a b : OR4) : Bool :=
  (a == b) || (a == .a1 && b == .r1) || (a == .a2 && b == .r2)

def or4H : FinHistory OR4 where
  hb := or4hb
  hb_refl := fun o => by cases o <;> decide
  hb_trans := fun a b c h1 h2 => by
    cases a <;> cases b <;> cases c <;> simp [or4hb] at h1 h2 ⊢

def memX : OR4 → Bool
  | .a1 | .a2 | .r2 => true
  | .r1 => false

def memY : OR4 → Bool
  | .a1 | .a2 | .r1 => true
  | .r2 => false

theorem memX_down (a b : OR4) (hm : memX b = true) (hh : or4hb a b = true) :
    memX a = true := by
  cases a <;> cases b <;> simp [memX, or4hb] at hm hh ⊢

theorem memY_down (a b : OR4) (hm : memY b = true) (hh : or4hb a b = true) :
    memY a = true := by
  cases a <;> cases b <;> simp [memY, or4hb] at hm hh ⊢

def cutX : Cut or4H where
  mem := memX
  down := memX_down

def cutY : Cut or4H where
  mem := memY
  down := memY_down

def or4Interp (c : Cut or4H) : ORSet Nat Nat :=
  (fun p => (p.1 == 0 && p.2 == 1 && c.mem .a1) || (p.1 == 0 && p.2 == 2 && c.mem .a2),
   fun p => (p.1 == 0 && p.2 == 1 && c.mem .r1) || (p.1 == 0 && p.2 == 2 && c.mem .r2))

/-- Clash states are the cut interpretations (definitional). -/
def orClashL : ORSet Nat Nat := or4Interp cutX
def orClashR : ORSet Nat Nat := or4Interp cutY

theorem orset_clash_joint : Joint or4H or4Interp orClashL orClashR :=
  ⟨cutX, cutY, rfl, rfl⟩

theorem orClashL_shape :
    orClashL.1 (0, 1) = true ∧ orClashL.1 (0, 2) = true ∧
    orClashL.2 (0, 1) = false ∧ orClashL.2 (0, 2) = true := by
  simp [orClashL, or4Interp, cutX, memX]

theorem orClashR_shape :
    orClashR.1 (0, 1) = true ∧ orClashR.1 (0, 2) = true ∧
    orClashR.2 (0, 1) = true ∧ orClashR.2 (0, 2) = false := by
  simp [orClashR, or4Interp, cutY, memY]

theorem orset_clash_present :
    Present orClashL 0 ∧ Present orClashR 0 ∧ ¬ Present (orClashL ⊔ orClashR) 0 := by
  refine ⟨⟨1, orClashL_shape.1, orClashL_shape.2.2.1⟩,
          ⟨2, orClashR_shape.2.1, orClashR_shape.2.2.2⟩, ?_⟩
  intro ⟨t, hadd, htomb⟩
  -- expand membership at (0,t) after merge
  have hL := orClashL_shape
  have hR := orClashR_shape
  match t with
  | 0 =>
    simp [orClashL, orClashR, or4Interp, cutX, cutY, memX, memY, gset_mem_merge] at hadd
  | 1 =>
    simp [orClashL, orClashR, or4Interp, cutX, cutY, memX, memY, gset_mem_merge] at htomb
  | 2 =>
    simp [orClashL, orClashR, or4Interp, cutX, cutY, memX, memY, gset_mem_merge] at htomb
  | _ + 3 =>
    simp [orClashL, orClashR, or4Interp, cutX, cutY, memX, memY, gset_mem_merge] at hadd

/-- OR-Map: same cuts, trivial registers. -/
theorem ormap_clash_joint :
    Joint or4H
      (fun c =>
        let s := or4Interp c
        ((s.1, s.2, fun _ => (⟨0, 0⟩ : LWW)) : ORMap.ORMap Nat Nat))
      (orClashL.1, orClashL.2, fun _ => (⟨0, 0⟩ : LWW))
      (orClashR.1, orClashR.2, fun _ => (⟨0, 0⟩ : LWW)) :=
  ⟨cutX, cutY, rfl, rfl⟩

/-- Illegal: rem without its add is not a cut. -/
theorem rem_without_add_not_a_cut :
    ¬ ∃ c : Cut or4H, c.mem .r1 = true ∧ c.mem .a1 = false := by
  intro ⟨c, hr, ha⟩
  have := c.down .a1 .r1 hr (by decide : or4H.hb .a1 .r1 = true)
  simp [ha] at this

/-! ## §3. Concurrent two-op miniatures (definitional clash states) -/

inductive TwoAdd | add0 | add1
  deriving DecidableEq

def twoAddH : FinHistory TwoAdd := eqHistory TwoAdd

def cutAdd0 : Cut twoAddH where
  mem := fun o => o == .add0
  down := eqHistory_down TwoAdd (fun o => o == .add0)

def cutAdd1 : Cut twoAddH where
  mem := fun o => o == .add1
  down := eqHistory_down TwoAdd (fun o => o == .add1)

def twoAddInterp (c : Cut twoAddH) : GSet Nat :=
  fun n => (n == 0 && c.mem .add0) || (n == 1 && c.mem .add1)

def gset0 : GSet Nat := twoAddInterp cutAdd0
def gset1 : GSet Nat := twoAddInterp cutAdd1

theorem atMostOne_joint : Joint twoAddH twoAddInterp gset0 gset1 :=
  ⟨cutAdd0, cutAdd1, rfl, rfl⟩

inductive TwoEdge | e01 | e10
  deriving DecidableEq

def twoEdgeH : FinHistory TwoEdge := eqHistory TwoEdge

def cutE01 : Cut twoEdgeH where
  mem := fun o => o == .e01
  down := eqHistory_down TwoEdge (fun o => o == .e01)

def cutE10 : Cut twoEdgeH where
  mem := fun o => o == .e10
  down := eqHistory_down TwoEdge (fun o => o == .e10)

def edgeInterp (c : Cut twoEdgeH) : Acyclicity.EdgeGraph :=
  fun e =>
    (e.1 == 0 && e.2 == 1 && c.mem .e01) || (e.1 == 1 && e.2 == 0 && c.mem .e10)

def edge01 : Acyclicity.EdgeGraph := edgeInterp cutE01
def edge10 : Acyclicity.EdgeGraph := edgeInterp cutE10

theorem acyclicity_joint : Joint twoEdgeH edgeInterp edge01 edge10 :=
  ⟨cutE01, cutE10, rfl, rfl⟩

inductive TwoSpend | spendA | spendB
  deriving DecidableEq

def twoSpendH : FinHistory TwoSpend := eqHistory TwoSpend

def cutSpendA : Cut twoSpendH where
  mem := fun o => o == .spendA
  down := eqHistory_down TwoSpend (fun o => o == .spendA)

def cutSpendB : Cut twoSpendH where
  mem := fun o => o == .spendB
  down := eqHistory_down TwoSpend (fun o => o == .spendB)

def pnInterp (c : Cut twoSpendH) : PNCounter Bool :=
  (fun b => if b then 10 else 0,
   fun b => if b then (if c.mem .spendA then 10 else 0)
            else (if c.mem .spendB then 10 else 0))

def pnA : PNCounter Bool := pnInterp cutSpendA
def pnB : PNCounter Bool := pnInterp cutSpendB

theorem pncounter_joint : Joint twoSpendH pnInterp pnA pnB :=
  ⟨cutSpendA, cutSpendB, rfl, rfl⟩

inductive TwoAlloc | allocA | allocB
  deriving DecidableEq

def twoAllocH : FinHistory TwoAlloc := eqHistory TwoAlloc

def cutAllocA : Cut twoAllocH where
  mem := fun o => o == .allocA
  down := eqHistory_down TwoAlloc (fun o => o == .allocA)

def cutAllocB : Cut twoAllocH where
  mem := fun o => o == .allocB
  down := eqHistory_down TwoAlloc (fun o => o == .allocB)

def budgetInterp (c : Cut twoAllocH) : Segmented.QuotaState :=
  if c.mem .allocA then
    ((fun b => if b then 10 else 0), (fun b => if b then 10 else 0))
  else if c.mem .allocB then
    ((fun b => if b then 0 else 10), (fun b => if b then 0 else 10))
  else
    ((fun _ => 0), (fun _ => 0))

def budA : Segmented.QuotaState := budgetInterp cutAllocA
def budB : Segmented.QuotaState := budgetInterp cutAllocB

theorem budget_joint : Joint twoAllocH budgetInterp budA budB :=
  ⟨cutAllocA, cutAllocB, rfl, rfl⟩

/-! ## §4. Free-id Sequence dup fragments -/

inductive SeqIns | ins21 | ins20
  deriving DecidableEq

def seqInsH : FinHistory SeqIns := eqHistory SeqIns

def cutIns21 : Cut seqInsH where
  mem := fun o => o == .ins21
  down := eqHistory_down SeqIns (fun o => o == .ins21)

def cutIns20 : Cut seqInsH where
  mem := fun o => o == .ins20
  down := eqHistory_down SeqIns (fun o => o == .ins20)

def seqInsInterp (c : Cut seqInsH) : GSet (Nat × Nat) :=
  fun p => (p.1 == 2 && p.2 == 1 && c.mem .ins21) || (p.1 == 2 && p.2 == 0 && c.mem .ins20)

def dupFragL : GSet (Nat × Nat) := seqInsInterp cutIns21
def dupFragR : GSet (Nat × Nat) := seqInsInterp cutIns20

/-- Under free id choice, concurrent inserts of `(2,1)` vs `(2,0)` are jointly
reachable. Content addressing is a ban on *issuing* both — not a cut theorem. -/
theorem sequence_dup_frag_joint : Joint seqInsH seqInsInterp dupFragL dupFragR :=
  ⟨cutIns21, cutIns20, rfl, rfl⟩

/-! ## §5. Causal clash ⇒ ¬ IConfluent -/

structure CausalClash {Op σ : Type} [MergeState σ]
    (H : FinHistory Op) (interp : Cut H → σ) (I : σ → Prop) where
  s₁ : σ
  s₂ : σ
  joint : Joint H interp s₁ s₂
  h₁ : I s₁
  h₂ : I s₂
  hbad : ¬ I (s₁ ⊔ s₂)

theorem causal_clash_not_iconfluent {Op σ : Type} [MergeState σ]
    {H : FinHistory Op} {interp : Cut H → σ} {I : σ → Prop}
    (c : CausalClash H interp I) : ¬ IConfluent I := fun h =>
  c.hbad (h c.s₁ c.s₂ c.h₁ c.h₂)

def orsetPresentClash : CausalClash or4H or4Interp (fun s => Present s 0) where
  s₁ := orClashL
  s₂ := orClashR
  joint := orset_clash_joint
  h₁ := orset_clash_present.1
  h₂ := orset_clash_present.2.1
  hbad := orset_clash_present.2.2

theorem orset_present_via_causal_clash :
    ¬ IConfluent (fun s : ORSet Nat Nat => Present s 0) :=
  causal_clash_not_iconfluent orsetPresentClash

/-! ## §6. Element-wide remove — the LatticeOnly protocol reading

Tag-scoped rem (§2) makes the catalog clash Live. The ORSet honesty note's
original *caution* was aimed at a different op shape: **element-wide remove**,
where a rem tombs *every* add-tag in its causal past (the classic
observed-remove "remove what I have seen"). Under the further discipline that
both adds happen-before both rems (rem issuers have seen both tags), the
asymmetric-tomb clash is **unreachable**.
-/

/-- Same four ids; hb forces each rem after **both** adds (element-wide issuer
saw the full add set). -/
def ewhb (a b : OR4) : Bool :=
  (a == b) ||
  (a == .a1 && (b == .r1 || b == .r2)) ||
  (a == .a2 && (b == .r1 || b == .r2))

def ewH : FinHistory OR4 where
  hb := ewhb
  hb_refl := fun o => by cases o <;> decide
  hb_trans := fun a b c h1 h2 => by
    cases a <;> cases b <;> cases c <;> simp [ewhb] at h1 h2 ⊢

/-- Element-wide interpretation: adds as presence of add ops; a rem tombs
**every** add-tag that is in the cut and happens-before that rem. -/
def ewInterp (c : Cut ewH) : ORSet Nat Nat :=
  (fun p => (p.1 == 0 && p.2 == 1 && c.mem .a1) || (p.1 == 0 && p.2 == 2 && c.mem .a2),
   fun p =>
     let t1 := p.1 == 0 && p.2 == 1
     let t2 := p.1 == 0 && p.2 == 2
     -- rem r1 tombs every add ≤ r1 in cut; similarly r2
     (t1 && c.mem .r1 && c.mem .a1) || (t1 && c.mem .r2 && c.mem .a1) ||
     (t2 && c.mem .r1 && c.mem .a2) || (t2 && c.mem .r2 && c.mem .a2))

/-- Catalog left clash: adds {1,2}, tombs **only** {2}. -/
def ewClashL : ORSet Nat Nat :=
  (fun p => p == (0, 1) || p == (0, 2), fun p => p == (0, 2))

theorem ewInterp_add1 {c : Cut ewH} :
    (ewInterp c).1 (0, 1) = c.mem .a1 := by
  simp only [ewInterp]
  cases h1 : c.mem .a1 <;> cases h2 : c.mem .a2 <;> simp [*]

theorem ewInterp_add2 {c : Cut ewH} :
    (ewInterp c).1 (0, 2) = c.mem .a2 := by
  simp only [ewInterp]
  cases h1 : c.mem .a1 <;> cases h2 : c.mem .a2 <;> simp [*]

/-- With both adds present, the two tomb bits are equal — both are
`(r1 ∨ r2)`. That is the whole element-wide discipline. -/
theorem ewInterp_tombs_agree {c : Cut ewH}
    (ha1 : c.mem .a1 = true) (ha2 : c.mem .a2 = true) :
    (ewInterp c).2 (0, 1) = (ewInterp c).2 (0, 2) := by
  simp only [ewInterp, ha1, ha2]
  cases c.mem .r1 <;> cases c.mem .r2 <;> rfl

/-- Under element-wide rem after both adds: no cut interprets to adds-both /
tombs-only-tag-2 (asymmetric tombs). -/
theorem ew_clashL_unreachable :
    ¬ ∃ c : Cut ewH, ewInterp c = ewClashL := by
  intro ⟨c, heq⟩
  have h1 : (ewInterp c).1 (0, 1) = true := by rw [congrArg Prod.fst heq]; decide
  have h2 : (ewInterp c).1 (0, 2) = true := by rw [congrArg Prod.fst heq]; decide
  have t1 : (ewInterp c).2 (0, 1) = false := by rw [congrArg Prod.snd heq]; decide
  have t2 : (ewInterp c).2 (0, 2) = true := by rw [congrArg Prod.snd heq]; decide
  have ma1 : c.mem .a1 = true := (ewInterp_add1 (c := c)) ▸ h1
  have ma2 : c.mem .a2 = true := (ewInterp_add2 (c := c)) ▸ h2
  have agree := ewInterp_tombs_agree ma1 ma2
  exact Bool.noConfusion (t1.symm.trans (agree.trans t2))

def ewClashR : ORSet Nat Nat :=
  (fun p => p == (0, 1) || p == (0, 2), fun p => p == (0, 1))

theorem ew_clashR_unreachable :
    ¬ ∃ c : Cut ewH, ewInterp c = ewClashR := by
  intro ⟨c, heq⟩
  have h1 : (ewInterp c).1 (0, 1) = true := by rw [congrArg Prod.fst heq]; decide
  have h2 : (ewInterp c).1 (0, 2) = true := by rw [congrArg Prod.fst heq]; decide
  have t1 : (ewInterp c).2 (0, 1) = true := by rw [congrArg Prod.snd heq]; decide
  have t2 : (ewInterp c).2 (0, 2) = false := by rw [congrArg Prod.snd heq]; decide
  have ma1 : c.mem .a1 = true := (ewInterp_add1 (c := c)) ▸ h1
  have ma2 : c.mem .a2 = true := (ewInterp_add2 (c := c)) ▸ h2
  have agree := ewInterp_tombs_agree ma1 ma2
  exact Bool.noConfusion (t2.symm.trans (agree.symm.trans t1))

/-- **Protocol dichotomy:** tag-scoped rem ⇒ clash Live; element-wide rem after
full observation ⇒ clash unreachable. Same lattice pair, opposite causal
verdicts — reachability depends on the remove op shape. -/
theorem orset_reachability_depends_on_remove_shape :
    (∃ c₁ c₂ : Cut or4H, or4Interp c₁ = orClashL ∧ or4Interp c₂ = orClashR) ∧
      (¬ ∃ c : Cut ewH, ewInterp c = ewClashL) ∧
      (¬ ∃ c : Cut ewH, ewInterp c = ewClashR) :=
  ⟨orset_clash_joint, ew_clashL_unreachable, ew_clashR_unreachable⟩

end Uwueave.CausalReach
