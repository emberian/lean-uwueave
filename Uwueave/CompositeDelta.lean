/-
# Uwueave.CompositeDelta — residual programs for arbitrary finite branches

`Recoverable` closes the resurrection converse for one operation and deliberately
stops at `StepGenerated`.  This file supplies the missing run-level object: a
branch is carried as an explicit finite patch, and a residual algebra gives the
patch to replay after the opposite branch.  The algebra is intentionally
proof-carrying.  Its diamond law says the two residual executions agree, its
merge law identifies that common state with the supplied three-way merge, and
its legality law proves that the common state preserves the invariant.

The distinction between a state and the patch that produced it remains visible.
No theorem reconstructs an arbitrary patch from two states: cyclic operations
make that false.  `PatchEdge` is the minimal history adapter that retains the
patch on an edge, and `residualDiamond` attaches the two residual edges without
depending on `Uwueave.Histories`.

The main transport theorem is exact:

    legalUnderComposition_iff_ancestralConfluent

It quantifies over arbitrary admitted finite runs, not one operation and not
`StepGenerated`.  The cheap lock inhabits the full residual algebra with a
one-instruction certificate.  The length-two counter from
`stepConfluent_does_not_imply_ancestralConfluent` fails the named
`LegalUnderComposition` law, so the new hypothesis has observable content.
-/
import Uwueave.Recoverable

namespace Uwueave.CompositeDelta

open Uwueave Uwueave.Ancestral Uwueave.Necessity Uwueave.Recoverable

universe u v w

variable {S : Type u} {Op : Type v}

/-! ## §1. Explicit composite patches -/

/-- A composite delta is an explicit finite operation patch. -/
abbrev Patch (Op : Type v) := List Op

/-- Execute the unconditional effects of a patch.  Guards are recorded
separately by `Admitted`; this matches `Ancestral.Serializing`, whose candidate
serializations apply effects even if the second ordering would abort. -/
def Patch.exec (g : Guarded S Op) : S → Patch Op → S
  | s, [] => s
  | s, op :: ops => Patch.exec g (g.eff op s) ops

/-- The total state transformer denoted by a patch. -/
def Patch.effect (g : Guarded S Op) (patch : Patch Op) : S → S :=
  fun s => patch.exec g s

/-- Every operation in the patch is admitted at the state produced by its
predecessors. -/
def Patch.Admitted (g : Guarded S Op) : S → Patch Op → Prop
  | _, [] => True
  | s, op :: ops => g.guard op s = true ∧ Patch.Admitted g (g.eff op s) ops

/-- Patch execution composes by list concatenation. -/
theorem Patch.exec_append (g : Guarded S Op) (s : S) (p q : Patch Op) :
    (p ++ q).exec g s = q.exec g (p.exec g s) := by
  induction p generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih (g.eff op s)

/-- Admission composes at the intermediate state. -/
theorem Patch.admitted_append (g : Guarded S Op) (s : S) (p q : Patch Op) :
    (p ++ q).Admitted g s ↔ p.Admitted g s ∧ q.Admitted g (p.exec g s) := by
  induction p generalizing s with
  | nil => simp [Patch.Admitted, Patch.exec]
  | cons op ops ih =>
      simp only [List.cons_append, Patch.Admitted, Patch.exec, ih]
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, h.2⟩

/-- An admitted patch is exactly a successful implementation run to its total
effect. -/
theorem Patch.runsTo_of_admitted (g : Guarded S Op) (s : S) (p : Patch Op)
    (hp : p.Admitted g s) : RunsTo g.impl s (p.exec g s) p := by
  induction p generalizing s with
  | nil => rfl
  | cons op ops ih =>
      rcases hp with ⟨hop, hops⟩
      rw [RunsTo, run_cons_some g.impl s op ops]
      · exact ih (g.eff op s) hops
      · simp [Guarded.impl, hop]

/-- Conversely, a successful run exposes both admission and its computed
endpoint.  This is the bridge from `Ancestral.Reachable` to explicit patches. -/
theorem Patch.admitted_of_runsTo (g : Guarded S Op) (s x : S) (p : Patch Op)
    (hp : RunsTo g.impl s x p) : p.Admitted g s ∧ p.exec g s = x := by
  induction p generalizing s with
  | nil =>
      have hsx : s = x := Option.some.inj hp
      exact ⟨trivial, hsx⟩
  | cons op ops ih =>
      by_cases hop : g.guard op s = true
      · have htry : g.impl.tryApply op s = some (g.eff op s) := by
          simp [Guarded.impl, hop]
        have hr : RunsTo g.impl (g.eff op s) x ops := by
          rw [RunsTo, run_cons_some g.impl s op ops htry] at hp
          exact hp
        obtain ⟨ha, he⟩ := ih (g.eff op s) hr
        exact ⟨⟨hop, ha⟩, he⟩
      · have htry : g.impl.tryApply op s = none := by
          simp [Guarded.impl, hop]
        have hnone : run g.impl s (op :: ops) = none :=
          run_cons_none g.impl s op ops htry
        rw [RunsTo, hnone] at hp
        contradiction

/-- A patch-labelled history edge.  Unlike a bare pair of states, it retains
the evidence required to residualize a cyclic or otherwise ambiguous delta. -/
structure PatchEdge (g : Guarded S Op) where
  parent : S
  child : S
  patch : Patch Op
  admitted : patch.Admitted g parent
  child_eq : patch.exec g parent = child

/-- Every patch edge forgets soundly to ordinary reachability. -/
theorem PatchEdge.reachable {g : Guarded S Op} (edge : PatchEdge g) :
    Reachable g.impl edge.parent edge.child := by
  refine ⟨edge.patch, ?_⟩
  rw [← edge.child_eq]
  exact edge.patch.runsTo_of_admitted g edge.parent edge.admitted

/-! ## §2. The exact arbitrary-run law -/

/-- **Legality under finite composition.** Every pair of admitted finite
branches with legal endpoints merges legally.  This is the run-level law that
`StepConfluent` cannot express. -/
def LegalUnderComposition (M : AncestralMerge S) (g : Guarded S Op)
    (I : Invariant S) : Prop :=
  ∀ (l : S) (p q : Patch Op), I l → p.Admitted g l → q.Admitted g l →
    I (p.exec g l) → I (q.exec g l) →
    I (M.merge3 l (p.exec g l) (q.exec g l))

/-- The patch law and ancestral confluence are the same obligation.  The
forward direction extracts patches from arbitrary `Reachable` witnesses; the
reverse direction packages admitted patches back into those witnesses. -/
theorem legalUnderComposition_iff_ancestralConfluent
    (M : AncestralMerge S) (g : Guarded S Op) (I : Invariant S) :
    LegalUnderComposition M g I ↔ AncestralConfluent M g.impl I := by
  constructor
  · intro h l x y hl hx hy hrx hry
    obtain ⟨p, hp⟩ := hrx
    obtain ⟨q, hq⟩ := hry
    obtain ⟨hap, hpx⟩ := Patch.admitted_of_runsTo g l x p hp
    obtain ⟨haq, hqy⟩ := Patch.admitted_of_runsTo g l y q hq
    subst x
    subst y
    exact h l p q hl hap haq hx hy
  · intro h l p q hl hp hq hpl hql
    exact h l (p.exec g l) (q.exec g l) hl hpl hql
      (PatchEdge.reachable
        { parent := l, child := p.exec g l, patch := p,
          admitted := hp, child_eq := rfl })
      (PatchEdge.reachable
        { parent := l, child := q.exec g l, patch := q,
          admitted := hq, child_eq := rfl })

/-! ## §3. Residual and commutation algebra -/

/-- A proof-carrying residual algebra for a supplied three-way merge.  The
residual `residual l p q` is the transformed form of `p` to execute after `q`.
Both transformed continuations must be admitted, commute to the same state,
compute the merge, and preserve the invariant.

The assumptions are precisely the triples ancestral confluence quantifies over:
legal ancestor, admitted branches, and legal branch endpoints. -/
structure Algebra (M : AncestralMerge S) (g : Guarded S Op)
    (I : Invariant S) where
  residual : S → Patch Op → Patch Op → Patch Op
  residual_admitted : ∀ (l : S) (p q : Patch Op),
    I l → p.Admitted g l → q.Admitted g l →
    I (p.exec g l) → I (q.exec g l) →
    (residual l p q).Admitted g (q.exec g l)
  commute : ∀ (l : S) (p q : Patch Op),
    I l → p.Admitted g l → q.Admitted g l →
    I (p.exec g l) → I (q.exec g l) →
    (residual l p q).exec g (q.exec g l) =
      (residual l q p).exec g (p.exec g l)
  merge_eq : ∀ (l : S) (p q : Patch Op),
    I l → p.Admitted g l → q.Admitted g l →
    I (p.exec g l) → I (q.exec g l) →
    M.merge3 l (p.exec g l) (q.exec g l) =
      (residual l p q).exec g (q.exec g l)
  legal_under_composition : ∀ (l : S) (p q : Patch Op),
    I l → p.Admitted g l → q.Admitted g l →
    I (p.exec g l) → I (q.exec g l) →
    I ((residual l p q).exec g (q.exec g l))

/-- The residual algebra discharges the named arbitrary-run legality law. -/
theorem Algebra.legalUnderComposition {M : AncestralMerge S} {g : Guarded S Op}
    {I : Invariant S} (A : Algebra M g I) : LegalUnderComposition M g I := by
  intro l p q hl hp hq hpl hql
  rw [A.merge_eq l p q hl hp hq hpl hql]
  exact A.legal_under_composition l p q hl hp hq hpl hql

/-- Therefore a residual algebra transports directly to full ancestral
confluence, with no `StepGenerated` premise. -/
theorem Algebra.ancestralConfluent {M : AncestralMerge S} {g : Guarded S Op}
    {I : Invariant S} (A : Algebra M g I) : AncestralConfluent M g.impl I :=
  (legalUnderComposition_iff_ancestralConfluent M g I).mp A.legalUnderComposition

/-- The residual diamond attached to a pair of sibling history edges. -/
structure ResidualDiamond (g : Guarded S Op) (left right : PatchEdge g)
    (merged : S) where
  leftToMerge : PatchEdge g
  rightToMerge : PatchEdge g
  left_parent : leftToMerge.parent = left.child
  right_parent : rightToMerge.parent = right.child
  left_child : leftToMerge.child = merged
  right_child : rightToMerge.child = merged

/-- Minimal history adapter: two sibling patch edges grow admitted residual
edges to the common merge state.  No version-DAG assumptions are smuggled in. -/
def Algebra.residualDiamond {M : AncestralMerge S} {g : Guarded S Op}
    {I : Invariant S} (A : Algebra M g I)
    (left right : PatchEdge g) (sameParent : left.parent = right.parent)
    (hparent : I left.parent) (hleft : I left.child) (hright : I right.child) :
    ResidualDiamond g left right (M.merge3 left.parent left.child right.child) := by
  let l := left.parent
  let p := left.patch
  let q := right.patch
  have hrightAdmitted : q.Admitted g l := by
    simpa [l, q, sameParent] using right.admitted
  have hpEnd : p.exec g l = left.child := left.child_eq
  have hqEnd : q.exec g l = right.child := by
    simpa [l, q, sameParent] using right.child_eq
  have hresR := A.residual_admitted l p q hparent left.admitted hrightAdmitted
    (hpEnd ▸ hleft) (hqEnd ▸ hright)
  have hresL := A.residual_admitted l q p hparent hrightAdmitted left.admitted
    (hqEnd ▸ hright) (hpEnd ▸ hleft)
  have hmerge := A.merge_eq l p q hparent left.admitted hrightAdmitted
    (hpEnd ▸ hleft) (hqEnd ▸ hright)
  have hcomm := A.commute l p q hparent left.admitted hrightAdmitted
    (hpEnd ▸ hleft) (hqEnd ▸ hright)
  refine
    { leftToMerge :=
        { parent := left.child
          child := M.merge3 l left.child right.child
          patch := A.residual l q p
          admitted := ?_
          child_eq := ?_ }
      rightToMerge :=
        { parent := right.child
          child := M.merge3 l left.child right.child
          patch := A.residual l p q
          admitted := ?_
          child_eq := ?_ }
      left_parent := rfl
      right_parent := rfl
      left_child := rfl
      right_child := rfl }
  · simpa [hpEnd] using hresL
  · rw [← hpEnd, ← hqEnd]
    exact hcomm.symm.trans hmerge.symm
  · simpa [hqEnd] using hresR
  · rw [← hpEnd, ← hqEnd]
    exact hmerge.symm

/-! ### §3.1 Honest work certificates -/

/-- A costed residual algebra reuses `Recoverable`'s certified single-delta
recovery and ties composite work to the residual patch's actual length.  No
wall-clock interpretation is inferred. -/
structure CostedAlgebra (M : AncestralMerge S) (g : Guarded S Op)
    (I : Invariant S) (Step : Type w) extends Algebra M g I where
  singleRecovery : CostedDeltaRecoveryOn g Step
  work : S → Patch Op → Patch Op → Nat
  work_eq_residual_length : ∀ l p q, work l p q = (residual l p q).length

/-! ## §4. Positive fixture — the cheap lock -/

/-- One replacement operation that writes any legal lock state. -/
def lockPatch : Lock → Patch LockOp
  | ⟨true, false⟩ => [.grantAlice]
  | ⟨false, true⟩ => [.grantBob]
  | ⟨false, false⟩ => [.release]
  | ⟨true, true⟩ => [.release]

/-- A legal lock state is exactly reconstructed by its one-operation patch,
independently of the state on which that patch is replayed. -/
theorem lockPatch_exec (before target : Lock) (ht : AtMostOne target) :
    (lockPatch target).exec lockOps before = target := by
  rcases before with ⟨ba, bb⟩
  rcases target with ⟨ta, tb⟩
  cases ba <;> cases bb <;> cases ta <;> cases tb <;>
    first | rfl | exact absurd ht (by decide)

/-- Lock replacement patches are always admitted. -/
theorem lockPatch_admitted (before target : Lock) :
    (lockPatch target).Admitted lockOps before := by
  rcases before with ⟨ba, bb⟩
  rcases target with ⟨ta, tb⟩
  cases ba <;> cases bb <;> cases ta <;> cases tb <;>
    exact ⟨rfl, trivial⟩

/-- The residual patch writes the lock merge's policy result. -/
def lockResidual (l : Lock) (p q : Patch LockOp) : Patch LockOp :=
  lockPatch (lockMerge l (p.exec lockOps l) (q.exec lockOps l))

/-- **Cheap positive instance.** Arbitrary admitted lock branches have a
one-operation residual diamond. -/
def cheapLockAlgebra :
    CostedAlgebra lockAM lockOps AtMostOne LockRecoveryStep where
  residual := lockResidual
  residual_admitted := by
    intro l p q _ _ _ _ _
    exact lockPatch_admitted _ _
  commute := by
    intro l p q _ _ _ hp hq
    have hm : AtMostOne (lockMerge l (p.exec lockOps l) (q.exec lockOps l)) :=
      lock_merge_atMostOne l _ _ hp hq
    have hm' : AtMostOne (lockMerge l (q.exec lockOps l) (p.exec lockOps l)) :=
      lock_merge_atMostOne l _ _ hq hp
    rw [lockResidual, lockResidual, lockPatch_exec _ _ hm, lockPatch_exec _ _ hm',
      lockMerge_comm]
  merge_eq := by
    intro l p q _ _ _ hp hq
    show lockMerge l (p.exec lockOps l) (q.exec lockOps l) = _
    rw [lockResidual, lockPatch_exec]
    exact lock_merge_atMostOne l _ _ hp hq
  legal_under_composition := by
    intro l p q _ _ _ hp hq
    rw [lockResidual, lockPatch_exec]
    exact lock_merge_atMostOne l _ _ hp hq
    exact lock_merge_atMostOne l _ _ hp hq
  singleRecovery := cheapLockRecovery
  work := fun _ _ _ => 1
  work_eq_residual_length := by
    intro l p q
    unfold lockResidual
    rcases lockMerge l (p.exec lockOps l) (q.exec lockOps l) with ⟨a, b⟩
    cases a <;> cases b <;> rfl

/-- Every composite lock residual has exactly one operation of work. -/
theorem cheapLockAlgebra_work (l : Lock) (p q : Patch LockOp) :
    cheapLockAlgebra.work l p q = 1 := rfl

/-- The composite certificate's unit work agrees with the pre-existing cheap
single-delta recovery certificate. -/
theorem cheapLockAlgebra_work_eq_singleRecovery (l : Lock) (p q : Patch LockOp) :
    cheapLockAlgebra.work l p q = cheapLockRecovery.work l (p.exec lockOps l) := by
  rw [cheapLockAlgebra_work, cheapLockRecovery_work]

/-- The residual proof, rather than `StepGenerated`, transports the lock to full
ancestral confluence. -/
theorem cheapLockAlgebra_ancestralConfluent :
    AncestralConfluent lockAM lockImpl AtMostOne :=
  cheapLockAlgebra.toAlgebra.ancestralConfluent

/-! ## §5. Negative fixture — the length-two counter -/

/-- The exact two-spend branches are admitted independently at zero. -/
theorem counter_two_patch_admitted :
    Patch.Admitted (spendOps 2) 0 [(), ()] := by
  exact ⟨rfl, ⟨rfl, trivial⟩⟩

/-- The new run-level law fails on the existing length-two witness: both
branches are legal at `2`, but their effect-faithful merge is `4`. -/
theorem counter_not_legalUnderComposition :
    ¬ LegalUnderComposition counterAM (spendOps 2) (fun n => n ≤ 3) := by
  intro h
  have hend : Patch.exec (spendOps 2) 0 [(), ()] ≤ 3 := by
    change 2 ≤ 3
    omega
  have hbad := h 0 [(), ()] [(), ()] (by omega)
    counter_two_patch_admitted counter_two_patch_admitted hend hend
  change 4 ≤ 3 at hbad
  omega

/-- The old counter theorem now points at a named missing composite law rather
than merely saying that one-step confluence does not lift. -/
theorem stepConfluent_counter_fails_composite_law :
    StepConfluent counterAM (spendOps 2) (fun n => n ≤ 3) ∧
      ¬ LegalUnderComposition counterAM (spendOps 2) (fun n => n ≤ 3) :=
  ⟨stepConfluent_does_not_imply_ancestralConfluent.2.1,
    fun hcomp => stepConfluent_does_not_imply_ancestralConfluent.2.2
      ((legalUnderComposition_iff_ancestralConfluent counterAM (spendOps 2)
        (fun n => n ≤ 3)).mp hcomp)⟩

/-- Consequently the counter cannot inhabit the residual algebra: the failed
law is a field, not an informal side condition. -/
theorem counter_has_no_composite_algebra (Step : Type w) :
    ¬ Nonempty (CostedAlgebra counterAM (spendOps 2) (fun n => n ≤ 3) Step) := by
  rintro ⟨A⟩
  exact counter_not_legalUnderComposition A.toAlgebra.legalUnderComposition

end Uwueave.CompositeDelta
