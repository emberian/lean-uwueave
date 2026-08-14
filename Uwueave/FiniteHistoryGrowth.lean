/-
# Uwueave.FiniteHistoryGrowth -- structurally fresh, repeatable history growth

`HistoryRuntime.appendSelected` materializes one policy-selected merge.  This
module isolates the more primitive fact underneath it: retained version patches
and a residual algebra are enough to append a coherent, legal merge at *any
declared common base*.  Selection remains a separate adapter.  This distinction
is load-bearing at a criss-cross frontier, where `Histories.cc_no_lowest` rules
out selected-only iteration.

Fresh identities are structural.  `IterVersion V 0` is definitionally `V`, and
each successor is the old carrier plus exactly one `Unit` summand.  No hash,
counter, or caller promise is treated as freshness evidence.

The graph lemmas below are exact: reachability between embedded old versions is
both preserved and reflected; reachability into the fresh node factors through
one of its two declared parents; and the fresh node reaches no old version.
Together with an extended covering enumeration, these facts make each growth
step reusable by later finite search.
-/
import Uwueave.HistoryRuntime

namespace Uwueave.FiniteHistoryGrowth

open Uwueave Uwueave.Ancestral Uwueave.Necessity
open Uwueave.Histories Uwueave.FiniteHistory Uwueave.CompositeDelta
open Uwueave.HistoryEngine Uwueave.HistoryRuntime Uwueave.HistoryPolicy

set_option autoImplicit false

/-! ## 1. Structural freshness -/

/-- Add exactly one structurally fresh version at every successor. -/
def IterVersion (V : Type) : Nat → Type
  | 0 => V
  | n + 1 => IterVersion V n ⊕ Unit

/-- The initial carrier is definitionally the caller's carrier. -/
example (V : Type) : IterVersion V 0 = V := rfl

/-- The successor carrier is definitionally one old summand and one fresh
inhabitant. -/
example (V : Type) (n : Nat) :
    IterVersion V (n + 1) = (IterVersion V n ⊕ Unit) := rfl

def old {V : Type} {n : Nat} (v : IterVersion V n) : IterVersion V (n + 1) :=
  .inl v

def fresh {V : Type} {n : Nat} : IterVersion V (n + 1) := .inr ()

theorem old_injective {V : Type} {n : Nat} :
    Function.Injective (@old V n) := by
  intro a b h
  exact Sum.inl.inj h

theorem fresh_ne_old {V : Type} {n : Nat} (v : IterVersion V n) :
    (@fresh V n) ≠ old v := by
  intro h
  cases h

/-! ## 2. Exact graph transport for one append -/

theorem appendDag_ancestry_inl_of {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right : V) {a b : V}
    (h : Ancestry D a b) :
    Ancestry (appendDag D left right) (.inl a) (.inl b) := by
  induction h with
  | direct edge => exact .direct edge
  | extend _ edge ih => exact .extend ih edge

private theorem appendDag_ancestry_inl_reflect_aux {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right : V) {a : V} {endpoint : V ⊕ Unit}
    (h : Ancestry (appendDag D left right) (.inl a) endpoint) :
    match endpoint with
    | .inl b => Ancestry D a b
    | .inr _ => True := by
  induction h with
  | @direct endpoint edge =>
      cases endpoint with
      | inl endpoint => exact .direct edge
      | inr _unit => trivial
  | @extend parent endpoint ancestry edge ih =>
      cases endpoint with
      | inl endpoint =>
          cases parent with
          | inl parent => exact .extend ih edge
          | inr _unit => simp [appendDag] at edge
      | inr _unit => trivial

theorem appendDag_ancestry_inl_reflect {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right : V) {a b : V}
    (h : Ancestry (appendDag D left right) (.inl a) (.inl b)) :
    Ancestry D a b :=
  appendDag_ancestry_inl_reflect_aux D left right h

/-- Strict ancestry between old versions is unchanged by append. -/
theorem appendDag_ancestry_inl_iff {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right a b : V) :
    Ancestry (appendDag D left right) (.inl a) (.inl b) ↔
      Ancestry D a b :=
  ⟨appendDag_ancestry_inl_reflect D left right,
    appendDag_ancestry_inl_of D left right⟩

/-- Reachability between old versions is preserved *and reflected*.  In
particular, appending a merge cannot manufacture an old-to-old path through the
fresh node. -/
theorem appendDag_reaches_inl_iff {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right a b : V) :
    Reaches (appendDag D left right) (.inl a) (.inl b) ↔ Reaches D a b := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (Sum.inl.inj h)
    · exact Or.inr (appendDag_ancestry_inl_reflect D left right h)
  · intro h
    exact appendDag_reaches_inl h

private theorem appendDag_ancestry_to_fresh_aux {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right a : V) {endpoint : V ⊕ Unit}
    (h : Ancestry (appendDag D left right) (.inl a) endpoint) :
    endpoint = .inr () → Reaches D a left ∨ Reaches D a right := by
  induction h with
  | @direct endpoint edge =>
      intro endpointEq
      subst endpoint
      simp only [appendDag, decide_eq_true_eq] at edge
      rcases edge with rfl | rfl
      · exact Or.inl (Reaches.refl D _)
      · exact Or.inr (Reaches.refl D _)
  | @extend parent endpoint path finalEdge ih =>
      intro endpointEq
      subst endpoint
      cases parent with
      | inl parent =>
          have oldPath : Ancestry D a parent :=
            appendDag_ancestry_inl_reflect D left right path
          simp only [appendDag, decide_eq_true_eq] at finalEdge
          rcases finalEdge with rfl | rfl
          · exact Or.inl (Or.inr oldPath)
          · exact Or.inr (Or.inr oldPath)
      | inr _unit => simp [appendDag] at finalEdge

private theorem appendDag_ancestry_to_fresh {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right a : V)
    (h : Ancestry (appendDag D left right) (.inl a) (.inr ())) :
    Reaches D a left ∨ Reaches D a right :=
  appendDag_ancestry_to_fresh_aux D left right a h rfl

/-- An old version reaches the fresh merge exactly when it reaches at least one
declared parent. -/
theorem appendDag_reaches_fresh_iff {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right a : V) :
    Reaches (appendDag D left right) (.inl a) (.inr ()) ↔
      Reaches D a left ∨ Reaches D a right := by
  constructor
  · intro h
    rcases h with h | h
    · cases h
    · exact appendDag_ancestry_to_fresh D left right a h
  · intro h
    rcases h with h | h
    · rcases h with rfl | ancestry
      · exact Or.inr (.direct (by simp [appendDag]))
      · exact Or.inr (.extend (appendDag_ancestry_inl_of D left right ancestry)
          (by simp [appendDag]))
    · rcases h with rfl | ancestry
      · exact Or.inr (.direct (by simp [appendDag]))
      · exact Or.inr (.extend (appendDag_ancestry_inl_of D left right ancestry)
          (by simp [appendDag]))

/-- The fresh node has exactly the two declared old parents (or one when they
coincide). -/
theorem appendDag_parent_fresh_iff {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right parent : V) :
    (appendDag D left right).parent (.inl parent) (.inr ()) = true ↔
      parent = left ∨ parent = right := by
  simp [appendDag]

/-- The fresh node has no outgoing edge at all. -/
theorem appendDag_fresh_has_no_child {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right : V) (child : V ⊕ Unit) :
    (appendDag D left right).parent (.inr ()) child = false := by
  cases child <;> rfl

private theorem appendDag_no_ancestry_from_fresh {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right : V) {endpoint : V ⊕ Unit}
    (h : Ancestry (appendDag D left right) (.inr ()) endpoint) : False := by
  induction h with
  | direct edge => simp [appendDag] at edge
  | extend _ _ ih => exact ih

/-- Consequently the fresh node reaches no embedded old version. -/
theorem appendDag_fresh_not_reaches_old {V : Type} [DecidableEq V]
    (D : VersionDag V) (left right oldVersion : V) :
    ¬ Reaches (appendDag D left right) (.inr ()) (.inl oldVersion) := by
  intro h
  rcases h with h | h
  · cases h
  · exact appendDag_no_ancestry_from_fresh D left right h

/-- A covering enumeration grows by exactly the fresh structural identity. -/
def appendEnumeration {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (left right : V) : Enumeration (appendDag D left right) where
  vertices := F.vertices.map Sum.inl ++ [.inr ()]
  nodup := by
    rw [List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · exact List.Pairwise.map Sum.inl
        (fun _ _ distinct equal => distinct (Sum.inl.inj equal)) F.nodup
    · simp
  complete := by
    intro version
    cases version with
    | inl version => simp [F.complete version]
    | inr _unit => cases _unit; simp

theorem appendEnumeration_vertices_length {V : Type} [DecidableEq V]
    {D : VersionDag V} (F : Enumeration D) (left right : V) :
    (appendEnumeration F left right).vertices.length = F.vertices.length + 1 := by
  simp [appendEnumeration]

/-! ## 3. Retained patch transport and composition -/

/-- An old retained patch remains a retained patch after append. -/
def liftVersionPatch {V S Op : Type} [DecidableEq V]
    {H : History V S Op} {g : Guarded S Op} {base tip appendBase left right : V}
    {merged : S} (branch : VersionPatch H g base tip) :
    VersionPatch (appendHistory H appendBase left right merged) g (.inl base) (.inl tip) where
  versions := appendDag_reaches_inl branch.versions
  patch := branch.patch
  admitted := branch.admitted
  tip_eq := branch.tip_eq

/-- Retained patches compose without reconstructing either patch from its
endpoints. -/
def composeVersionPatch {V S Op : Type} {H : History V S Op}
    {g : Guarded S Op} {base middle tip : V}
    (first : VersionPatch H g base middle)
    (second : VersionPatch H g middle tip) : VersionPatch H g base tip where
  versions := first.versions.trans second.versions
  patch := first.patch ++ second.patch
  admitted := by
    rw [Patch.admitted_append]
    refine ⟨first.admitted, ?_⟩
    simpa only [first.tip_eq] using second.admitted
  tip_eq := by
    rw [Patch.exec_append, first.tip_eq, second.tip_eq]

/-! ## 4. Policy-neutral common-base append -/

variable {S Op : Type}

/-- The evidence needed to append a merge at a declared common base.  Unlike
`SelectedRequest`, this structure says nothing about a selection policy or a
lowest base.  The two retained branches themselves prove common ancestry. -/
structure CommonAppendRequest {V : Type} (H : History V S Op)
    (g : Guarded S Op) (I : Invariant S) (left right : V) where
  base : V
  leftPatch : VersionPatch H g base left
  rightPatch : VersionPatch H g base right
  base_legal : I (H.state base)
  left_legal : I (H.state left)
  right_legal : I (H.state right)

/-- The policy-neutral algebraic admission, including both residual legs. -/
structure CommonAdmission {V : Type} {H : History V S Op}
    {g : Guarded S Op} {I : Invariant S} {left right : V}
    (M : AncestralMerge S) (request : CommonAppendRequest H g I left right) where
  merged : S
  merged_eq : merged = M.merge3 (H.state request.base) (H.state left) (H.state right)
  legal : I merged
  diamond : ResidualDiamond g request.leftPatch.toEdge request.rightPatch.toEdge merged

/-- Residual algebra legality discharges a common-base admission without any
base-selection premise. -/
def admitCommon {V : Type} {H : History V S Op} {g : Guarded S Op}
    {I : Invariant S} {left right : V} {M : AncestralMerge S}
    (A : Algebra M g I) (request : CommonAppendRequest H g I left right) :
    CommonAdmission M request := by
  let merged := M.merge3 (H.state request.base) (H.state left) (H.state right)
  have diamond := A.residualDiamond request.leftPatch.toEdge request.rightPatch.toEdge
    rfl request.base_legal request.left_legal request.right_legal
  have legal : I merged := by
    dsimp [merged]
    rw [← request.leftPatch.tip_eq, ← request.rightPatch.tip_eq]
    exact A.legalUnderComposition (H.state request.base)
      request.leftPatch.patch request.rightPatch.patch request.base_legal
      request.leftPatch.admitted request.rightPatch.admitted
      (request.leftPatch.tip_eq ▸ request.left_legal)
      (request.rightPatch.tip_eq ▸ request.right_legal)
  exact ⟨merged, rfl, legal, diamond⟩

/-- A coherent policy-neutral append plus the residual version patches needed
by a later growth step. -/
structure AppendedCommon {V : Type} [DecidableEq V]
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S}
    {left right : V} {M : AncestralMerge S}
    (oldCoherent : H.Coherent M g.impl) (A : Algebra M g I)
    (request : CommonAppendRequest H g I left right) where
  admission : CommonAdmission M request
  history : History (V ⊕ Unit) S Op
  history_eq : history = appendHistory H request.base left right admission.merged
  coherent : history.Coherent M g.impl
  leftResidual : VersionPatch history g (.inl left) (.inr ())
  rightResidual : VersionPatch history g (.inl right) (.inr ())
  baseToFreshViaLeft : VersionPatch history g (.inl request.base) (.inr ())
  baseToFreshViaRight : VersionPatch history g (.inl request.base) (.inr ())

/-- Append one coherent legal merge at an arbitrary retained common base. -/
def appendCommon {V : Type} [DecidableEq V]
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S}
    {left right : V} {M : AncestralMerge S}
    (oldCoherent : H.Coherent M g.impl) (A : Algebra M g I)
    (request : CommonAppendRequest H g I left right) :
    AppendedCommon oldCoherent A request := by
  let admission := admitCommon A request
  let history := appendHistory H request.base left right admission.merged
  have coherent : history.Coherent M g.impl := by
    change (appendHistory H request.base left right admission.merged).Coherent M g.impl
    constructor
    · intro version rootOrigin
      cases version with
      | inl version =>
          change liftOrigin (H.origin version) = .root at rootOrigin
          have oldRoot := (liftOrigin_eq_root_iff (H.origin version)).1 rootOrigin
          exact congrArg Sum.inl (oldCoherent.root_unique version oldRoot)
      | inr _unit => cases rootOrigin
    · intro version
      cases version with
      | inl version =>
          have oldNode := oldCoherent.nodes version
          cases originEq : H.origin version with
          | root => simp [OriginOK, appendHistory, liftOrigin, originEq]
          | ran parent =>
              simp only [OriginOK, originEq] at oldNode
              simpa [OriginOK, appendHistory, liftOrigin, originEq] using oldNode
          | merged base oldLeft oldRight =>
              simp only [OriginOK, originEq] at oldNode
              rcases oldNode with ⟨leftParent, rightParent, common, stateEq⟩
              simp only [OriginOK, appendHistory, liftOrigin, originEq]
              exact ⟨leftParent, rightParent,
                ⟨appendDag_reaches_inl common.1, appendDag_reaches_inl common.2⟩,
                stateEq⟩
      | inr _unit =>
          change (appendDag H.dag left right).parent (.inl left) (.inr ()) = true ∧
            (appendDag H.dag left right).parent (.inl right) (.inr ()) = true ∧
            CommonAncestor (appendDag H.dag left right) (.inl left) (.inl right)
              (.inl request.base) ∧
            admission.merged =
              M.merge3 (H.state request.base) (H.state left) (H.state right)
          exact ⟨by simp [appendDag], by simp [appendDag],
            ⟨appendDag_reaches_inl request.leftPatch.versions,
              appendDag_reaches_inl request.rightPatch.versions⟩,
            admission.merged_eq⟩
  have leftResidual : VersionPatch history g (.inl left) (.inr ()) := by
    refine
      { versions := Or.inr (.direct (by simp [history, appendHistory, appendDag]))
        patch := admission.diamond.leftToMerge.patch
        admitted := ?_
        tip_eq := ?_ }
    · simpa [history, appendHistory, admission.diamond.left_parent] using
        admission.diamond.leftToMerge.admitted
    · simpa [history, appendHistory, admission.diamond.left_parent,
        admission.diamond.left_child] using admission.diamond.leftToMerge.child_eq
  have rightResidual : VersionPatch history g (.inl right) (.inr ()) := by
    refine
      { versions := Or.inr (.direct (by simp [history, appendHistory, appendDag]))
        patch := admission.diamond.rightToMerge.patch
        admitted := ?_
        tip_eq := ?_ }
    · simpa [history, appendHistory, admission.diamond.right_parent] using
        admission.diamond.rightToMerge.admitted
    · simpa [history, appendHistory, admission.diamond.right_parent,
        admission.diamond.right_child] using admission.diamond.rightToMerge.child_eq
  have liftedLeft : VersionPatch history g (.inl request.base) (.inl left) := by
    simpa [history] using liftVersionPatch request.leftPatch
      (appendBase := request.base) (left := left) (right := right)
      (merged := admission.merged)
  have liftedRight : VersionPatch history g (.inl request.base) (.inl right) := by
    simpa [history] using liftVersionPatch request.rightPatch
      (appendBase := request.base) (left := left) (right := right)
      (merged := admission.merged)
  exact
    { admission := admission
      history := history
      history_eq := rfl
      coherent := coherent
      leftResidual := leftResidual
      rightResidual := rightResidual
      baseToFreshViaLeft := composeVersionPatch liftedLeft leftResidual
      baseToFreshViaRight := composeVersionPatch liftedRight rightResidual }

/-- Old legality plus the algebra-proved fresh legality covers every state in
the extended carrier. -/
theorem AppendedCommon.all_legal {V : Type} [DecidableEq V]
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S}
    {left right : V} {M : AncestralMerge S}
    {oldCoherent : H.Coherent M g.impl} {A : Algebra M g I}
    {request : CommonAppendRequest H g I left right}
    (appended : AppendedCommon oldCoherent A request)
    (oldLegal : ∀ version, I (H.state version)) :
    ∀ version, I (appended.history.state version) := by
  intro version
  rw [appended.history_eq]
  cases version with
  | inl version => exact oldLegal version
  | inr _unit => exact appended.admission.legal

/-! ## 5. Selected policy adapter -/

/-- Forget only the selected-policy layer, retaining all operational evidence. -/
def commonOfSelected {V : Type} {P : HistoryMerge V S Op}
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S} {left right : V}
    (request : SelectedRequest P H g I left right) :
    CommonAppendRequest H g I left right where
  base := request.base
  leftPatch := request.left
  rightPatch := request.right
  base_legal := request.base_legal
  left_legal := request.left_legal
  right_legal := request.right_legal

/-- `appendCommon` is a strict generalization of the selected append seam. -/
def appendSelectedViaCommon {V : Type} [DecidableEq V]
    {P : HistoryMerge V S Op} {H : History V S Op} {g : Guarded S Op}
    {I : Invariant S} {left right : V}
    (oldCoherent : H.Coherent P.kernel g.impl) (A : Algebra P.kernel g I)
    (request : SelectedRequest P H g I left right) :
    AppendedCommon oldCoherent A (commonOfSelected request) :=
  appendCommon oldCoherent A (commonOfSelected request)

/-- The policy adapter appends exactly the policy-selected result. -/
theorem appendSelectedViaCommon_policy_eq {V : Type} [DecidableEq V]
    {P : HistoryMerge V S Op} {H : History V S Op} {g : Guarded S Op}
    {I : Invariant S} {left right : V}
    (oldCoherent : H.Coherent P.kernel g.impl) (A : Algebra P.kernel g I)
    (request : SelectedRequest P H g I left right) :
    P.result H left right =
      (appendSelectedViaCommon oldCoherent A request).admission.merged := by
  unfold appendSelectedViaCommon appendCommon admitCommon
  unfold HistoryMerge.result HistoryMerge.apply HistoryMerge.decisionAt
  rw [request.selected]
  exact P.reconcileSelected _ _ _

/-! ## 6. Load-bearing fixtures and the honest stopping point -/

/-- The cheap-lock selected fixture passes through the policy-neutral core. -/
def lockCommonAppended :=
  appendSelectedViaCommon lockHistory_coherent cheapLockAlgebra.toAlgebra
    lockForkRequest

theorem lockCommonAppended_coherent :
    lockCommonAppended.history.Coherent lockAM lockOps.impl :=
  lockCommonAppended.coherent

theorem lockCommonAppended_legal :
    AtMostOne lockCommonAppended.admission.merged :=
  lockCommonAppended.admission.legal

/-- The fixture retains a root-to-fresh patch, so a subsequent growth request
does not need to reverse-engineer a delta from its endpoint states. -/
def lockCommonAppended_retains_growth_patch :
    VersionPatch lockCommonAppended.history lockOps (.inl LVer.root) (.inr ()) :=
  lockCommonAppended.baseToFreshViaLeft

/-- The old lock ancestry is reflected exactly through the concrete append. -/
theorem lockCommonAppended_old_reachability_exact (a b : LVer) :
    Reaches lockCommonAppended.history.dag (.inl a) (.inl b) ↔
      Reaches lockHistory.dag a b := by
  rw [lockCommonAppended.history_eq]
  exact appendDag_reaches_inl_iff lockHistory.dag .alice .bob a b

/-- **Counter-fixture:** the known criss-cross pair has two valid common bases
and no lowest one.  Therefore an induction whose successor requires only a
`SelectedRequest` cannot even state its next step here.  `appendCommon` accepts
an explicitly retained common base instead, but this module does not pretend
the counter MRDT supplies the residual algebra needed to make that append
legal. -/
theorem crissCross_blocks_selected_only_growth :
    CommonAncestor ccDag .mergeL .mergeR .left ∧
      CommonAncestor ccDag .mergeL .mergeR .right ∧
      ¬ ∃ base, LowestCommonBase ccDag .mergeL .mergeR base :=
  ⟨cc_left_common, cc_right_common, cc_no_lowest⟩

end Uwueave.FiniteHistoryGrowth
