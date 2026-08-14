/-
# Uwueave.ResolvedHistoryGrowth -- explicit ambiguity resolution in provenance

An ambiguous version pair has no lowest common base.  It may nevertheless have
several certified maximal common bases, and an implementation may explicitly
resolve that ambiguity by choosing one of the bases named by its policy.  This
module records that choice as proof-carrying provenance and routes the chosen
common base through `FiniteHistoryGrowth.appendCommon`.

The underlying `Histories.Origin.merged` can record only `(base, left, right)`.
It cannot record the policy decision or which ambiguous arm was chosen.  The
`ResolvedAmbiguousRequest` and `ResolvedAppend` packages therefore retain those
facts beside the history, while proving that `Origin.merged` contains exactly
the resolved base.  No stronger provenance is encoded into `Origin`.

The concrete lock fixture builds two independent merge versions over one fork,
proves their two branch versions are incomparable maximal common bases (hence
there is no lowest base), and then appends a second-round merge by explicitly
choosing the first named base.  This is graph/history growth only: it claims no
arbitrary induction, delivery convergence, protocol convergence, or
authentication.
-/
import Uwueave.FiniteHistoryGrowth

namespace Uwueave.ResolvedHistoryGrowth

open Uwueave Uwueave.Ancestral Uwueave.Necessity
open Uwueave.Histories Uwueave.CompositeDelta Uwueave.HistoryEngine
open Uwueave.HistoryBase Uwueave.HistoryPolicy Uwueave.HistoryRuntime
open Uwueave.FiniteHistoryGrowth

set_option autoImplicit false

/-! ## 1. The exact graph shape of two independent appends -/

variable {V : Type} [DecidableEq V]

private abbrev ParallelDag (D : VersionDag V) (left right : V) :=
  appendDag (appendDag D left right) (.inl left) (.inl right)

private abbrev firstTip (V : Type) : (V ⊕ Unit) ⊕ Unit :=
  .inl (.inr ())

private abbrev secondTip (V : Type) : (V ⊕ Unit) ⊕ Unit :=
  .inr ()

private abbrev oldTwice (version : V) : (V ⊕ Unit) ⊕ Unit :=
  .inl (.inl version)

theorem parallel_left_common (D : VersionDag V) (left right : V) :
    CommonAncestor (ParallelDag D left right) (firstTip V) (secondTip V)
      (oldTwice left) := by
  constructor
  · exact Or.inr (.direct (by simp [ParallelDag, appendDag]))
  · exact Or.inr (.direct (by simp [ParallelDag, appendDag]))

theorem parallel_right_common (D : VersionDag V) (left right : V) :
    CommonAncestor (ParallelDag D left right) (firstTip V) (secondTip V)
      (oldTwice right) := by
  constructor
  · exact Or.inr (.direct (by simp [ParallelDag, appendDag]))
  · exact Or.inr (.direct (by simp [ParallelDag, appendDag]))

private theorem parallel_left_maximal (D : VersionDag V) (left right : V)
    (notLeftRight : ¬ Reaches D left right) :
    MaximalCommonBase (ParallelDag D left right) (firstTip V) (secondTip V)
      (oldTwice left) := by
  refine ⟨parallel_left_common D left right, ?_⟩
  intro candidate common leftToCandidate
  cases candidate with
  | inr _unit =>
      exact (appendDag_fresh_not_reaches_old (appendDag D left right)
        (.inl left) (.inl right) (.inr ()) common.1).elim
  | inl candidate =>
      have leftToCandidate' :
          Reaches (appendDag D left right) (.inl left) candidate :=
        (appendDag_reaches_inl_iff (appendDag D left right)
          (.inl left) (.inl right) (.inl left) candidate).1 leftToCandidate
      cases candidate with
      | inr _unit =>
          have split := (appendDag_reaches_fresh_iff (appendDag D left right)
            (.inl left) (.inl right) (.inr ())).1 common.2
          rcases split with reachesLeft | reachesRight
          · exact (appendDag_fresh_not_reaches_old D left right left reachesLeft).elim
          · exact (appendDag_fresh_not_reaches_old D left right right reachesRight).elim
      | inl candidate =>
          have leftToCandidateD : Reaches D left candidate :=
            (appendDag_reaches_inl_iff D left right left candidate).1
              leftToCandidate'
          have candidateToFirst :
              Reaches (appendDag D left right) (.inl candidate) (.inr ()) :=
            (appendDag_reaches_inl_iff (appendDag D left right)
              (.inl left) (.inl right) (.inl candidate) (.inr ())).1 common.1
          have split := (appendDag_reaches_fresh_iff D left right candidate).1
            candidateToFirst
          rcases split with candidateToLeft | candidateToRight
          · have equal : candidate = left :=
              Reaches.antisymm candidateToLeft leftToCandidateD
            subst candidate
            rfl
          · exact (notLeftRight (leftToCandidateD.trans candidateToRight)).elim

private theorem parallel_right_maximal (D : VersionDag V) (left right : V)
    (notRightLeft : ¬ Reaches D right left) :
    MaximalCommonBase (ParallelDag D left right) (firstTip V) (secondTip V)
      (oldTwice right) := by
  refine ⟨parallel_right_common D left right, ?_⟩
  intro candidate common rightToCandidate
  cases candidate with
  | inr _unit =>
      exact (appendDag_fresh_not_reaches_old (appendDag D left right)
        (.inl left) (.inl right) (.inr ()) common.1).elim
  | inl candidate =>
      have rightToCandidate' :
          Reaches (appendDag D left right) (.inl right) candidate :=
        (appendDag_reaches_inl_iff (appendDag D left right)
          (.inl left) (.inl right) (.inl right) candidate).1 rightToCandidate
      cases candidate with
      | inr _unit =>
          have split := (appendDag_reaches_fresh_iff (appendDag D left right)
            (.inl left) (.inl right) (.inr ())).1 common.2
          rcases split with reachesLeft | reachesRight
          · exact (appendDag_fresh_not_reaches_old D left right left reachesLeft).elim
          · exact (appendDag_fresh_not_reaches_old D left right right reachesRight).elim
      | inl candidate =>
          have rightToCandidateD : Reaches D right candidate :=
            (appendDag_reaches_inl_iff D left right right candidate).1
              rightToCandidate'
          have candidateToFirst :
              Reaches (appendDag D left right) (.inl candidate) (.inr ()) :=
            (appendDag_reaches_inl_iff (appendDag D left right)
              (.inl left) (.inl right) (.inl candidate) (.inr ())).1 common.1
          have split := (appendDag_reaches_fresh_iff D left right candidate).1
            candidateToFirst
          rcases split with candidateToLeft | candidateToRight
          · exact (notRightLeft (rightToCandidateD.trans candidateToLeft)).elim
          · have equal : candidate = right :=
              Reaches.antisymm candidateToRight rightToCandidateD
            subst candidate
            rfl

theorem parallel_no_lowest (D : VersionDag V) (left right : V)
    (distinct : left ≠ right)
    (notLeftRight : ¬ Reaches D left right)
    (notRightLeft : ¬ Reaches D right left) :
    ¬ ∃ base, LowestCommonBase (ParallelDag D left right)
      (firstTip V) (secondTip V) base :=
  ambiguous_excludes_lowest
    (parallel_left_maximal D left right notLeftRight)
    (parallel_right_maximal D left right notRightLeft)
    (fun equal => distinct (Sum.inl.inj (Sum.inl.inj equal)))

/-! ## 2. Policy-aware ambiguity resolution -/

variable {S Op : Type}

/-- A policy has reported an ambiguous pair; the caller explicitly chooses one
of the two bases named by that report and supplies retained patches from that
base.  `common.base = chosen` prevents the provenance record and operational
append from drifting apart. -/
structure ResolvedAmbiguousRequest {V : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (g : Guarded S Op) (I : Invariant S)
    (left right : V) where
  first : V
  second : V
  inScope : P.scope H left right
  decision_eq : P.select H left right = .ambiguous first second
  chosen : V
  chosen_named : chosen = first ∨ chosen = second
  common : CommonAppendRequest H g I left right
  common_base_eq : common.base = chosen

/-- The package retained after resolved append.  The original policy decision,
the resolution, the common-base evidence, and the materialized history all stay
available. -/
structure ResolvedAppend {V : Type} [DecidableEq V]
    {P : HistoryMerge V S Op} {H : History V S Op} {g : Guarded S Op}
    {I : Invariant S} {left right : V} {M : AncestralMerge S}
    (kernel_eq : P.kernel = M) (oldCoherent : H.Coherent M g.impl)
    (A : Algebra M g I)
    (request : ResolvedAmbiguousRequest P H g I left right) where
  appended : AppendedCommon oldCoherent A request.common
  decision_valid : ValidInHistory H left right (.ambiguous request.first request.second)
  origin_records_resolution :
    appended.history.origin (.inr ()) =
      .merged (.inl request.chosen) (.inl left) (.inl right)

/-- Materialize an explicit ambiguity resolution.  This deliberately uses the
kernel at the chosen common base, not `P.reconcile`'s unconstrained ambiguous
branch. -/
def appendResolved {V : Type} [DecidableEq V]
    {P : HistoryMerge V S Op} {H : History V S Op} {g : Guarded S Op}
    {I : Invariant S} {left right : V} {M : AncestralMerge S}
    (kernel_eq : P.kernel = M) (oldCoherent : H.Coherent M g.impl)
    (A : Algebra M g I)
    (request : ResolvedAmbiguousRequest P H g I left right) :
    ResolvedAppend kernel_eq oldCoherent A request := by
  let appended := appendCommon oldCoherent A request.common
  have valid : ValidInHistory H left right
      (.ambiguous request.first request.second) := by
    have selected := P.selectSound H left right request.inScope
    simpa [request.decision_eq] using selected
  refine
    { appended := appended
      decision_valid := valid
      origin_records_resolution := ?_ }
  rw [appended.history_eq]
  simp [appendHistory, request.common_base_eq]

/-! ## 3. Concrete two-round lock criss-cross -/

open Uwueave.CompositeDelta

def lockFirstRequest :
    CommonAppendRequest lockHistory lockOps AtMostOne .alice .bob :=
  commonOfSelected lockForkRequest

def lockFirstAppend :=
  appendCommon lockHistory_coherent cheapLockAlgebra.toAlgebra lockFirstRequest

def lockParallelRequest :
    CommonAppendRequest lockFirstAppend.history lockOps AtMostOne
      (.inl LVer.alice) (.inl LVer.bob) where
  base := .inl .root
  leftPatch := by
    rw [lockFirstAppend.history_eq]
    exact liftVersionPatch lockRootToAlice
  rightPatch := by
    rw [lockFirstAppend.history_eq]
    exact liftVersionPatch lockRootToBob
  base_legal := by decide
  left_legal := by decide
  right_legal := by decide

def lockParallelAppend :=
  appendCommon lockFirstAppend.coherent cheapLockAlgebra.toAlgebra
    lockParallelRequest

abbrev LockParallelVersion := (LVer ⊕ Unit) ⊕ Unit

def lockMergeLeft : LockParallelVersion := .inl (.inr ())
def lockMergeRight : LockParallelVersion := .inr ()
def lockBaseAlice : LockParallelVersion := .inl (.inl .alice)
def lockBaseBob : LockParallelVersion := .inl (.inl .bob)

theorem lockParallel_history_eq :
    lockParallelAppend.history =
      appendHistory
        (appendHistory lockHistory .root .alice .bob
          lockFirstAppend.admission.merged)
        (.inl .root) (.inl .alice) (.inl .bob)
        lockParallelAppend.admission.merged := by
  rfl

private theorem lock_alice_not_reaches_bob : ¬ Reaches lvDag .alice .bob :=
  not_reaches_of_ne_of_rank_ge (by decide) (by decide)

private theorem lock_bob_not_reaches_alice : ¬ Reaches lvDag .bob .alice :=
  not_reaches_of_ne_of_rank_ge (by decide) (by decide)

theorem lockParallel_alice_maximal :
    MaximalCommonBase lockParallelAppend.history.dag lockMergeLeft lockMergeRight
      lockBaseAlice := by
  rw [lockParallel_history_eq]
  exact parallel_left_maximal lvDag .alice .bob lock_alice_not_reaches_bob

theorem lockParallel_bob_maximal :
    MaximalCommonBase lockParallelAppend.history.dag lockMergeLeft lockMergeRight
      lockBaseBob := by
  rw [lockParallel_history_eq]
  exact parallel_right_maximal lvDag .alice .bob lock_bob_not_reaches_alice

theorem lockParallel_no_lowest :
    ¬ ∃ base, LowestCommonBase lockParallelAppend.history.dag
      lockMergeLeft lockMergeRight base := by
  rw [lockParallel_history_eq]
  exact parallel_no_lowest lvDag .alice .bob (by decide)
    lock_alice_not_reaches_bob lock_bob_not_reaches_alice

def lockResolvedSelect (_ : History LockParallelVersion Lock LockOp)
    (left right : LockParallelVersion) : MergeModel.BaseDecision LockParallelVersion :=
  if left = lockMergeLeft ∧ right = lockMergeRight then
    .ambiguous lockBaseAlice lockBaseBob
  else
    .unavailable

def lockResolvedScope (H : History LockParallelVersion Lock LockOp)
    (left right : LockParallelVersion) : Prop :=
  H.dag = lockParallelAppend.history.dag ∧
    left = lockMergeLeft ∧ right = lockMergeRight

theorem lockResolvedSelect_sound : ∀ H left right,
    lockResolvedScope H left right →
      ValidInHistory H left right (lockResolvedSelect H left right) := by
  rintro H left right ⟨dagEq, rfl, rfl⟩
  simp only [lockResolvedSelect, true_and, ↓reduceIte]
  change MaximalCommonBase H.dag lockMergeLeft lockMergeRight lockBaseAlice ∧
    MaximalCommonBase H.dag lockMergeLeft lockMergeRight lockBaseBob ∧
    lockBaseAlice ≠ lockBaseBob
  rw [dagEq]
  exact ⟨lockParallel_alice_maximal, lockParallel_bob_maximal, by decide⟩

def lockResolvedPolicy : HistoryMerge LockParallelVersion Lock LockOp :=
  explicit lockAM lockPriority lockResolvedSelect lockResolvedScope
    lockResolvedSelect_sound

def liftThroughParallelAppend
    {base tip : LVer ⊕ Unit}
    (patch : VersionPatch lockFirstAppend.history lockOps base tip) :
    VersionPatch lockParallelAppend.history lockOps (.inl base) (.inl tip) := by
  rw [lockParallelAppend.history_eq]
  exact liftVersionPatch patch

def lockResolvedCommon :
    CommonAppendRequest lockParallelAppend.history lockOps AtMostOne
      lockMergeLeft lockMergeRight where
  base := lockBaseAlice
  leftPatch := liftThroughParallelAppend lockFirstAppend.leftResidual
  rightPatch := lockParallelAppend.leftResidual
  base_legal := by decide
  left_legal := lockFirstAppend.admission.legal
  right_legal := lockParallelAppend.admission.legal

def lockResolvedRequest :
    ResolvedAmbiguousRequest lockResolvedPolicy lockParallelAppend.history
      lockOps AtMostOne lockMergeLeft lockMergeRight where
  first := lockBaseAlice
  second := lockBaseBob
  inScope := ⟨rfl, rfl, rfl⟩
  decision_eq := by simp [lockResolvedPolicy, explicit, lockResolvedSelect]
  chosen := lockBaseAlice
  chosen_named := Or.inl rfl
  common := lockResolvedCommon
  common_base_eq := rfl

def lockSecondRound : ResolvedAppend rfl lockParallelAppend.coherent
    cheapLockAlgebra.toAlgebra lockResolvedRequest :=
  appendResolved rfl lockParallelAppend.coherent cheapLockAlgebra.toAlgebra
    lockResolvedRequest

/-- The promised bounded result: two independent first-round merge versions
form an honest criss-cross ambiguity with no lowest base, yet an explicit
policy-named resolution appends a coherent and legal second-round merge while
retaining its exact origin and base-to-fresh patch. -/
theorem lock_two_round_criss_cross_fixture :
    lockParallelAppend.history.Coherent lockAM lockOps.impl ∧
      (¬ ∃ base, LowestCommonBase lockParallelAppend.history.dag
        lockMergeLeft lockMergeRight base) ∧
      lockSecondRound.appended.history.Coherent lockAM lockOps.impl ∧
      AtMostOne lockSecondRound.appended.admission.merged ∧
      lockSecondRound.appended.history.origin (.inr ()) =
        .merged (.inl lockBaseAlice) (.inl lockMergeLeft) (.inl lockMergeRight) :=
  ⟨lockParallelAppend.coherent, lockParallel_no_lowest,
    lockSecondRound.appended.coherent, lockSecondRound.appended.admission.legal,
    lockSecondRound.origin_records_resolution⟩

/-- Retained operational evidence makes the bounded result usable by a later
explicit step; no endpoint-to-patch reconstruction is assumed. -/
def lockSecondRound_base_to_fresh :
    VersionPatch lockSecondRound.appended.history lockOps
      (.inl lockBaseAlice) (.inr ()) :=
  lockSecondRound.appended.baseToFreshViaLeft

theorem lock_parallel_fresh_ids_distinct : lockMergeLeft ≠ lockMergeRight := by
  intro equal
  cases equal

theorem lock_second_round_fresh_ne_old (version : LockParallelVersion) :
    (Sum.inr () : LockParallelVersion ⊕ Unit) ≠ .inl version := by
  intro equal
  cases equal

theorem lock_second_round_base_reaches_fresh :
    Reaches lockSecondRound.appended.history.dag
      (.inl lockBaseAlice) (.inr ()) :=
  lockSecondRound_base_to_fresh.versions

end Uwueave.ResolvedHistoryGrowth
