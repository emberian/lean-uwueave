/-
# Uwueave.HistoryRuntime -- total finite history decisions and causal append

This module closes the explicitly finite part of the history frontier.  A
covering `FiniteHistory.Enumeration` makes the fourth `PairDecision.refused`
branch impossible: every nonempty finite set of common ancestors has a maximal
extension; one maximal element is a lowest base, while more than one is an
honest ambiguity.

The second half is an executable causal event-set boundary.  Exact retries are
idempotent and identifier collisions are refused. The small `append` core
requires every parent immediately; the `DeliveryState` endpoint adds an
explicit bounded buffer and deterministic finite draining for out-of-order
arrival. Identifiers are caller-supplied equality keys, not authentication.

The construction remains `Type 0`, inherits the caller-supplied rank and finite
coverage premises, and does not discover an enumeration for an infinite DAG.
-/
import Uwueave.HistoryEngine

namespace Uwueave.HistoryRuntime

open Uwueave Uwueave.Ancestral Uwueave.Histories
open Uwueave.FiniteHistory Uwueave.HistoryBase Uwueave.HistoryPolicy
open Uwueave.HistoryEngine Uwueave.CompositeDelta

set_option autoImplicit false

/-! ## 1. Finite refusal is impossible -/

private def decisionBool {P : Prop} : Decidable P → Bool
  | isTrue _ => true
  | isFalse _ => false

private theorem decisionBool_eq_true {P : Prop} (d : Decidable P) :
    decisionBool d = true ↔ P := by
  cases d with
  | isTrue h => simp [decisionBool, h]
  | isFalse h => simp [decisionBool, h]

/-- Common ancestors at or above `start`, as an exhaustive finite list. -/
def extensions {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y start : V) : List V :=
  F.vertices.filter fun candidate =>
    decisionBool (F.decideCommonAncestor x y candidate) &&
      decisionBool (F.decideReaches start candidate)

theorem mem_extensions_iff {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y start candidate : V) :
    candidate ∈ extensions F x y start ↔
      CommonAncestor D x y candidate ∧ Reaches D start candidate := by
  simp [extensions, decisionBool_eq_true, F.complete]

/-- Every common ancestor in a covered finite ranked DAG reaches a maximal
common ancestor.  Choosing maximum rank among its common descendants makes the
proof executable and avoids any classical carrier-level choice. -/
theorem exists_maximal_above {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) {x y start : V} (common : CommonAncestor D x y start) :
    ∃ top, MaximalCommonBase D x y top ∧ Reaches D start top := by
  let candidates := extensions F x y start
  have startMem : start ∈ candidates := by
    exact (mem_extensions_iff F x y start start).2
      ⟨common, Reaches.refl D start⟩
  have nonempty : candidates ≠ [] := List.ne_nil_of_mem startMem
  let top := candidates.maxOn D.rank nonempty
  have topMem : top ∈ candidates := List.maxOn_mem
  have topFacts := (mem_extensions_iff F x y start top).1 topMem
  refine ⟨top, ⟨topFacts.1, ?_⟩, topFacts.2⟩
  intro candidate candidateCommon topReaches
  have candidateMem : candidate ∈ candidates :=
    (mem_extensions_iff F x y start candidate).2
      ⟨candidateCommon, topFacts.2.trans topReaches⟩
  have rankLe : D.rank candidate ≤ D.rank top :=
    List.le_apply_maxOn_of_mem candidateMem
  rcases topReaches.eq_or_rank_lt with equal | rankLt
  · exact equal.symm
  · exact False.elim (Nat.not_lt_of_ge rankLe rankLt)

/-- The proof payload of `PairDecision.refused` contradicts finite coverage. -/
theorem refused_impossible {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) {x y : V} (common : List V)
    (_commonExact : ∀ b, b ∈ common ↔ CommonAncestor D x y b)
    (noLowest : ¬ ∃ b, LowestCommonBase D x y b)
    (commonNotAbsent : ¬ (∀ b, ¬ CommonAncestor D x y b))
    (noAmbiguity : ¬ ∃ b₁ b₂, MaximalCommonBase D x y b₁ ∧
      MaximalCommonBase D x y b₂ ∧ b₁ ≠ b₂) : False := by
  classical
  have someCommon : ∃ b, CommonAncestor D x y b := by
    exact Classical.byContradiction fun absent => commonNotAbsent
      (fun candidate candidateCommon => absent ⟨candidate, candidateCommon⟩)
  obtain ⟨seed, seedCommon⟩ := someCommon
  obtain ⟨top, topMaximal, seedToTop⟩ := exists_maximal_above F seedCommon
  apply noLowest
  refine ⟨top, topMaximal.1, ?_⟩
  intro candidate candidateCommon
  obtain ⟨candidateTop, candidateMaximal, candidateReaches⟩ :=
    exists_maximal_above F candidateCommon
  have equal : candidateTop = top := by
    by_cases same : candidateTop = top
    · exact same
    · exact False.elim (noAmbiguity ⟨candidateTop, top, candidateMaximal,
        topMaximal, same⟩)
  simpa only [equal] using candidateReaches

/-- A covering finite enumeration eliminates the operational refusal branch. -/
theorem PairDecision.not_refused {V : Type} [DecidableEq V]
    {D : VersionDag V} {F : Enumeration D} {x y : V}
    (decision : PairDecision F x y) : decision.kind ≠ .refused := by
  cases decision with
  | selected => simp [PairDecision.kind]
  | ambiguous => simp [PairDecision.kind]
  | unavailable => simp [PairDecision.kind]
  | refused common exact noLowest notAbsent noAmbiguity =>
      exact False.elim
        (refused_impossible F common exact noLowest notAbsent noAmbiguity)

/-- Total proof-carrying finite merge-base selection. -/
def decideTotal {V : Type} [DecidableEq V] {D : VersionDag V}
    (F : Enumeration D) (x y : V) : BaseSelection D x y :=
  match decidePair F x y with
  | .selected base lowest _ _ => .selected base lowest
  | .ambiguous first second firstMax secondMax distinct _ _ =>
      .ambiguous first second firstMax secondMax distinct
  | .unavailable noneCommon _ _ => .unavailable noneCommon
  | .refused common exact noLowest notAbsent noAmbiguity =>
      False.elim (refused_impossible F common exact noLowest notAbsent noAmbiguity)

theorem decideTotal_valid {V S Op : Type} [DecidableEq V]
    (H : History V S Op) (F : Enumeration H.dag) (x y : V) :
    ValidInHistory H x y (FiniteHistory.toDecision (decideTotal F x y)) :=
  FiniteHistory.toDecision_valid (decideTotal F x y)

/-! ## 2. A total finite policy on one DAG schema -/

/-- A total selector for every pair of histories carrying the enumerated DAG.
The scope mentions only schema equality; it cannot hide individual pairs. -/
def finiteExplicit {V S Op : Type} [DecidableEq V]
    (H : History V S Op) (F : Enumeration H.dag)
    (kernel : AncestralMerge S) (conflict : S → S → S) :
    HistoryMerge V S Op :=
  explicit kernel conflict
    (fun _ x y => FiniteHistory.toDecision (decideTotal F x y))
    (fun candidate _ _ => candidate.dag = H.dag)
    (by
      intro candidate x y sameDag
      change ValidInHistory candidate x y
        (FiniteHistory.toDecision (decideTotal F x y))
      simpa [ValidInHistory, sameDag] using decideTotal_valid H F x y)

theorem finiteExplicit_scope_all_pairs {V S Op : Type} [DecidableEq V]
    (H : History V S Op) (F : Enumeration H.dag)
    (kernel : AncestralMerge S) (conflict : S → S → S) (x y : V) :
    (finiteExplicit H F kernel conflict).scope H x y := rfl

/-! ## 3. A finite sweep of higher semantic judgements -/

/-- Proof-carrying executable classification of a proposition. -/
inductive Check (P : Prop) where
  | passed (proof : P)
  | failed (refutation : ¬ P)

def Check.ofDecidable (P : Prop) (decision : Decidable P) : Check P :=
  match decision with
  | isTrue proof => .passed proof
  | isFalse refutation => .failed refutation

def Check.accepted {P : Prop} : Check P → Bool
  | .passed _ => true
  | .failed _ => false

theorem Check.accepted_eq_true_iff {P : Prop} (check : Check P) :
    check.accepted = true ↔ P := by
  cases check with
  | passed proof => simp [Check.accepted, proof]
  | failed refutation => simp [Check.accepted, refutation]

/-- Higher judgements retained for one ordered pair.  The caller supplies the
decision procedures for semantic predicates whose result carrier or contextual
equivalence domain is not enumerated by `F`. -/
structure HigherEntry {V S Op R : Type} [DecidableEq V] [MergeState S]
    (P : HistoryMerge V S Op) (H : History V S Op) (I : Invariant S)
    (observe : S → R) (F : Enumeration H.dag) where
  x : V
  y : V
  graph : BaseSelection H.dag x y
  baseRobust : Check (BaseRobustAt P H I observe x y)
  selectorSafe : Check (P.scope H x y → I (H.state x) → I (H.state y) →
    I (P.result H x y))

/-- Sweep the graph decision plus `BaseRobustAt` and pairwise selector safety
over every ordered pair in source enumeration order. -/
def higherSweep {V S Op R : Type} [DecidableEq V] [MergeState S]
    (P : HistoryMerge V S Op) (H : History V S Op) (F : Enumeration H.dag)
    (I : Invariant S) (observe : S → R)
    (decRobust : ∀ x y, Decidable (BaseRobustAt P H I observe x y))
    (decSafe : ∀ x y, Decidable
      (P.scope H x y → I (H.state x) → I (H.state y) → I (P.result H x y))) :
    List (HigherEntry P H I observe F) :=
  F.vertices.flatMap fun x => F.vertices.map fun y =>
    { x := x
      y := y
      graph := decideTotal F x y
      baseRobust := Check.ofDecidable _ (decRobust x y)
      selectorSafe := Check.ofDecidable _ (decSafe x y) }

theorem higherSweep_complete {V S Op R : Type} [DecidableEq V] [MergeState S]
    (P : HistoryMerge V S Op) (H : History V S Op) (F : Enumeration H.dag)
    (I : Invariant S) (observe : S → R)
    (decRobust : ∀ x y, Decidable (BaseRobustAt P H I observe x y))
    (decSafe : ∀ x y, Decidable
      (P.scope H x y → I (H.state x) → I (H.state y) → I (P.result H x y)))
    (x y : V) :
    ∃ entry, entry ∈ higherSweep P H F I observe decRobust decSafe ∧
      entry.x = x ∧ entry.y = y := by
  let entry : HigherEntry P H I observe F :=
    { x := x
      y := y
      graph := decideTotal F x y
      baseRobust := Check.ofDecidable _ (decRobust x y)
      selectorSafe := Check.ofDecidable _ (decSafe x y) }
  refine ⟨entry, ?_, rfl, rfl⟩
  simp only [higherSweep, List.mem_flatMap, List.mem_map]
  exact ⟨x, F.complete x, y, F.complete y, rfl⟩

/-- Whole-policy judgements classified beside the finite pair sweep.  Their
decision procedures remain explicit inputs: finite version coverage decides
graph quantification, not arbitrary propositions over `S`, `R`, or all other
histories. -/
structure HigherClassification {V S Op R : Type} [MergeState S]
    (P : HistoryMerge V S Op) (H : History V S Op) (I : Invariant S)
    (observe : S → R) where
  baseRobust : Check (BaseRobust P H I observe)
  selectorSafe : Check (SelectorSafe P H I)
  ambiguityExplicit : Check (AmbiguityExplicit P)
  selectorSymmetric : Check (SelectorSymmetric P)
  reconcileSymmetric : Check (ReconcileSymmetric P)
  recordDetermined : Check (RecordDetermined P)
  historyConvergent : Check (HistoryConvergent P)

def classifyHigher {V S Op R : Type} [MergeState S]
    (P : HistoryMerge V S Op) (H : History V S Op) (I : Invariant S)
    (observe : S → R)
    (decBaseRobust : Decidable (BaseRobust P H I observe))
    (decSelectorSafe : Decidable (SelectorSafe P H I))
    (decAmbiguity : Decidable (AmbiguityExplicit P))
    (decSelectorSymmetry : Decidable (SelectorSymmetric P))
    (decReconcileSymmetry : Decidable (ReconcileSymmetric P))
    (decRecordDetermined : Decidable (RecordDetermined P))
    (decConvergent : Decidable (HistoryConvergent P)) :
    HigherClassification P H I observe where
  baseRobust := Check.ofDecidable _ decBaseRobust
  selectorSafe := Check.ofDecidable _ decSelectorSafe
  ambiguityExplicit := Check.ofDecidable _ decAmbiguity
  selectorSymmetric := Check.ofDecidable _ decSelectorSymmetry
  reconcileSymmetric := Check.ofDecidable _ decReconcileSymmetry
  recordDetermined := Check.ofDecidable _ decRecordDetermined
  historyConvergent := Check.ofDecidable _ decConvergent

/-! ## 4. Fresh merge-node append -/

def liftOrigin {V : Type} : Origin V → Origin (V ⊕ Unit)
  | .root => .root
  | .ran parent => .ran (.inl parent)
  | .merged base left right => .merged (.inl base) (.inl left) (.inl right)

theorem liftOrigin_eq_root_iff {V : Type} (origin : Origin V) :
    liftOrigin origin = .root ↔ origin = .root := by
  cases origin <;> simp [liftOrigin]

def appendDag {V : Type} [DecidableEq V] (D : VersionDag V) (left right : V) :
    VersionDag (V ⊕ Unit) where
  parent
    | .inl parent, .inl child => D.parent parent child
    | .inl parent, .inr _ => decide (parent = left ∨ parent = right)
    | .inr _, _ => false
  rank
    | .inl version => D.rank version
    | .inr _ => max (D.rank left) (D.rank right) + 1
  rank_lt := by
    intro parent child edge
    cases parent with
    | inl parent =>
        cases child with
        | inl child => exact D.rank_lt parent child edge
        | inr _unit =>
            simp only [decide_eq_true_eq] at edge
            rcases edge with rfl | rfl
            · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
            · exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
    | inr _unit => simp at edge

def appendHistory {V S Op : Type} [DecidableEq V] (H : History V S Op)
    (base left right : V) (merged : S) : History (V ⊕ Unit) S Op where
  dag := appendDag H.dag left right
  state
    | .inl version => H.state version
    | .inr _ => merged
  origin
    | .inl version => liftOrigin (H.origin version)
    | .inr _ => .merged (.inl base) (.inl left) (.inl right)
  root := .inl H.root

theorem appendDag_reaches_inl {V : Type} [DecidableEq V]
    {D : VersionDag V} {left right a b : V}
    (reaches : Reaches D a b) :
    Reaches (appendDag D left right) (.inl a) (.inl b) := by
  rcases reaches with rfl | ancestry
  · exact Reaches.refl _ _
  · right
    induction ancestry with
    | direct edge => exact .direct edge
    | extend ancestry edge ih => exact .extend ih edge

/-- Appending the result of `admitSelected` materializes both its
`SelectedAdmission` and a coherent fresh merge node. -/
structure AppendedSelected {V S Op : Type} [DecidableEq V]
    {P : HistoryMerge V S Op}
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S} {x y : V}
    (kernelCoherent : H.Coherent P.kernel g.impl)
    (algebra : Algebra P.kernel g I) (request : SelectedRequest P H g I x y) where
  admission : SelectedAdmission P H g I x y
  history : History (V ⊕ Unit) S Op
  history_eq : history = appendHistory H request.base x y admission.merged
  coherent : history.Coherent P.kernel g.impl

def appendSelected {V S Op : Type} [DecidableEq V] {P : HistoryMerge V S Op}
    {H : History V S Op} {g : Guarded S Op} {I : Invariant S} {x y : V}
    (kernelCoherent : H.Coherent P.kernel g.impl)
    (algebra : Algebra P.kernel g I) (request : SelectedRequest P H g I x y) :
    AppendedSelected kernelCoherent algebra request := by
  let admission := admitSelected algebra request
  let history := appendHistory H request.base x y admission.merged
  have mergedEq : admission.merged =
      P.kernel.merge3 (H.state request.base) (H.state x) (H.state y) := by
    rfl
  refine {
    admission := admission
    history := history
    history_eq := rfl
    coherent := ?_ }
  change (appendHistory H request.base x y admission.merged).Coherent
    P.kernel g.impl
  constructor
  · intro version rootOrigin
    cases version with
    | inl version =>
        change liftOrigin (H.origin version) = .root at rootOrigin
        have oldRoot := (liftOrigin_eq_root_iff (H.origin version)).1 rootOrigin
        change Sum.inl version = Sum.inl H.root
        exact congrArg Sum.inl (kernelCoherent.root_unique version oldRoot)
    | inr _unit => cases rootOrigin
  · intro version
    cases version with
    | inl version =>
        have old := kernelCoherent.nodes version
        cases originEq : H.origin version with
        | root =>
            simp [OriginOK, appendHistory, liftOrigin, originEq]
        | ran parent =>
            simp only [OriginOK, originEq] at old
            simpa [OriginOK, appendHistory, liftOrigin, originEq] using old
        | merged base left right =>
            simp only [OriginOK, originEq] at old
            rcases old with ⟨leftParent, rightParent, common, stateEq⟩
            simp only [OriginOK, appendHistory, liftOrigin, originEq]
            refine ⟨leftParent, rightParent, ?_, stateEq⟩
            exact ⟨appendDag_reaches_inl common.1,
              appendDag_reaches_inl common.2⟩
    | inr _unit =>
        change (appendDag H.dag x y).parent (.inl x) (.inr ()) = true ∧
          (appendDag H.dag x y).parent (.inl y) (.inr ()) = true ∧
          CommonAncestor (appendDag H.dag x y) (.inl x) (.inl y)
            (.inl request.base) ∧
          admission.merged =
            P.kernel.merge3 (H.state request.base) (H.state x) (H.state y)
        refine ⟨by simp [appendDag], by simp [appendDag], ?_, mergedEq⟩
        exact ⟨appendDag_reaches_inl request.left.versions,
          appendDag_reaches_inl request.right.versions⟩

/-- The existing selected lock fixture materialized as a fresh coherent merge
node, not merely as a state-level `SelectedAdmission`. -/
def lockForkAppended := appendSelected lockHistory_coherent
  cheapLockAlgebra.toAlgebra lockForkRequest

theorem lockForkAppended_coherent :
    lockForkAppended.history.Coherent lockForkPolicy.kernel lockOps.impl :=
  lockForkAppended.coherent

theorem lockForkAppended_legal : AtMostOne lockForkAppended.admission.merged :=
  lockForkAppended.admission.legal

/-! ## 5. Causal append and event-set convergence -/

structure Event (Id Payload : Type) where
  id : Id
  parents : List Id
  payload : Payload
  deriving DecidableEq, Repr

structure EventState (Id Payload : Type) where
  accepted : List (Event Id Payload)
  deriving DecidableEq, Repr

def EventState.empty {Id Payload : Type} : EventState Id Payload := ⟨[]⟩

def EventState.hasId {Id Payload : Type} [DecidableEq Id]
    (state : EventState Id Payload) (id : Id) : Bool :=
  state.accepted.any fun event => event.id == id

inductive AppendDecision (Id Payload : Type) where
  | appended (state : EventState Id Payload)
  | retry (state : EventState Id Payload)
  | collision (prior : Event Id Payload)
  | missingParent (parent : Id)
  | selfParent
  | duplicateParent
  deriving DecidableEq, Repr

/-- Immediate causal append.  Missing parents are refused, not buffered. -/
def append {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (state : EventState Id Payload) (event : Event Id Payload) :
    AppendDecision Id Payload :=
  if event ∈ state.accepted then
    .retry state
  else
    match state.accepted.find? (fun prior => prior.id == event.id) with
    | some prior => .collision prior
    | none =>
      if event.id ∈ event.parents then .selfParent
      else if ¬ event.parents.Nodup then .duplicateParent
      else
        match event.parents.find? (fun parent => ¬ state.hasId parent) with
        | some parent => .missingParent parent
        | none => .appended ⟨state.accepted ++ [event]⟩

theorem append_retry {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (state : EventState Id Payload) (event : Event Id Payload)
    (known : event ∈ state.accepted) : append state event = .retry state := by
  simp [append, known]

def SameEventSet {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (left right : EventState Id Payload) : Prop :=
  ∀ event, event ∈ left.accepted ↔ event ∈ right.accepted

/-- The extensional, arrival-order-independent view of an event state. -/
def eventSetView {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (state : EventState Id Payload) : Event Id Payload → Prop :=
  fun event => event ∈ state.accepted

theorem sameEventSet_refl {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (state : EventState Id Payload) : SameEventSet state state :=
  fun _ => Iff.rfl

theorem sameEventSet_lookup {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {left right : EventState Id Payload} (same : SameEventSet left right)
    (event : Event Id Payload) :
    (event ∈ left.accepted) = (event ∈ right.accepted) :=
  propext (same event)

/-- Equal full event sets produce definitionally comparable membership views. -/
theorem sameEventSet_view_eq {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {left right : EventState Id Payload} (same : SameEventSet left right) :
    eventSetView left = eventSetView right := by
  funext event
  exact propext (same event)

/-- Replica materializations that depend only on membership converge once the
complete event sets agree, independently of physical append order. -/
theorem sameEventSet_converges {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {left right : EventState Id Payload} (same : SameEventSet left right)
    (view : Event Id Payload → Bool) :
    (∀ event, event ∈ left.accepted → view event = true) ↔
      (∀ event, event ∈ right.accepted → view event = true) := by
  constructor <;> intro holds event member
  · exact holds event ((same event).2 member)
  · exact holds event ((same event).1 member)

/-! ## 6. Stable-id delivery with an explicit bounded buffer -/

/-- Runtime materialization plus a bounded, non-authoritative out-of-order
buffer.  Stable event identifiers, rather than nested sum constructors, name
every successive append. -/
structure DeliveryState (Id Payload : Type) where
  materialized : EventState Id Payload
  pending : List (Event Id Payload)
  capacity : Nat
  deriving DecidableEq, Repr

/-- The exported structure is inspectable, so boundedness is a named runtime
invariant rather than a hidden constructor premise. Public bounded-buffer
claims below are explicitly about states reachable from `empty` by successful
`receive` transitions, which preserve this predicate. -/
def DeliveryValid {Id Payload : Type} (state : DeliveryState Id Payload) : Prop :=
  state.pending.length ≤ state.capacity

def DeliveryState.empty (Id Payload : Type) (capacity : Nat) :
    DeliveryState Id Payload := ⟨EventState.empty, [], capacity⟩

theorem DeliveryState.empty_valid (Id Payload : Type) (capacity : Nat) :
    DeliveryValid (DeliveryState.empty Id Payload capacity) := by
  simp [DeliveryValid, DeliveryState.empty]

/-- One deterministic scan. Events which become ready only after an event to
their right are reconsidered by the next scan. -/
private def drainOnce {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (materialized : EventState Id Payload) :
    List (Event Id Payload) → EventState Id Payload × List (Event Id Payload)
  | [] => (materialized, [])
  | event :: rest =>
      match append materialized event with
      | .appended next => drainOnce next rest
      | _ =>
          let (next, waiting) := drainOnce materialized rest
          (next, event :: waiting)

private def drainFuel {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload] :
    Nat → EventState Id Payload → List (Event Id Payload) →
      EventState Id Payload × List (Event Id Payload)
  | 0, materialized, pending => (materialized, pending)
  | fuel + 1, materialized, pending =>
      let (next, waiting) := drainOnce materialized pending
      drainFuel fuel next waiting

private theorem drainOnce_pending_length_le {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (materialized : EventState Id Payload) (pending : List (Event Id Payload)) :
    (drainOnce materialized pending).2.length ≤ pending.length := by
  induction pending generalizing materialized with
  | nil => simp [drainOnce]
  | cons event rest ih =>
      cases decision : append materialized event with
      | appended next =>
          simpa [drainOnce, decision] using
            Nat.le_trans (ih next) (Nat.le_succ rest.length)
      | retry | collision | missingParent | selfParent | duplicateParent =>
          simpa [drainOnce, decision] using Nat.succ_le_succ (ih materialized)

private theorem drainFuel_pending_length_le {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (fuel : Nat) (materialized : EventState Id Payload)
    (pending : List (Event Id Payload)) :
    (drainFuel fuel materialized pending).2.length ≤ pending.length := by
  induction fuel generalizing materialized pending with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      simp only [drainFuel]
      rcases onceEq : drainOnce materialized pending with ⟨next, waiting⟩
      exact Nat.le_trans (ih next waiting)
        (by simpa [onceEq] using drainOnce_pending_length_le materialized pending)

/-- Repeated deterministic scans. `pending.length + 1` scans are enough for
every finite dependency chain already represented in the buffer; unavailable
external parents remain explicitly pending. -/
def drain {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (materialized : EventState Id Payload) (pending : List (Event Id Payload)) :
    EventState Id Payload × List (Event Id Payload) :=
  drainFuel (pending.length + 1) materialized pending

theorem drain_pending_length_le {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (materialized : EventState Id Payload) (pending : List (Event Id Payload)) :
    (drain materialized pending).2.length ≤ pending.length :=
  drainFuel_pending_length_le _ _ _

inductive ReceiveDecision (Id Payload : Type) where
  | delivered (state : DeliveryState Id Payload)
  | buffered (state : DeliveryState Id Payload)
  | retry (state : DeliveryState Id Payload)
  | collision (prior : Event Id Payload)
  | bufferFull (capacity : Nat)
  | selfParent
  | duplicateParent
  deriving DecidableEq, Repr

/-- Receive one stable-id event. Exact accepted or buffered delivery is a
retry; conflicting reuse is refused across both stores. Missing-parent events
occupy one explicit buffer slot, and a successful causal append drains every
now-ready finite dependency layer deterministically. -/
def receive {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (state : DeliveryState Id Payload) (event : Event Id Payload) :
    ReceiveDecision Id Payload :=
  if event ∈ state.materialized.accepted ∨ event ∈ state.pending then
    .retry state
  else
    match (state.materialized.accepted ++ state.pending).find?
        (fun prior => prior.id == event.id) with
    | some prior => .collision prior
    | none =>
      if event.id ∈ event.parents then .selfParent
      else if ¬ event.parents.Nodup then .duplicateParent
      else
        match event.parents.find? (fun parent => ¬ state.materialized.hasId parent) with
        | some _ =>
            if state.pending.length < state.capacity then
              .buffered { state with pending := state.pending ++ [event] }
            else .bufferFull state.capacity
        | none =>
            match append state.materialized event with
            | .appended next =>
                let (settled, waiting) := drain next state.pending
                .delivered { state with materialized := settled, pending := waiting }
            | .retry _ => .retry state
            | .collision prior => .collision prior
            | .missingParent _ => .bufferFull state.capacity
            | .selfParent => .selfParent
            | .duplicateParent => .duplicateParent

theorem receive_retry {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload]
    (state : DeliveryState Id Payload) (event : Event Id Payload)
    (known : event ∈ state.materialized.accepted ∨ event ∈ state.pending) :
    receive state event = .retry state := by
  simp [receive, known]

/-- A successful buffering decision never exceeds the state's written bound,
even if the caller supplied an otherwise arbitrary state. -/
theorem receive_buffered_within_capacity {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {state next : DeliveryState Id Payload} {event : Event Id Payload}
    (buffered : receive state event = .buffered next) :
    next.pending.length ≤ next.capacity := by
  simp only [receive] at buffered
  grind [DeliveryValid]

theorem receive_delivered_within_capacity {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {state next : DeliveryState Id Payload} {event : Event Id Payload}
    (valid : DeliveryValid state)
    (delivered : receive state event = .delivered next) :
    DeliveryValid next := by
  simp only [receive] at delivered
  split at delivered <;> try contradiction
  split at delivered <;> try contradiction
  split at delivered <;> try contradiction
  split at delivered <;> try contradiction
  split at delivered <;> try contradiction
  split at delivered <;> try contradiction
  next ready =>
    cases decision : append state.materialized event with
    | appended settled =>
        simp only [decision] at delivered
        cases delivered
        exact Nat.le_trans (drain_pending_length_le settled state.pending) valid
    | retry | collision | missingParent | selfParent | duplicateParent =>
        simp [decision] at delivered

theorem receive_retry_state {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {state next : DeliveryState Id Payload} {event : Event Id Payload}
    (retry : receive state event = .retry next) : next = state := by
  simp only [receive] at retry
  split at retry
  · exact (ReceiveDecision.retry.inj retry).symm
  split at retry <;> try contradiction
  split at retry <;> try contradiction
  split at retry <;> try contradiction
  split at retry <;> try contradiction
  split at retry <;> try contradiction
  next ready =>
    cases decision : append state.materialized event with
    | retry source =>
        simp only [decision] at retry
        exact (ReceiveDecision.retry.inj retry).symm
    | appended | collision | missingParent | selfParent | duplicateParent =>
        simp [decision] at retry

/-- Every transition which returns a successor preserves the bound. This is
the exact operational sense in which the buffer is bounded from `empty`. -/
theorem receive_success_valid {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {state next : DeliveryState Id Payload} {event : Event Id Payload}
    (valid : DeliveryValid state)
    (success : receive state event = .delivered next ∨
      receive state event = .buffered next ∨
      receive state event = .retry next) :
    DeliveryValid next := by
  rcases success with delivered | buffered | retry
  · exact receive_delivered_within_capacity valid delivered
  · exact receive_buffered_within_capacity buffered
  · rw [receive_retry_state retry]
    exact valid

def SettledSameEventSet {Id Payload : Type} [DecidableEq Id]
    [DecidableEq Payload] (left right : DeliveryState Id Payload) : Prop :=
  left.pending = [] ∧ right.pending = [] ∧
    SameEventSet left.materialized right.materialized

theorem SettledSameEventSet.view_eq {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {left right : DeliveryState Id Payload}
    (same : SettledSameEventSet left right) :
    eventSetView left.materialized = eventSetView right.materialized :=
  sameEventSet_view_eq same.2.2

/-! ### Two successive criss-cross merges over stable natural identifiers -/

def runtimeRoot : Event Nat String := ⟨0, [], "root"⟩
def runtimeLeft : Event Nat String := ⟨1, [0], "left"⟩
def runtimeRight : Event Nat String := ⟨2, [0], "right"⟩
def runtimeMergeLeft : Event Nat String := ⟨3, [1, 2], "merge-left"⟩
def runtimeMergeRight : Event Nat String := ⟨4, [1, 2], "merge-right"⟩
def runtimeTip : Event Nat String := ⟨5, [3, 4], "merge-tip"⟩

def runtimeCausalOrder : List (Event Nat String) :=
  [runtimeRoot, runtimeLeft, runtimeRight, runtimeMergeLeft,
    runtimeMergeRight, runtimeTip]

def runtimeReverseOrder : List (Event Nat String) :=
  [runtimeTip, runtimeMergeRight, runtimeMergeLeft, runtimeRight,
    runtimeLeft, runtimeRoot]

def receiveAll {Id Payload : Type} [DecidableEq Id] [DecidableEq Payload] :
    DeliveryState Id Payload → List (Event Id Payload) →
      Option (DeliveryState Id Payload)
  | state, [] => some state
  | state, event :: rest =>
      match receive state event with
      | .delivered next | .buffered next | .retry next => receiveAll next rest
      | _ => none

theorem receiveAll_success_valid {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    {initial final : DeliveryState Id Payload}
    {events : List (Event Id Payload)} (valid : DeliveryValid initial)
    (success : receiveAll initial events = some final) : DeliveryValid final := by
  induction events generalizing initial with
  | nil =>
      simp only [receiveAll, Option.some.injEq] at success
      subst final
      exact valid
  | cons event rest ih =>
      cases decision : receive initial event with
      | delivered next =>
          exact ih (receive_success_valid valid (Or.inl decision))
            (by simpa [receiveAll, decision] using success)
      | buffered next =>
          exact ih (receive_success_valid valid (Or.inr (Or.inl decision)))
            (by simpa [receiveAll, decision] using success)
      | retry next =>
          exact ih (receive_success_valid valid (Or.inr (Or.inr decision)))
            (by simpa [receiveAll, decision] using success)
      | collision | bufferFull | selfParent | duplicateParent =>
          simp [receiveAll, decision] at success

def runtimeCausalState : DeliveryState Nat String :=
  ⟨⟨runtimeCausalOrder⟩, [], 5⟩

def runtimeReverseSettledState : DeliveryState Nat String :=
  ⟨⟨[runtimeRoot, runtimeRight, runtimeLeft, runtimeMergeRight,
      runtimeMergeLeft, runtimeTip]⟩, [], 5⟩

theorem runtime_causal_order_exact :
    receiveAll (DeliveryState.empty Nat String 5) runtimeCausalOrder =
      some runtimeCausalState := rfl

theorem runtime_reverse_order_settles :
    receiveAll (DeliveryState.empty Nat String 5) runtimeReverseOrder =
      some runtimeReverseSettledState := rfl

theorem runtime_reverse_order_respects_capacity :
    DeliveryValid runtimeReverseSettledState :=
  receiveAll_success_valid (DeliveryState.empty_valid Nat String 5)
    runtime_reverse_order_settles

theorem runtime_orders_converge :
    SettledSameEventSet runtimeCausalState runtimeReverseSettledState := by
  simp [SettledSameEventSet, SameEventSet, runtimeCausalState,
    runtimeReverseSettledState, runtimeCausalOrder, or_comm, or_left_comm]

theorem runtime_duplicate_retry :
    receive runtimeCausalState runtimeTip = .retry runtimeCausalState := rfl

theorem runtime_buffer_bound_refuses :
    receive (DeliveryState.empty Nat String 0) runtimeTip = .bufferFull 0 := rfl

def runtimeTipBufferedState : DeliveryState Nat String :=
  ⟨EventState.empty, [runtimeTip], 5⟩

def runtimeForgedTip : Event Nat String := ⟨5, [3, 4], "forged-tip"⟩

theorem runtime_buffered_retry :
    receive runtimeTipBufferedState runtimeTip = .retry runtimeTipBufferedState := rfl

theorem runtime_pending_collision_refused :
    receive runtimeTipBufferedState runtimeForgedTip = .collision runtimeTip := rfl

/-! ## 7. Asymmetry versus convergence and exact conditioned necessity -/

/-- Pairwise order agreement at the observable policy output. -/
def OrderAgreementAt {V S Op : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) : Prop :=
  (P.apply H x y).state = (P.apply H y x).state

/-- On the actual states and decisions at a pair, the reconciler distinguishes
different decisions after accounting for the swapped argument order. -/
def DecisionSeparatingAt {V S Op : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (x y : V) : Prop :=
  ∀ left right : MergeModel.BaseDecision V,
    (P.reconcile (stateDecision H left) (H.state x) (H.state y)).state =
      (P.reconcile (stateDecision H right) (H.state x) (H.state y)).state →
        left = right

/-- Under reconcile symmetry and decision separation, selector symmetry is not
merely sufficient: it is exactly necessary for pairwise order agreement. -/
theorem orderAgreement_iff_selector_symmetric_at {V S Op : Type}
    (P : HistoryMerge V S Op) (H : History V S Op) (x y : V)
    (reconcileSymmetric : ReconcileSymmetric P)
    (separating : DecisionSeparatingAt P H x y) :
    OrderAgreementAt P H x y ↔ P.select H x y = P.select H y x := by
  constructor
  · intro agrees
    apply separating
    calc
      (P.reconcile (stateDecision H (P.select H x y))
          (H.state x) (H.state y)).state =
          (P.reconcile (stateDecision H (P.select H y x))
            (H.state y) (H.state x)).state := agrees
      _ = (P.reconcile (stateDecision H (P.select H y x))
            (H.state x) (H.state y)).state :=
        (reconcileSymmetric _ _ _).symm
  · intro selectorEq
    unfold OrderAgreementAt HistoryMerge.apply HistoryMerge.decisionAt
    rw [selectorEq]
    exact reconcileSymmetric _ _ _

/-- An order-sensitive selector whose two answers are both licensed by the
criss-cross DAG. -/
def ccOrderSelect (_ : History Ver Nat Unit) :
    Ver → Ver → MergeModel.BaseDecision Ver
  | .mergeL, .mergeR => .ambiguous .left .right
  | .mergeR, .mergeL => .ambiguous .right .left
  | _, _ => .selected .root

theorem ccOrderSelect_sound : ∀ H x y, ccScope H x y →
    ValidInHistory H x y (ccOrderSelect H x y) := by
  rintro H x y ⟨sameDag, ordered | ordered⟩ <;>
    obtain ⟨rfl, rfl⟩ := ordered
  · change MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [sameDag]
    exact ⟨cc_left_maximal, cc_right_maximal, by decide⟩
  · change MaximalCommonBase H.dag _ _ _ ∧ MaximalCommonBase H.dag _ _ _ ∧ _
    rw [sameDag]
    exact ⟨maximalCommonBase_symm cc_right_maximal,
      maximalCommonBase_symm cc_left_maximal, by decide⟩

def ccOrderPolicy : HistoryMerge Ver Nat Unit :=
  explicit counterAM (fun left right => max left right)
    ccOrderSelect ccScope ccOrderSelect_sound

/-- History convergence does not imply selector symmetry.  This policy is
record-determined, hence convergent, while its two ordered ambiguous answers
reverse the base pair. -/
theorem asymmetric_but_convergent :
    HistoryConvergent ccOrderPolicy ∧ ¬ SelectorSymmetric ccOrderPolicy := by
  refine ⟨recordDetermined_converges
      (recordDetermined_of_constant (fun _ _ _ _ => rfl)), ?_⟩
  intro symmetric
  have := symmetric ccHistory .mergeL .mergeR
  simp [ccOrderPolicy, explicit, ccOrderSelect] at this

/-! ## Deliberate boundary

The total selector above depends on an explicit finite `Enumeration` whose
covering proof supplies every version; it does not claim total synthesis for
arbitrary infinite DAGs.  This module also inherits the current `Type`/`Type 0`
universe boundary of `Histories` and `MergeModel`.  Finally, `Event` is an
endpoint/runtime envelope with an opaque payload.  We do not yet claim a codec
or refinement theorem reconstructing a generic proof-indexed `History`,
`SelectedAdmission`, or `Coherent` witness from stored host bytes.  Network
authentication remains outside this slice. The logical event layer requires a
duplicate-free parent list but does not canonicalize its order; the separate
Rust journal deliberately requires strictly increasing parent bytes. No
Lean-to-Rust codec/refinement theorem relates those choices. The buffer bound
is proved for states reachable from `DeliveryState.empty` through successful
`receive` transitions; arbitrary public structure literals carry no such fact.
-/

end Uwueave.HistoryRuntime
