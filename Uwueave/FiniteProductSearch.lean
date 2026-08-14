/-
# Uwueave.FiniteProductSearch — exact search over declared finite products

This module is a downstream search kernel.  It accepts only proof-carrying
finite carriers, checks explicit work caps before materialising exponential
search spaces, and returns evidence in both the found and refused branches.

Its claims are intentionally local to the supplied carrier, palette, relation,
and product axes.  It does not enumerate an arbitrary universe, infer that an
operational table models a deployment, or impose an order on a domain-specific
price record.
-/
import Uwueave.ClashGraph

namespace Uwueave.FiniteProductSearch

open Uwueave

universe u v w

/-! ## Proof-carrying finite carriers and resource results -/

/-- A duplicate-free complete enumeration.  `complete`, not list membership by
convention, licenses whole-type finite conclusions. -/
structure Carrier (α : Type u) where
  values : List α
  nodup : values.Nodup
  complete : ∀ x : α, x ∈ values

def decideForallMem {α : Type u} (values : List α) (P : α → Prop)
    (decideP : ∀ value, Decidable (P value)) :
    Decidable (∀ value ∈ values, P value) :=
  match values with
  | [] => isTrue (by simp)
  | head :: tail =>
      match decideP head with
      | isFalse hhead =>
          isFalse (fun hall => hhead (hall head List.mem_cons_self))
      | isTrue hhead =>
          match decideForallMem tail P decideP with
          | isFalse htail =>
              isFalse (fun hall => htail (fun value hmem =>
                hall value (List.mem_cons_of_mem head hmem)))
          | isTrue htail =>
              isTrue (fun value hmem => by
                rcases List.mem_cons.mp hmem with rfl | hmem
                · exact hhead
                · exact htail value hmem)

/-- Work caps are independent because the search spaces have different growth
rates and refusal should identify the resource which stopped evaluation. -/
structure Limits where
  maxStates : Nat
  maxOperations : Nat
  maxColorings : Nat
  maxSubsets : Nat
  maxProducts : Nat
  deriving DecidableEq, Repr

inductive LimitAxis where
  | states
  | operations
  | colorings
  | subsets
  | products
  deriving DecidableEq, Repr

/-- Resource refusal is not semantic refusal. -/
inductive Capped (α : Type u) where
  | ready (value : α)
  | tooLarge (axis : LimitAxis) (required maximum : Nat)

namespace Capped

def isReady {α : Type u} : Capped α → Bool
  | .ready _ => true
  | .tooLarge .. => false

def refusalAxis? {α : Type u} : Capped α → Option LimitAxis
  | .ready _ => none
  | .tooLarge axis .. => some axis

end Capped

/-! ## Computed finite reachability -/

structure ProtocolInput (S : Type u) (Op : Type v) where
  states : Carrier S
  operations : Carrier Op
  step : S → Op → S

def ProtocolInput.expand {S : Type u} {Op : Type v} [DecidableEq S]
    (input : ProtocolInput S Op) (seen : List S) : List S :=
  (seen ++ seen.flatMap fun state =>
    input.operations.values.map (input.step state)).eraseDups

def ProtocolInput.layers {S : Type u} {Op : Type v} [DecidableEq S]
    (input : ProtocolInput S Op) : Nat → List S → List S
  | 0, seen => seen
  | fuel + 1, seen => input.layers fuel (input.expand seen)

/-- The closure is computed from `states`, `operations`, and `step`.  One
extra layer is used only by the checker below to certify stabilization. -/
def ProtocolInput.reachableStates {S : Type u} {Op : Type v} [DecidableEq S]
    (input : ProtocolInput S Op) (base : S) : List S :=
  input.layers input.states.values.length [base]

theorem ProtocolInput.mem_expand_self {S : Type u} {Op : Type v}
    [DecidableEq S] (input : ProtocolInput S Op) {seen : List S} {state : S}
    (h : state ∈ seen) : state ∈ input.expand seen := by
  simp [ProtocolInput.expand, h]

theorem ProtocolInput.mem_layers_mono {S : Type u} {Op : Type v}
    [DecidableEq S] (input : ProtocolInput S Op) :
    ∀ fuel seen state, state ∈ seen → state ∈ input.layers fuel seen
  | 0, _, _, h => h
  | fuel + 1, seen, state, h =>
      input.mem_layers_mono fuel (input.expand seen) state
        (input.mem_expand_self h)

theorem ProtocolInput.mem_expand_sound {S : Type u} {Op : Type v}
    [DecidableEq S] (input : ProtocolInput S Op)
    {base state : S} {seen : List S}
    (hsound : ∀ current ∈ seen,
      LiveSegmented.Reachable
        ({ step := input.step, observe := id } :
          LiveSegmented.RunModel S Op S) base current)
    (hstate : state ∈ input.expand seen) :
    LiveSegmented.Reachable
      ({ step := input.step, observe := id } :
        LiveSegmented.RunModel S Op S) base state := by
  simp only [ProtocolInput.expand, List.mem_eraseDups,
    List.mem_append, List.mem_flatMap, List.mem_map] at hstate
  rcases hstate with hold | ⟨current, hcurrent, operation, _, rfl⟩
  · exact hsound state hold
  · exact LiveSegmented.reachable_trans (hsound current hcurrent)
      ⟨[operation], rfl⟩

theorem ProtocolInput.mem_layers_sound_from {S : Type u} {Op : Type v}
    [DecidableEq S] (input : ProtocolInput S Op) (base : S) :
    ∀ fuel seen,
      (∀ current ∈ seen,
        LiveSegmented.Reachable
          ({ step := input.step, observe := id } :
            LiveSegmented.RunModel S Op S) base current) →
      ∀ state, state ∈ input.layers fuel seen →
        LiveSegmented.Reachable
          ({ step := input.step, observe := id } :
            LiveSegmented.RunModel S Op S) base state
  | 0, seen, hsound, state, hstate => hsound state hstate
  | fuel + 1, seen, hsound, state, hstate =>
      input.mem_layers_sound_from base fuel (input.expand seen)
        (fun current hcurrent =>
          input.mem_expand_sound hsound hcurrent)
        state hstate

theorem ProtocolInput.mem_reachableStates_sound {S : Type u} {Op : Type v}
    [DecidableEq S] (input : ProtocolInput S Op) (base state : S)
    (h : state ∈ input.reachableStates base) :
    LiveSegmented.Reachable
      ({ step := input.step, observe := id } :
        LiveSegmented.RunModel S Op S) base state := by
  apply input.mem_layers_sound_from base input.states.values.length [base]
  · intro current hcurrent
    have heq : current = base := by simpa using hcurrent
    subst current
    exact LiveSegmented.reachable_refl _ _
  · exact h

/-- Stabilization is checked from the two computed successive layers. -/
def ProtocolInput.closedB {S : Type u} {Op : Type v} [DecidableEq S]
    (input : ProtocolInput S Op) : Bool :=
  let reached := input.reachableStates
  input.states.values.all fun base =>
    (reached base).all fun state =>
      input.operations.values.all fun operation =>
        (reached base).contains (input.step state operation)

theorem ProtocolInput.closedB_spec {S : Type u} {Op : Type v}
    [DecidableEq S] (input : ProtocolInput S Op)
    (hclosed : input.closedB = true) :
    ∀ base current, current ∈ input.reachableStates base →
      ∀ operation, input.step current operation ∈ input.reachableStates base := by
  intro base current hcurrent operation
  have hbase := List.all_eq_true.mp hclosed base (input.states.complete base)
  have hstate := List.all_eq_true.mp hbase current hcurrent
  have hop := List.all_eq_true.mp hstate operation
    (input.operations.complete operation)
  exact List.contains_iff_mem.mp hop

/-- An accepted scope contains no authored reachability table.  It contains the
computed closure and the Boolean stabilization certificate checked above. -/
structure ProtocolScope (S : Type u) (Op : Type v) [MergeState S]
    [DecidableEq S] extends ProtocolInput S Op where
  closed : toProtocolInput.closedB = true

inductive ProtocolCheck (S : Type u) (Op : Type v) [MergeState S]
    [DecidableEq S] (input : ProtocolInput S Op) (limits : Limits) where
  | accepted (scope : ProtocolScope S Op)
      (inputExact : scope.toProtocolInput = input)
  | tooLarge (axis : LimitAxis) (required maximum : Nat)
  | notClosed (failure : input.closedB = false)

def checkProtocol {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] (input : ProtocolInput S Op) (limits : Limits) :
    ProtocolCheck S Op input limits :=
  if hstates : input.states.values.length ≤ limits.maxStates then
    if hops : input.operations.values.length ≤ limits.maxOperations then
      match hclosed : input.closedB with
      | true => .accepted { toProtocolInput := input, closed := hclosed } rfl
      | false => .notClosed hclosed
    else
      .tooLarge .operations input.operations.values.length limits.maxOperations
  else
    .tooLarge .states input.states.values.length limits.maxStates

namespace ProtocolCheck

def isAccepted {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] {input : ProtocolInput S Op} {limits : Limits} :
    ProtocolCheck S Op input limits → Bool
  | .accepted .. => true
  | .tooLarge .. => false
  | .notClosed _ => false

def refusalAxis? {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] {input : ProtocolInput S Op} {limits : Limits} :
    ProtocolCheck S Op input limits → Option LimitAxis
  | .accepted .. => none
  | .tooLarge axis .. => some axis
  | .notClosed _ => none

end ProtocolCheck

def ProtocolScope.runModel {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S]
    (scope : ProtocolScope S Op) : LiveSegmented.RunModel S Op S where
  step := scope.step
  observe := id

def ProtocolScope.reachableB {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S]
    (scope : ProtocolScope S Op) (x y : S) : Bool :=
  scope.reachableStates x |>.contains y

theorem ProtocolScope.exec_mem_reachableStates {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (base current : S) (hcurrent : current ∈ scope.reachableStates base) :
    ∀ operations : List Op,
      scope.runModel.exec current operations ∈ scope.reachableStates base
  | [] => hcurrent
  | operation :: operations =>
      scope.exec_mem_reachableStates base (scope.step current operation)
        (scope.toProtocolInput.closedB_spec scope.closed
          base current hcurrent operation) operations

theorem ProtocolScope.reachableB_iff {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op) (x y : S) :
    scope.reachableB x y = true ↔
      LiveSegmented.Reachable scope.runModel x y :=
  by
    constructor
    · intro h
      exact scope.toProtocolInput.mem_reachableStates_sound x y
        (List.contains_iff_mem.mp h)
    · rintro ⟨operations, rfl⟩
      have hstart : x ∈ scope.reachableStates x :=
        scope.toProtocolInput.mem_layers_mono
          scope.states.values.length [x] x (by simp)
      exact List.contains_iff_mem.mpr
        (scope.exec_mem_reachableStates x x hstart operations)

def ProtocolScope.coReachableB {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S]
    (scope : ProtocolScope S Op) (base x y : S) : Bool :=
  scope.reachableB base x && scope.reachableB base y

theorem ProtocolScope.coReachableB_iff {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (base x y : S) :
    scope.coReachableB base x y = true ↔
      LiveSegmented.CoReachable scope.runModel base x y := by
  simp [ProtocolScope.coReachableB, ProtocolScope.reachableB_iff,
    LiveSegmented.CoReachable]

/-! ## Cap-before-enumeration minimum seam synthesis -/

def coloringCount {S : Type u} {Seg : Type v}
    (states : Carrier S) (palette : List Seg) : Nat :=
  palette.length ^ states.values.length

/-- The existing exhaustive seam synthesizer behind a resource-first boundary.
Neither `allColorings` nor the semantic search is referenced in a refusal
branch. -/
def synthesizeMinimumSeamCapped {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (states : Carrier S) (palette : List Seg) (fallback : Seg)
    (limits : Limits) :
    Capped (SeamColoring.MinimumSynthesis I states.values palette) :=
  if hstates : states.values.length ≤ limits.maxStates then
    if hcolorings : coloringCount states palette ≤ limits.maxColorings then
      .ready (SeamColoring.synthesizeMinimumSeam I states.values
        states.complete palette fallback)
    else
      .tooLarge .colorings (coloringCount states palette)
        limits.maxColorings
  else
    .tooLarge .states states.values.length limits.maxStates

/-! ### Generic exact strategy search, instantiated globally, live, and by a
finite fork scenario below. -/

def validStrategies {S : Type u} {Seg : Type v} [DecidableEq S]
    [DecidableEq Seg] (states : Carrier S) (palette : List Seg)
    (fallback : Seg) (Good : (S → Seg) → Prop)
    (decideGood : ∀ strategy, Decidable (Good strategy)) :
    List (S → Seg) :=
  (SeamColoring.allColorings palette fallback states.values).filter
    fun strategy => @decide (Good strategy) (decideGood strategy)

/-- The small executable observation used by fixtures.  The proof-carrying
`synthesizeStrategy` below uses the same candidates and objective. -/
def minimumStrategyUsedColors? {S : Type u} {Seg : Type v}
    [DecidableEq S] [DecidableEq Seg] (states : Carrier S)
    (palette : List Seg) (fallback : Seg) (Good : (S → Seg) → Prop)
    (decideGood : ∀ strategy, Decidable (Good strategy)) : Option Nat :=
  (SeamColoring.argMin?
    (SeamColoring.usedColorCount states.values palette)
    (validStrategies states palette fallback Good decideGood)).map
      (SeamColoring.usedColorCount states.values palette)

structure MinimumStrategy {S : Type u} {Seg : Type v} [DecidableEq Seg]
    (states : Carrier S) (palette : List Seg)
    (Good : (S → Seg) → Prop) where
  strategy : S → Seg
  usesOnly : SeamColoring.UsesOnly states.values palette strategy
  good : Good strategy
  least : ∀ other : S → Seg,
    SeamColoring.UsesOnly states.values palette other → Good other →
      SeamColoring.usedColorCount states.values palette strategy ≤
        SeamColoring.usedColorCount states.values palette other

inductive StrategyResult {S : Type u} {Seg : Type v} [DecidableEq Seg]
    (states : Carrier S) (palette : List Seg)
    (Good : (S → Seg) → Prop) where
  | found (minimum : MinimumStrategy states palette Good)
  | refused (exhaustive : ∀ strategy : S → Seg,
      SeamColoring.UsesOnly states.values palette strategy → ¬ Good strategy)

def synthesizeStrategy {S : Type u} {Seg : Type v} [DecidableEq S]
    [DecidableEq Seg] (states : Carrier S) (palette : List Seg)
    (fallback : Seg) (Good : (S → Seg) → Prop)
    (decideGood : ∀ strategy, Decidable (Good strategy)) :
    StrategyResult states palette Good :=
  let candidates := validStrategies states palette fallback Good decideGood
  match h : SeamColoring.argMin?
      (SeamColoring.usedColorCount states.values palette) candidates with
  | none =>
      .refused (by
        have hempty : candidates = [] :=
          (SeamColoring.argMin_eq_none_iff
            (SeamColoring.usedColorCount states.values palette)
            candidates).mp h
        intro strategy huses hgood
        have hall := SeamColoring.allColorings_complete palette fallback
          states.complete strategy huses
        have hmem : strategy ∈ candidates := by
          apply List.mem_filter.mpr
          exact ⟨hall, @decide_eq_true (Good strategy)
            (decideGood strategy) hgood⟩
        rw [hempty] at hmem
        exact List.not_mem_nil hmem)
  | some strategy =>
      have hmem : strategy ∈ candidates :=
        SeamColoring.argMin_mem _ h
      have hparts := List.mem_filter.mp hmem
      .found {
        strategy := strategy
        usesOnly := SeamColoring.allColorings_usesOnly palette fallback
          states.values hparts.1
        good := @of_decide_eq_true (Good strategy)
          (decideGood strategy) hparts.2
        least := by
          intro other huses hgood
          apply SeamColoring.argMin_le_of_mem _ h
          apply List.mem_filter.mpr
          exact ⟨SeamColoring.allColorings_complete palette fallback
              states.complete other huses,
            @decide_eq_true (Good other) (decideGood other) hgood⟩
      }

def synthesizeStrategyCapped {S : Type u} {Seg : Type v} [DecidableEq S]
    [DecidableEq Seg] (states : Carrier S) (palette : List Seg)
    (fallback : Seg) (Good : (S → Seg) → Prop)
    (decideGood : ∀ strategy, Decidable (Good strategy))
    (limits : Limits) : Capped (StrategyResult states palette Good) :=
  if hstates : states.values.length ≤ limits.maxStates then
    if hcolorings : coloringCount states palette ≤ limits.maxColorings then
      .ready (synthesizeStrategy states palette fallback Good decideGood)
    else
      .tooLarge .colorings (coloringCount states palette)
        limits.maxColorings
  else
    .tooLarge .states states.values.length limits.maxStates

namespace StrategyResult

def isFound {S : Type u} {Seg : Type v} [DecidableEq Seg]
    {states : Carrier S} {palette : List Seg}
    {Good : (S → Seg) → Prop} : StrategyResult states palette Good → Bool
  | .found _ => true
  | .refused _ => false

def minimumUsedColors? {S : Type u} {Seg : Type v} [DecidableEq Seg]
    {states : Carrier S} {palette : List Seg}
    {Good : (S → Seg) → Prop} : StrategyResult states palette Good → Option Nat
  | .found minimum => some
      (SeamColoring.usedColorCount states.values palette minimum.strategy)
  | .refused _ => none

end StrategyResult

theorem finiteGlobalValid_iff {S : Type u} {Seg : Type v}
    [MergeState S] (states : Carrier S) (strategy : S → Seg)
    (I : Invariant S) :
    SeamColoring.FiniteValid states.values strategy I ↔
      Segmented.SegmentedIConfluent strategy I := by
  constructor
  · intro h
    exact SeamColoring.segmented_of_segmentedOn states.complete
      (SeamColoring.segmentedOn_iff_properColoring.mpr h)
  · intro h
    exact SeamColoring.segmentedOn_iff_properColoring.mp
      (SeamColoring.segmentedOn_of_segmented h states.values)

def decideGlobalSegmented {S : Type u} {Seg : Type v}
    [MergeState S] [DecidableEq Seg] (states : Carrier S)
    (strategy : S → Seg) (I : Invariant S) [DecidablePred I] :
    Decidable (Segmented.SegmentedIConfluent strategy I) :=
  decidable_of_iff (SeamColoring.FiniteValid states.values strategy I)
    (finiteGlobalValid_iff states strategy I)

def synthesizeMinimumGlobalSeamCapped {S : Type u} {Seg : Type v}
    [MergeState S] [DecidableEq S] [DecidableEq Seg]
    (states : Carrier S) (I : Invariant S) [DecidablePred I]
    (palette : List Seg) (fallback : Seg) (limits : Limits) :
    Capped (StrategyResult states palette
      (fun strategy => Segmented.SegmentedIConfluent strategy I)) :=
  synthesizeStrategyCapped states palette fallback
    (fun strategy => Segmented.SegmentedIConfluent strategy I)
    (fun strategy => decideGlobalSegmented states strategy I) limits

def FiniteLiveSegmented {S : Type u} {Op : Type v} {Seg : Type w}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (strategy : S → Seg) (I : Invariant S) : Prop :=
  ∀ base ∈ scope.states.values, ∀ left ∈ scope.states.values,
    ∀ right ∈ scope.states.values,
      scope.coReachableB base left right = true →
      strategy left = strategy right → I left → I right →
      I (left ⊔ right) ∧ strategy (left ⊔ right) = strategy left

theorem finiteLiveSegmented_iff {S : Type u} {Op : Type v} {Seg : Type w}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (strategy : S → Seg) (I : Invariant S) :
    FiniteLiveSegmented scope strategy I ↔
      LiveSegmented.LiveSegmented scope.runModel strategy I := by
  constructor
  · intro h base left right hco heq hleft hright
    exact h base (scope.states.complete base)
      left (scope.states.complete left) right (scope.states.complete right)
      ((scope.coReachableB_iff base left right).mpr hco)
      heq hleft hright
  · intro h base _ left _ right _ hco heq hleft hright
    exact h base left right
      ((scope.coReachableB_iff base left right).mp hco)
      heq hleft hright

def decideLiveSegmented {S : Type u} {Op : Type v} {Seg : Type w}
    [MergeState S] [DecidableEq S] [DecidableEq Seg]
    (scope : ProtocolScope S Op) (strategy : S → Seg)
    (I : Invariant S) [DecidablePred I] :
    Decidable (LiveSegmented.LiveSegmented scope.runModel strategy I) :=
  let finiteDecision : Decidable (FiniteLiveSegmented scope strategy I) :=
    decideForallMem scope.states.values (fun base =>
      ∀ left ∈ scope.states.values, ∀ right ∈ scope.states.values,
        scope.coReachableB base left right = true →
        strategy left = strategy right → I left → I right →
        I (left ⊔ right) ∧ strategy (left ⊔ right) = strategy left)
      (fun base =>
        decideForallMem scope.states.values (fun left =>
          ∀ right ∈ scope.states.values,
            scope.coReachableB base left right = true →
            strategy left = strategy right → I left → I right →
            I (left ⊔ right) ∧ strategy (left ⊔ right) = strategy left)
          (fun left =>
            decideForallMem scope.states.values (fun right =>
              scope.coReachableB base left right = true →
              strategy left = strategy right → I left → I right →
              I (left ⊔ right) ∧
                strategy (left ⊔ right) = strategy left)
              (fun _ => inferInstance)))
  letI : Decidable (FiniteLiveSegmented scope strategy I) := finiteDecision
  decidable_of_iff (FiniteLiveSegmented scope strategy I)
    (finiteLiveSegmented_iff scope strategy I)

def synthesizeMinimumLiveSeamCapped {S : Type u} {Op : Type v}
    {Seg : Type w} [MergeState S] [DecidableEq S] [DecidableEq Seg]
    (scope : ProtocolScope S Op) (I : Invariant S) [DecidablePred I]
    (palette : List Seg) (fallback : Seg) (limits : Limits) :
    Capped (StrategyResult scope.states palette
      (fun strategy =>
        LiveSegmented.LiveSegmented scope.runModel strategy I)) :=
  synthesizeStrategyCapped scope.states palette fallback
    (fun strategy => LiveSegmented.LiveSegmented scope.runModel strategy I)
    (fun strategy => decideLiveSegmented scope strategy I) limits

def synthesizeMinimumScenarioSeamCapped {S : Type u} {Op : Type v}
    {Seg : Type w} [MergeState S] [DecidableEq S] [DecidableEq Seg]
    (states : Carrier S) (I : Invariant S) [DecidablePred I]
    (step : S → Op → S) (scenario : ForkGrade.Scenario S Op)
    (palette : List Seg) (fallback : Seg) (limits : Limits) :
    Capped (StrategyResult states palette
      (fun strategy => SeamColoring.FiniteValid
        (scenario.worlds step) strategy I)) :=
  synthesizeStrategyCapped states palette fallback
    (fun strategy => SeamColoring.FiniteValid
      (scenario.worlds step) strategy I)
    (fun strategy => inferInstance) limits

/- `minimum` above means minimum `usedColorCount` on the complete declared
`states` carrier among strategies valid on the scenario worlds.  It does not
mean minimum `ForkGrade.liveCost`, whose objective depends on branch crossings
rather than only on colouring width. -/

/-! ## Exact maximum clique over a finite carrier -/

def FiniteClique {α : Type u} (R : α → α → Prop) (vertices : List α) : Prop :=
  vertices.Pairwise R

def pairwiseB {α : Type u} (R : α → α → Bool) : List α → Bool
  | [] => true
  | head :: tail => tail.all (R head) && pairwiseB R tail

theorem pairwiseB_eq_true_iff {α : Type u} (R : α → α → Bool) :
    ∀ vertices : List α,
      pairwiseB R vertices = true ↔
        FiniteClique (fun left right => R left right = true) vertices
  | [] => by simp [pairwiseB, FiniteClique]
  | head :: tail => by
      rw [pairwiseB, Bool.and_eq_true, pairwiseB_eq_true_iff]
      simp only [FiniteClique, List.pairwise_cons]
      constructor
      · rintro ⟨hall, htail⟩
        exact ⟨fun value hmem => List.all_eq_true.mp hall value hmem,
          htail⟩
      · rintro ⟨hhead, htail⟩
        exact ⟨List.all_eq_true.mpr hhead, htail⟩

/-- Every order-preserving subset, with the same exact representation used by
the clique theorem below. -/
def subsets {α : Type u} : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      subsets tail ++ (subsets tail).map (head :: ·)

@[simp] theorem mem_subsets_iff_sublist {α : Type u}
    {source choice : List α} :
    choice ∈ subsets source ↔ choice.Sublist source := by
  induction source generalizing choice with
  | nil => simp [subsets]
  | cons head tail ih =>
      rw [subsets, List.mem_append]
      constructor
      · intro h
        rcases h with hskip | htake
        · exact List.Sublist.cons head (ih.mp hskip)
        · obtain ⟨prior, hprior, rfl⟩ := List.mem_map.mp htake
          exact List.Sublist.cons_cons head (ih.mp hprior)
      · intro h
        cases h with
        | cons _ hsub => exact Or.inl (ih.mpr hsub)
        | cons_cons _ hsub =>
            exact Or.inr (List.mem_map.mpr ⟨_, ih.mpr hsub, rfl⟩)

@[simp] theorem subsets_length {α : Type u} (source : List α) :
    (subsets source).length = 2 ^ source.length := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
      simp [subsets, ih, Nat.pow_succ]
      omega

theorem sublist_length_le {α : Type u} {left right : List α}
    (h : left.Sublist right) : left.length ≤ right.length := by
  induction h with
  | slnil => simp
  | cons _ hsub ih => simp; omega
  | cons_cons _ hsub ih => simp; omega

/-- Put an arbitrary duplicate-free supported list into carrier order. -/
def canonicalize {α : Type u} [DecidableEq α]
    (pool values : List α) : List α :=
  pool.filter fun value => values.contains value

theorem perm_canonicalize {α : Type u} [DecidableEq α]
    {pool values : List α} (hpool : pool.Nodup) (hvalues : values.Nodup)
    (hsupported : ∀ value ∈ values, value ∈ pool) :
    values.Perm (canonicalize pool values) := by
  rw [List.perm_iff_count]
  intro value
  by_cases hmem : value ∈ values
  · rw [hvalues.count]
    simp [canonicalize, hmem, hsupported value hmem, hpool.count]
  · rw [hvalues.count]
    have hnot : value ∉ canonicalize pool values := by
      simp [canonicalize, hmem]
    rw [if_neg hmem, List.count_eq_zero.mpr hnot]

theorem canonicalize_sublist {α : Type u} [DecidableEq α]
    (pool values : List α) :
    canonicalize pool values |>.Sublist pool := by
  exact List.filter_sublist

def cliqueCandidates {α : Type u} (carrier : Carrier α)
    (R : α → α → Bool) : List (List α) :=
  subsets carrier.values |>.filter (pairwiseB R)

/-- A maximum clique in canonical carrier order.  Arbitrarily permuted clique
lists can be canonicalised first; the exact theorem below ranges over every
sublist, which is the representation searched by the algorithm. -/
structure MaximumClique {α : Type u} (carrier : Carrier α)
    (R : α → α → Bool) where
  vertices : List α
  supported : vertices.Sublist carrier.values
  clique : FiniteClique (fun left right => R left right = true) vertices
  greatest : ∀ other : List α, other.Sublist carrier.values →
    FiniteClique (fun left right => R left right = true) other →
      other.length ≤ vertices.length

/-- `MaximumClique.greatest` is stated for the canonical carrier-order
representation searched by the algorithm.  Symmetry lets any duplicate-free
supported clique be canonicalised without changing length or cliquehood. -/
theorem MaximumClique.greatestSupported {α : Type u} [DecidableEq α]
    {carrier : Carrier α} {R : α → α → Bool}
    (maximum : MaximumClique carrier R)
    (hsymmetric : ∀ {left right}, R left right = true → R right left = true)
    (other : List α) (hnodup : other.Nodup)
    (hsupported : ∀ value ∈ other, value ∈ carrier.values)
    (hclique : FiniteClique (fun left right => R left right = true) other) :
    other.length ≤ maximum.vertices.length := by
  let ordered := canonicalize carrier.values other
  have hperm : other.Perm ordered :=
    perm_canonicalize carrier.nodup hnodup hsupported
  have hordered : FiniteClique
      (fun left right => R left right = true) ordered :=
    hclique.perm hperm hsymmetric
  have hle := maximum.greatest ordered
    (canonicalize_sublist carrier.values other) hordered
  rw [hperm.length_eq]
  exact hle

def minimumCliqueComplement? {α : Type u} (carrier : Carrier α)
    (R : α → α → Bool) : Option (List α) :=
  SeamColoring.argMin?
    (fun vertices => carrier.values.length - vertices.length)
    (cliqueCandidates carrier R)

theorem mem_cliqueCandidates_iff {α : Type u} (carrier : Carrier α)
    (R : α → α → Bool) (vertices : List α) :
    vertices ∈ cliqueCandidates carrier R ↔
      vertices.Sublist carrier.values ∧
        FiniteClique (fun left right => R left right = true) vertices := by
  simp [cliqueCandidates, pairwiseB_eq_true_iff]

/-- The result is total and the refusal branch is exhaustive for every
canonical subset of the declared carrier. -/
inductive CliqueResult {α : Type u} (carrier : Carrier α)
    (R : α → α → Bool) where
  | found (maximum : MaximumClique carrier R)
  | refused (exhaustive : ∀ vertices : List α, vertices.Sublist carrier.values →
      ¬ FiniteClique (fun left right => R left right = true) vertices)

def synthesizeMaximumClique {α : Type u} (carrier : Carrier α)
    (R : α → α → Bool) : CliqueResult carrier R :=
  match h : minimumCliqueComplement? carrier R with
  | none =>
      .refused (by
        unfold minimumCliqueComplement? at h
        have hempty : cliqueCandidates carrier R = [] :=
          (SeamColoring.argMin_eq_none_iff
            (fun vertices => carrier.values.length - vertices.length)
            (cliqueCandidates carrier R)).mp h
        intro vertices hsupported hclique
        have hmem : vertices ∈ cliqueCandidates carrier R :=
          (mem_cliqueCandidates_iff carrier R vertices).mpr
            ⟨hsupported, hclique⟩
        rw [hempty] at hmem
        exact List.not_mem_nil hmem)
  | some vertices => by
      unfold minimumCliqueComplement? at h
      exact .found {
        vertices := vertices
        supported :=
          (mem_cliqueCandidates_iff carrier R vertices).mp
            (SeamColoring.argMin_mem _ h) |>.1
        clique :=
          (mem_cliqueCandidates_iff carrier R vertices).mp
            (SeamColoring.argMin_mem _ h) |>.2
        greatest := by
          intro other hsub hclique
          have hmem : other ∈ cliqueCandidates carrier R :=
            (mem_cliqueCandidates_iff carrier R other).mpr ⟨hsub, hclique⟩
          have hleast := SeamColoring.argMin_le_of_mem _ h hmem
          have hvertices : vertices.length ≤ carrier.values.length :=
            sublist_length_le
              ((mem_cliqueCandidates_iff carrier R vertices).mp
                (SeamColoring.argMin_mem _ h)).1
          have hother : other.length ≤ carrier.values.length :=
            sublist_length_le hsub
          omega
      }

/-- Check the carrier and `2^N` subset bound before evaluating the clique
enumerator. -/
def synthesizeMaximumCliqueCapped {α : Type u} (carrier : Carrier α)
    (R : α → α → Bool) (limits : Limits) :
    Capped (CliqueResult carrier R) :=
  if hstates : carrier.values.length ≤ limits.maxStates then
    if hsubsets : 2 ^ carrier.values.length ≤ limits.maxSubsets then
      .ready (synthesizeMaximumClique carrier R)
    else
      .tooLarge .subsets (2 ^ carrier.values.length) limits.maxSubsets
  else
    .tooLarge .states carrier.values.length limits.maxStates

namespace CliqueResult

def maximumSize? {α : Type u} {carrier : Carrier α}
    {R : α → α → Bool} : CliqueResult carrier R → Option Nat
  | .found maximum => some maximum.vertices.length
  | .refused _ => none

end CliqueResult

/-! ### Maximum clique over an explicit finite pool

Unlike `Carrier`, a scenario pool need not cover its ambient type.  This
variant makes that narrower scope explicit while retaining exact found/refused
proofs for every canonical subset of the pool. -/

def poolCliqueCandidates {α : Type u} (pool : List α)
    (R : α → α → Bool) : List (List α) :=
  subsets pool |>.filter (pairwiseB R)

theorem mem_poolCliqueCandidates_iff {α : Type u} (pool : List α)
    (R : α → α → Bool) (vertices : List α) :
    vertices ∈ poolCliqueCandidates pool R ↔
      vertices.Sublist pool ∧
        FiniteClique (fun left right => R left right = true) vertices := by
  simp [poolCliqueCandidates, pairwiseB_eq_true_iff]

structure MaximumPoolClique {α : Type u} (pool : List α)
    (R : α → α → Bool) where
  vertices : List α
  supported : vertices.Sublist pool
  clique : FiniteClique (fun left right => R left right = true) vertices
  greatest : ∀ other : List α, other.Sublist pool →
    FiniteClique (fun left right => R left right = true) other →
      other.length ≤ vertices.length

theorem MaximumPoolClique.greatestSupported {α : Type u} [DecidableEq α]
    {pool : List α} {R : α → α → Bool}
    (maximum : MaximumPoolClique pool R) (hpool : pool.Nodup)
    (hsymmetric : ∀ {left right}, R left right = true → R right left = true)
    (other : List α) (hnodup : other.Nodup)
    (hsupported : ∀ value ∈ other, value ∈ pool)
    (hclique : FiniteClique (fun left right => R left right = true) other) :
    other.length ≤ maximum.vertices.length := by
  let ordered := canonicalize pool other
  have hperm : other.Perm ordered :=
    perm_canonicalize hpool hnodup hsupported
  have hordered : FiniteClique
      (fun left right => R left right = true) ordered :=
    hclique.perm hperm hsymmetric
  have hle := maximum.greatest ordered
    (canonicalize_sublist pool other) hordered
  rw [hperm.length_eq]
  exact hle

inductive PoolCliqueResult {α : Type u} (pool : List α)
    (R : α → α → Bool) where
  | found (maximum : MaximumPoolClique pool R)
  | refused (exhaustive : ∀ vertices : List α, vertices.Sublist pool →
      ¬ FiniteClique (fun left right => R left right = true) vertices)

def synthesizeMaximumPoolClique {α : Type u} (pool : List α)
    (R : α → α → Bool) : PoolCliqueResult pool R :=
  let candidates := poolCliqueCandidates pool R
  match h : SeamColoring.argMin?
      (fun vertices => pool.length - vertices.length) candidates with
  | none =>
      .refused (by
        have hempty : candidates = [] :=
          (SeamColoring.argMin_eq_none_iff
            (fun vertices => pool.length - vertices.length) candidates).mp h
        intro vertices hsupported hclique
        have hmem : vertices ∈ candidates :=
          (mem_poolCliqueCandidates_iff pool R vertices).mpr
            ⟨hsupported, hclique⟩
        rw [hempty] at hmem
        exact List.not_mem_nil hmem)
  | some vertices =>
      have hmem : vertices ∈ candidates := SeamColoring.argMin_mem _ h
      have hparts := (mem_poolCliqueCandidates_iff pool R vertices).mp hmem
      .found {
        vertices := vertices
        supported := hparts.1
        clique := hparts.2
        greatest := by
          intro other hsub hclique
          have hother : other ∈ candidates :=
            (mem_poolCliqueCandidates_iff pool R other).mpr
              ⟨hsub, hclique⟩
          have hleast := SeamColoring.argMin_le_of_mem _ h hother
          have hvlen := sublist_length_le hparts.1
          have holen := sublist_length_le hsub
          omega
      }

namespace PoolCliqueResult

def maximumSize? {α : Type u} {pool : List α} {R : α → α → Bool} :
    PoolCliqueResult pool R → Option Nat
  | .found maximum => some maximum.vertices.length
  | .refused _ => none

end PoolCliqueResult

/-! ### Exact live cliques without the `2^(N²)` product trap

A live clique has one common base.  Enumerating `(base, world)` as an ordinary
vertex would subsequently enumerate every subset of all `N²` pairs, most of
which mix bases and can never be live cliques.  The search below instead
enumerates `N` bases and `2^N` world subsets for each base. -/

def liveWorldClashB {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] (scope : ProtocolScope S Op) (I : Invariant S)
    [DecidablePred I] (base left right : S) : Bool :=
  scope.coReachableB base left right &&
    decide (SeamColoring.Clashes I left right)

theorem liveWorldClashB_eq_true_iff {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (I : Invariant S) [DecidablePred I] (base left right : S) :
    liveWorldClashB scope I base left right = true ↔
      LiveSegmented.LiveClashes scope.runModel I base left right := by
  simp [liveWorldClashB, LiveSegmented.LiveClashes,
    ProtocolScope.runModel, scope.coReachableB_iff]

def liveCliqueCandidates {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] (scope : ProtocolScope S Op) (I : Invariant S)
    [DecidablePred I] : List (S × List S) :=
  scope.states.values.flatMap fun base =>
    (subsets scope.states.values |>.filter
      (pairwiseB (liveWorldClashB scope I base))).map fun worlds =>
        (base, worlds)

theorem pairwise_liveWorldClashB_iff {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (I : Invariant S) [DecidablePred I] (base : S) (worlds : List S) :
    pairwiseB (liveWorldClashB scope I base) worlds = true ↔
      CliqueLive.LiveClique scope.runModel I base worlds := by
  rw [pairwiseB_eq_true_iff]
  constructor
  · intro h
    exact h.imp (fun hpair =>
      (liveWorldClashB_eq_true_iff scope I base _ _).mp hpair)
  · intro h
    exact h.imp (fun hpair =>
      (liveWorldClashB_eq_true_iff scope I base _ _).mpr hpair)

theorem mem_liveCliqueCandidates_iff {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (I : Invariant S) [DecidablePred I] (entry : S × List S) :
    entry ∈ liveCliqueCandidates scope I ↔
      entry.1 ∈ scope.states.values ∧
      entry.2.Sublist scope.states.values ∧
      CliqueLive.LiveClique scope.runModel I entry.1 entry.2 := by
  rcases entry with ⟨base, worlds⟩
  simp only [liveCliqueCandidates, List.mem_flatMap, List.mem_map,
    List.mem_filter, mem_subsets_iff_sublist, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨base', hbase, worlds', ⟨hsub, hclique⟩, heq⟩
    cases heq
    exact ⟨hbase, hsub,
      (pairwise_liveWorldClashB_iff scope I base worlds).mp hclique⟩
  · rintro ⟨hbase, hsub, hclique⟩
    exact ⟨base, hbase, worlds, ⟨hsub,
      (pairwise_liveWorldClashB_iff scope I base worlds).mpr hclique⟩, rfl⟩

structure MaximumLiveClique {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] (scope : ProtocolScope S Op) (I : Invariant S)
    [DecidablePred I] where
  base : S
  worlds : List S
  baseSupported : base ∈ scope.states.values
  worldsSupported : worlds.Sublist scope.states.values
  clique : CliqueLive.LiveClique scope.runModel I base worlds
  greatest : ∀ otherBase : S, otherBase ∈ scope.states.values →
    ∀ otherWorlds : List S, otherWorlds.Sublist scope.states.values →
      CliqueLive.LiveClique scope.runModel I otherBase otherWorlds →
        otherWorlds.length ≤ worlds.length

theorem MaximumLiveClique.greatestSupported {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] {scope : ProtocolScope S Op}
    {I : Invariant S} [DecidablePred I]
    (maximum : MaximumLiveClique scope I)
    (otherBase : S) (hbase : otherBase ∈ scope.states.values)
    (otherWorlds : List S) (hnodup : otherWorlds.Nodup)
    (hsupported : ∀ value ∈ otherWorlds,
      value ∈ scope.states.values)
    (hclique : CliqueLive.LiveClique scope.runModel I
      otherBase otherWorlds) :
    otherWorlds.length ≤ maximum.worlds.length := by
  let ordered := canonicalize scope.states.values otherWorlds
  have hperm : otherWorlds.Perm ordered :=
    perm_canonicalize scope.states.nodup hnodup hsupported
  have hsymmetric : ∀ {left right},
      LiveSegmented.LiveClashes scope.runModel I otherBase left right →
      LiveSegmented.LiveClashes scope.runModel I otherBase right left := by
    rintro left right ⟨⟨hleft, hright⟩, hIleft, hIright, hbad⟩
    exact ⟨⟨hright, hleft⟩, hIright, hIleft, by
      simpa [MergeState.merge_comm] using hbad⟩
  have hordered : CliqueLive.LiveClique scope.runModel I
      otherBase ordered := hclique.perm hperm hsymmetric
  have hle := maximum.greatest otherBase hbase ordered
    (canonicalize_sublist scope.states.values otherWorlds) hordered
  rw [hperm.length_eq]
  exact hle

inductive LiveCliqueResult {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] (scope : ProtocolScope S Op) (I : Invariant S)
    [DecidablePred I] where
  | found (maximum : MaximumLiveClique scope I)
  | refused (exhaustive : ∀ base : S, base ∈ scope.states.values →
      ∀ worlds : List S, worlds.Sublist scope.states.values →
        ¬ CliqueLive.LiveClique scope.runModel I base worlds)

def synthesizeMaximumLiveClique {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (I : Invariant S) [DecidablePred I] : LiveCliqueResult scope I :=
  let candidates := liveCliqueCandidates scope I
  match h : SeamColoring.argMin?
      (fun entry => scope.states.values.length - entry.2.length)
      candidates with
  | none =>
      .refused (by
        have hempty : candidates = [] :=
          (SeamColoring.argMin_eq_none_iff
            (fun entry => scope.states.values.length - entry.2.length)
            candidates).mp h
        intro base hbase worlds hsub hclique
        have hmem : (base, worlds) ∈ candidates :=
          (mem_liveCliqueCandidates_iff scope I (base, worlds)).mpr
            ⟨hbase, hsub, hclique⟩
        rw [hempty] at hmem
        exact List.not_mem_nil hmem)
  | some entry =>
      have hmem : entry ∈ candidates := SeamColoring.argMin_mem _ h
      have hparts := (mem_liveCliqueCandidates_iff scope I entry).mp hmem
      .found {
        base := entry.1
        worlds := entry.2
        baseSupported := hparts.1
        worldsSupported := hparts.2.1
        clique := hparts.2.2
        greatest := by
          intro otherBase hbase otherWorlds hsub hclique
          have hother : (otherBase, otherWorlds) ∈ candidates :=
            (mem_liveCliqueCandidates_iff scope I
              (otherBase, otherWorlds)).mpr ⟨hbase, hsub, hclique⟩
          have hleast := SeamColoring.argMin_le_of_mem _ h hother
          change scope.states.values.length - entry.2.length ≤
            scope.states.values.length - otherWorlds.length at hleast
          have hentryLen : entry.2.length ≤ scope.states.values.length :=
            sublist_length_le hparts.2.1
          have hotherLen : otherWorlds.length ≤ scope.states.values.length :=
            sublist_length_le hsub
          omega
      }

def maximumLiveCliqueSize? {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (I : Invariant S) [DecidablePred I] : Option Nat :=
  (SeamColoring.argMin?
    (fun entry => scope.states.values.length - entry.2.length)
    (liveCliqueCandidates scope I)).map fun entry => entry.2.length

def maximumPoolCliqueSize? {S : Type u} (pool : List S)
    (R : S → S → Bool) : Option Nat :=
  (SeamColoring.argMin?
    (fun vertices => pool.length - vertices.length)
    (poolCliqueCandidates pool R)).map List.length

namespace LiveCliqueResult

def maximumSize? {S : Type u} {Op : Type v} [MergeState S]
    [DecidableEq S] {scope : ProtocolScope S Op} {I : Invariant S}
    [DecidablePred I] : LiveCliqueResult scope I → Option Nat
  | .found maximum => some maximum.worlds.length
  | .refused _ => none

end LiveCliqueResult

/-- Check `N * 2^N`, the actual number of pre-filter live candidates, before
materialising any subset list. -/
def synthesizeMaximumLiveCliqueCapped {S : Type u} {Op : Type v}
    [MergeState S] [DecidableEq S] (scope : ProtocolScope S Op)
    (I : Invariant S) [DecidablePred I] (limits : Limits) :
    Capped (LiveCliqueResult scope I) :=
  let count := scope.states.values.length * 2 ^ scope.states.values.length
  if hstates : scope.states.values.length ≤ limits.maxStates then
    if hsubsets : count ≤ limits.maxSubsets then
      .ready (synthesizeMaximumLiveClique scope I)
    else
      .tooLarge .subsets count limits.maxSubsets
  else
    .tooLarge .states scope.states.values.length limits.maxStates

def scenarioClashB {S : Type u} {Op : Type v} [MergeState S]
    (I : Invariant S) [DecidablePred I] (step : S → Op → S)
    (scenario : ForkGrade.Scenario S Op) (left right : List Op) : Bool :=
  decide (SeamColoring.Clashes I
    (Cost.run step scenario.root left)
    (Cost.run step scenario.root right))

def synthesizeMaximumScenarioCliqueCapped {S : Type u} {Op : Type v}
    [MergeState S] (I : Invariant S) [DecidablePred I]
    (step : S → Op → S) (scenario : ForkGrade.Scenario S Op)
    (_pathsNodup : scenario.paths.Nodup) (limits : Limits) :
    Capped (PoolCliqueResult scenario.paths
      (scenarioClashB I step scenario)) :=
  if hsubsets : 2 ^ scenario.paths.length ≤ limits.maxSubsets then
    .ready (synthesizeMaximumPoolClique scenario.paths
      (scenarioClashB I step scenario))
  else
    .tooLarge .subsets (2 ^ scenario.paths.length) limits.maxSubsets

/-! ## Exact finite Cartesian-product search -/

/-- One exact finite axis.  Its values need not enumerate an ambient type;
`Admissible` states the explicit grammar which the list exhausts. -/
structure Axis (α : Type u) where
  values : List α
  Admissible : α → Prop
  sound : ∀ value, value ∈ values → Admissible value
  complete : ∀ value, Admissible value → value ∈ values

structure ProductProblem (α : Type u) (β : Type v) where
  left : Axis α
  right : Axis β
  compatible : α → β → Prop
  decideCompatible : ∀ left right, Decidable (compatible left right)
  score : α × β → Nat

def ProductProblem.candidates {α : Type u} {β : Type v}
    (problem : ProductProblem α β) : List (α × β) :=
  problem.left.values.flatMap fun left =>
    problem.right.values.map fun right => (left, right)

def ProductProblem.feasible {α : Type u} {β : Type v}
    (problem : ProductProblem α β) : List (α × β) :=
  problem.candidates.filter fun pair =>
    @decide (problem.compatible pair.1 pair.2)
      (problem.decideCompatible pair.1 pair.2)

theorem ProductProblem.mem_candidates_iff {α : Type u} {β : Type v}
    (problem : ProductProblem α β) (pair : α × β) :
    pair ∈ problem.candidates ↔
      pair.1 ∈ problem.left.values ∧ pair.2 ∈ problem.right.values := by
  rcases pair with ⟨left, right⟩
  simp [ProductProblem.candidates]

theorem ProductProblem.mem_feasible_iff {α : Type u} {β : Type v}
    (problem : ProductProblem α β) (pair : α × β) :
    pair ∈ problem.feasible ↔
      problem.left.Admissible pair.1 ∧
      problem.right.Admissible pair.2 ∧
      problem.compatible pair.1 pair.2 := by
  rw [ProductProblem.feasible, List.mem_filter]
  constructor
  · rintro ⟨hcandidate, hcompatibleB⟩
    have hcandidate' := (problem.mem_candidates_iff pair).mp hcandidate
    have hleft := hcandidate'.1
    have hright := hcandidate'.2
    have hcompatible : problem.compatible pair.1 pair.2 :=
      @of_decide_eq_true (problem.compatible pair.1 pair.2)
        (problem.decideCompatible pair.1 pair.2) hcompatibleB
    exact ⟨problem.left.sound pair.1 hleft,
      problem.right.sound pair.2 hright, hcompatible⟩
  · rintro ⟨hleft, hright, hcompatible⟩
    exact ⟨(problem.mem_candidates_iff pair).mpr
      ⟨problem.left.complete pair.1 hleft,
        problem.right.complete pair.2 hright⟩,
      @decide_eq_true (problem.compatible pair.1 pair.2)
        (problem.decideCompatible pair.1 pair.2) hcompatible⟩

structure ProductFound {α : Type u} {β : Type v}
    (problem : ProductProblem α β) where
  value : α × β
  leftAdmissible : problem.left.Admissible value.1
  rightAdmissible : problem.right.Admissible value.2
  compatible : problem.compatible value.1 value.2
  least : ∀ other : α × β,
    problem.left.Admissible other.1 →
    problem.right.Admissible other.2 →
    problem.compatible other.1 other.2 →
    problem.score value ≤ problem.score other

inductive ProductResult {α : Type u} {β : Type v}
    (problem : ProductProblem α β) where
  | found (witness : ProductFound problem)
  | refused (exhaustive : ∀ pair : α × β,
      problem.left.Admissible pair.1 →
      problem.right.Admissible pair.2 →
      ¬ problem.compatible pair.1 pair.2)

def synthesizeProduct {α : Type u} {β : Type v}
    (problem : ProductProblem α β) : ProductResult problem :=
  match h : SeamColoring.argMin? problem.score problem.feasible with
  | none =>
      .refused (by
        have hempty : problem.feasible = [] :=
          (SeamColoring.argMin_eq_none_iff problem.score problem.feasible).mp h
        intro pair hleft hright hcompatible
        have hmem : pair ∈ problem.feasible :=
          (problem.mem_feasible_iff pair).mpr
            ⟨hleft, hright, hcompatible⟩
        rw [hempty] at hmem
        exact List.not_mem_nil hmem)
  | some value =>
      let hmem := problem.mem_feasible_iff value |>.mp
        (SeamColoring.argMin_mem problem.score h)
      .found {
        value := value
        leftAdmissible := hmem.1
        rightAdmissible := hmem.2.1
        compatible := hmem.2.2
        least := by
          intro other hleft hright hcompatible
          exact SeamColoring.argMin_le_of_mem problem.score h
            ((problem.mem_feasible_iff other).mpr
              ⟨hleft, hright, hcompatible⟩)
      }

def synthesizeProductCapped {α : Type u} {β : Type v}
    (problem : ProductProblem α β) (limits : Limits) :
    Capped (ProductResult problem) :=
  let count := problem.left.values.length * problem.right.values.length
  if hcount : count ≤ limits.maxProducts then
    .ready (synthesizeProduct problem)
  else
    .tooLarge .products count limits.maxProducts

namespace ProductResult

def isFound {α : Type u} {β : Type v} {problem : ProductProblem α β} :
    ProductResult problem → Bool
  | .found _ => true
  | .refused _ => false

end ProductResult

/-! ## Executed fixtures -/

def generousLimits : Limits where
  maxStates := 16
  maxOperations := 16
  maxColorings := 1_000_000
  maxSubsets := 1_000_000
  maxProducts := 1_000_000

def pinCarrier : Carrier Cost.PinSet where
  values := SeamColoring.pinStates
  nodup := by decide
  complete := SeamColoring.pinStates_complete

theorem slot_minimum_seam_search_is_admitted :
    (synthesizeMinimumSeamCapped Cost.pinInv pinCarrier
      [false, true] false generousLimits).isReady = true := by
  decide

def c5Carrier : Carrier ClashGraph.C5 where
  values := ClashGraph.c5Vertices
  nodup := ClashGraph.c5.vertices_nodup
  complete := ClashGraph.c5.vertices_complete

def c5CliqueResult : CliqueResult c5Carrier ClashGraph.c5Adjacent :=
  synthesizeMaximumClique c5Carrier ClashGraph.c5Adjacent

def c5MaximumSize? : Option Nat :=
  (minimumCliqueComplement? c5Carrier ClashGraph.c5Adjacent).map List.length

theorem c5_maximum_clique_is_two :
    c5MaximumSize? = some 2 := by decide

/-! ### The full finite Slot protocol

All eight bit patterns are present: using only the four invariant-satisfying
states here would not be a carrier of `Slots` and would make global conclusions
false by omission. -/

def slotStates : List LiveSegmented.Slots :=
  [⟨false, false, false⟩, ⟨false, false, true⟩,
   ⟨false, true, false⟩, ⟨false, true, true⟩,
   ⟨true, false, false⟩, ⟨true, false, true⟩,
   ⟨true, true, false⟩, ⟨true, true, true⟩]

def slotCarrier : Carrier LiveSegmented.Slots where
  values := slotStates
  nodup := by decide
  complete := by
    intro state
    rcases state with ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> simp [slotStates]

def claimOperations : Carrier LiveSegmented.ClaimOp where
  values := [.claimA, .claimB]
  nodup := by decide
  complete := by intro operation; cases operation <;> simp

def slotProtocolInput : ProtocolInput
    LiveSegmented.Slots LiveSegmented.ClaimOp where
  states := slotCarrier
  operations := claimOperations
  step := LiveSegmented.claimStep

def slotProtocolScope : ProtocolScope
    LiveSegmented.Slots LiveSegmented.ClaimOp where
  toProtocolInput := slotProtocolInput
  closed := by decide

theorem slot_protocol_check_is_accepted :
    (checkProtocol slotProtocolInput generousLimits).isAccepted = true := by
  decide

theorem slot_reachability_is_computed_not_authored :
    slotProtocolScope.reachableB LiveSegmented.sO LiveSegmented.sA = true
      ∧ slotProtocolScope.reachableB LiveSegmented.sO LiveSegmented.sB = true
      ∧ slotProtocolScope.reachableB LiveSegmented.sO LiveSegmented.sC = false := by
  decide

def slotPalette : List (Fin 3) := [0, 1, 2]

theorem slot_live_minimum_cap_is_admitted :
    (synthesizeMinimumLiveSeamCapped slotProtocolScope
      LiveSegmented.atMostOne slotPalette 0 generousLimits).isReady = true := by
  decide

def slotScenarioCliqueMaximum? :=
  maximumPoolCliqueSize? CliqueLive.slotScenario.paths
    (scenarioClashB LiveSegmented.atMostOne LiveSegmented.claimStep
      CliqueLive.slotScenario)

theorem slot_exact_maximum_scenario_clique_is_two :
    slotScenarioCliqueMaximum? = some 2 := by decide

def duplicateSlotScenario :
    ForkGrade.Scenario LiveSegmented.Slots LiveSegmented.ClaimOp where
  root := LiveSegmented.sO
  paths := [[.claimA], [.claimA], [.claimB]]

theorem duplicate_scenario_is_rejected_by_nodup_boundary :
    ¬ duplicateSlotScenario.paths.Nodup := by decide

def reversedSlotScenario :
    ForkGrade.Scenario LiveSegmented.Slots LiveSegmented.ClaimOp where
  root := CliqueLive.slotScenario.root
  paths := CliqueLive.slotScenario.paths.reverse

theorem reversed_scenario_is_nodup : reversedSlotScenario.paths.Nodup := by
  decide

theorem reversed_scenario_capped_search_is_admitted :
    (synthesizeMaximumScenarioCliqueCapped LiveSegmented.atMostOne
      LiveSegmented.claimStep reversedSlotScenario reversed_scenario_is_nodup
      generousLimits).isReady = true := by decide

theorem reversed_scenario_maximum_is_two :
    maximumPoolCliqueSize? reversedSlotScenario.paths
      (scenarioClashB LiveSegmented.atMostOne LiveSegmented.claimStep
        reversedSlotScenario) = some 2 := by decide

/-- The existing, independently proved Slot witnesses pin the exact global and
live widths without forcing the kernel to normalise all `3^8` proof-carrying
search branches during every import.  The synthesizers above search those same
judgements when a caller actually requests a result. -/
theorem slot_exact_width_certificates :
    LiveSegmented.LeastSuch
        (LiveSegmented.LiveWidth LiveSegmented.slotProtocol
          LiveSegmented.atMostOne) 2
      ∧ LiveSegmented.LeastSuch
        (LiveSegmented.GlobalWidth LiveSegmented.atMostOne) 3 :=
  ⟨CliqueLive.slot_live_least_width, CliqueLive.slot_global_least_width⟩

theorem slot_live_clique_two_and_no_triangle :
    CliqueLive.LiveClique LiveSegmented.slotProtocol
        LiveSegmented.atMostOne LiveSegmented.sO
        [LiveSegmented.sA, LiveSegmented.sB]
      ∧ ∀ base x y z, ¬ CliqueLive.LiveClique
        LiveSegmented.slotProtocol LiveSegmented.atMostOne base [x, y, z] :=
  ⟨CliqueLive.slot_live_clique_two, CliqueLive.no_live_triangle⟩

/-- The existing fork fixture remains load-bearing: the synthesized finite
search layer imports, rather than duplicates, its proof that the two-branch
scenario has the derived clique floor one. -/
theorem slot_fork_floor_fixture :
    CliqueLive.slotScenario.paths.length - 1 ≤
        ForkGrade.liveOptimum CliqueLive.slotSpace
      ∧ ForkGrade.liveOptimum CliqueLive.slotSpace = 1 :=
  CliqueLive.slotScenario_floor_is_one

def tinyLimits : Limits where
  maxStates := 3
  maxOperations := 1
  maxColorings := 1
  maxSubsets := 1
  maxProducts := 1

theorem state_cap_refuses_before_pin_coloring_enumeration :
    (synthesizeMinimumSeamCapped Cost.pinInv pinCarrier
      [false, true] false tinyLimits).refusalAxis? = some .states := by
  decide

def boolAxis : Axis Bool where
  values := [false, true]
  Admissible := fun _ => True
  sound := by simp
  complete := by intro value _; cases value <;> simp

def unitAxis : Axis Unit where
  values := [()]
  Admissible := fun _ => True
  sound := by simp
  complete := by intro value _; cases value; simp

def boolUnitProduct : ProductProblem Bool Unit where
  left := boolAxis
  right := unitAxis
  compatible := fun left _ => left = true
  decideCompatible := fun left _ => inferInstance
  score := fun pair => if pair.1 then 0 else 1

theorem exact_product_finds_only_compatible_pair :
    (synthesizeProduct boolUnitProduct).isFound = true := by decide

theorem product_cap_refuses_before_cartesian_enumeration :
    (synthesizeProductCapped boolUnitProduct tinyLimits).refusalAxis? =
      some .products := by decide

end Uwueave.FiniteProductSearch
