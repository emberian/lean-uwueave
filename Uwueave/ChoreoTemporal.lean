/-
# Uwueave.ChoreoTemporal — infinite recursive behavior and fair barrier progress.

`ChoreoRec.approximate` gives executable finite unfoldings. This module adds a
coalgebraic observation semantics: a recursive control state exposes one
observable action and its continuation forever, with `halted` padding finite
programs and `stuck` exposing an unguarded recursion instead of silently
diverging in the meta-language. A `Nat → GlobalEvent` trace is genuinely
infinite; `Nat` is an event index, never elapsed time.

The temporal barrier theorem keeps three facts separate:

* `BarrierWellFormed` includes ordinary action guardedness and a successful
  finite-prefix barrier check for every read-branch stream. Action
  guardedness alone is insufficient: the exact infinite read loop below is
  guarded and never synchronizes.
* `PrefixFair` says the scheduler eventually exposes each global behavior
  index. It is a named scheduler premise, not derived from syntax.
* `EventualBarrierDelivery` says a matching roster barrier is eventually
  released. It is a delivery premise, not derived from fairness or projection.

No theorem here proves a deployed scheduler fair, turns indices into seconds,
or accepts a partial roster barrier. The mismatched runtime from `ChoreoRec`
remains deadlocked and is repeated as the exact negative fixture.
-/
import Uwueave.ChoreoRec
import Uwueave.Temporal

namespace Uwueave.ChoreoTemporal

open Uwueave
open Uwueave.Choreo
open Uwueave.ChoreoRec

universe u v

variable {R : Type v} {S : Type u} [MergeState S]

/-! ## 1. One-step coalgebra and its infinite trace -/

/-- Observable recursive control events. Mutator and predicate functions are
intentionally abstracted to their behavioral labels: which replica writes,
which replica reads which branch, synchronization, termination, or rejection
of an unguarded head. State refinement remains owned by `ChoreoRec`'s finite
denotation and projection theorems. -/
inductive GlobalEvent (R : Type v) where
  | halted
  | stuck
  | write (replica : R)
  | read (replica : R) (branch : Bool)
  | barrier
  deriving DecidableEq, Repr

/-- Bounded head normalization. The bound is operationally observable: an
unguarded `mu var` yields `stuck`; guarded recursive heads expose their first
finite action. -/
def observeHead : Nat → RecChoreo R S → Bool → GlobalEvent R × RecChoreo R S
  | 0, term, _ => (.stuck, term)
  | _ + 1, .done, _ => (.halted, .done)
  | _ + 1, .write replica _ continuation, _ =>
      (.write replica, continuation)
  | _ + 1, .read replica _ yes no, branch =>
      (.read replica branch, if branch then yes else no)
  | _ + 1, .sync continuation, _ => (.barrier, continuation)
  | _ + 1, .var, _ => (.stuck, .var)
  | fuel + 1, .mu body, branch =>
      observeHead fuel (unfoldBody (.mu body) body) branch

/-- Normalize one recursive control state. `size + 1` is enough to inspect a
finite head spine; genuinely unguarded self-unfolding consumes the bound and
becomes `stuck`. -/
def observe (term : RecChoreo R S) (branch : Bool) :
    GlobalEvent R × RecChoreo R S :=
  observeHead (term.size + 1) term branch

/-- Control after `index` coalgebra observations. -/
def controlAt (branches : Nat → Bool) (initial : RecChoreo R S) :
    Nat → RecChoreo R S
  | 0 => initial
  | index + 1 =>
      (observe (controlAt branches initial index) (branches index)).2

/-- **Infinite recursive choreography semantics.** Finite programs remain
infinite by emitting `halted`; rejected unguarded heads emit `stuck`. -/
def infiniteTrace (branches : Nat → Bool) (term : RecChoreo R S) :
    Temporal.Trace (GlobalEvent R) :=
  fun index => (observe (controlAt branches term index) (branches index)).1

/-- The exact finite observation of the infinite behavior. -/
def finitePrefix (branches : Nat → Bool) (term : RecChoreo R S)
    (length : Nat) : List (GlobalEvent R) :=
  List.ofFn fun index : Fin length => infiniteTrace branches term index

/-- Tail of the branch oracle after one observed read slot. -/
def branchTail (branches : Nat → Bool) : Nat → Bool :=
  fun index => branches (index + 1)

/-- Independent fuel-bounded observation of the recursive coalgebra. Unlike
`finitePrefix`, this definition does not index into the infinite trace: it
actually iterates `observe` and its returned continuation. -/
def unfoldPrefix (branches : Nat → Bool) (term : RecChoreo R S) :
    Nat → List (GlobalEvent R)
  | 0 => []
  | length + 1 =>
      let next := observe term (branches 0)
      next.1 :: unfoldPrefix (branchTail branches) next.2 length

/-- Advancing the independent coalgebra once agrees with advancing
`controlAt` by one event index. -/
theorem controlAt_tail (branches : Nat → Bool) (term : RecChoreo R S)
    (index : Nat) :
    controlAt (branchTail branches) (observe term (branches 0)).2 index =
      controlAt branches term (index + 1) := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simp only [controlAt]
      rw [ih]
      rfl

theorem infiniteTrace_tail (branches : Nat → Bool)
    (term : RecChoreo R S) (index : Nat) :
    infiniteTrace (branchTail branches) (observe term (branches 0)).2 index =
      infiniteTrace branches term (index + 1) := by
  unfold infiniteTrace
  rw [controlAt_tail]
  rfl

/-- **Finite-prefix approximation theorem.** Independently iterating the
recursive coalgebra for `length` steps yields exactly the first `length`
observations of its infinite trace. -/
theorem unfoldPrefix_eq_finitePrefix (branches : Nat → Bool)
    (term : RecChoreo R S) (length : Nat) :
    unfoldPrefix branches term length = finitePrefix branches term length := by
  induction length generalizing branches term with
  | zero => rfl
  | succ length ih =>
      rw [finitePrefix, List.ofFn_succ]
      simp only [unfoldPrefix]
      congr 1
      rw [ih]
      apply congrArg List.ofFn
      funext index
      exact infiniteTrace_tail branches term index

/-- A list is the first `length` observations of an infinite behavior. -/
def PrefixApproximates (length : Nat) (observed : List (GlobalEvent R))
    (trace : Temporal.Trace (GlobalEvent R)) : Prop :=
  observed = List.ofFn fun index : Fin length => trace index

/-- **Finite-prefix approximation, general form.** Every finite observation is
exactly the corresponding prefix of the coinductive trace. -/
theorem finitePrefix_approximates (branches : Nat → Bool)
    (term : RecChoreo R S) (length : Nat) :
    PrefixApproximates length (finitePrefix branches term length)
      (infiniteTrace branches term) :=
  rfl

@[simp] theorem finitePrefix_length (branches : Nat → Bool)
    (term : RecChoreo R S) (length : Nat) :
    (finitePrefix branches term length).length = length := by
  simp [finitePrefix]

/-! ## 2. Behavioral equivalence and endpoint congruence -/

/-- Bisimilarity of deterministic observation coalgebras: every finite
observation agrees. This pointwise formulation is the extensional greatest
bisimulation on `Nat`-indexed traces. -/
def Bisimilar (left right : Temporal.Trace (GlobalEvent R)) : Prop :=
  ∀ index, left index = right index

theorem Bisimilar.refl (trace : Temporal.Trace (GlobalEvent R)) :
    Bisimilar trace trace :=
  fun _ => rfl

theorem Bisimilar.symm {left right : Temporal.Trace (GlobalEvent R)}
    (h : Bisimilar left right) : Bisimilar right left :=
  fun index => (h index).symm

theorem Bisimilar.trans {left middle right : Temporal.Trace (GlobalEvent R)}
    (hlm : Bisimilar left middle) (hmr : Bisimilar middle right) :
    Bisimilar left right :=
  fun index => (hlm index).trans (hmr index)

/-- Observable endpoint events. A write by another replica is explicit
`silent`; the core's uncommunicated read is observed at every endpoint. -/
inductive EndpointEvent where
  | halted
  | stuck
  | silent
  | act
  | observe (branch : Bool)
  | barrier
  deriving DecidableEq, Repr

/-- Pointwise endpoint projection of an infinite global event. -/
def projectEvent [DecidableEq R] (replica : R) : GlobalEvent R → EndpointEvent
  | .halted => .halted
  | .stuck => .stuck
  | .write writer => if replica = writer then .act else .silent
  | .read _ branch => .observe branch
  | .barrier => .barrier

def projectTrace [DecidableEq R] (replica : R)
    (trace : Temporal.Trace (GlobalEvent R)) : Temporal.Trace EndpointEvent :=
  fun index => projectEvent replica (trace index)

/-- **Bisimulation congruence for projected endpoints.** No endpoint can
distinguish globally bisimilar recursive behaviors. -/
theorem project_bisim_congr [DecidableEq R]
    {left right : Temporal.Trace (GlobalEvent R)}
    (h : Bisimilar left right) (replica : R) :
    ∀ index, projectTrace replica left index = projectTrace replica right index := by
  intro index
  simp [projectTrace, h index]

/-! ## 3. Exact recursive positive and negative fixtures -/

def noBranches : Nat → Bool := fun _ => false

@[simp] theorem observe_guardedBarrierLoop (branch : Bool) :
    observe guardedBarrierLoop branch =
      (.barrier, guardedBarrierLoop) := by
  rfl

theorem guardedBarrierLoop_control (index : Nat) :
    controlAt noBranches guardedBarrierLoop index = guardedBarrierLoop := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simp [controlAt, ih, observe_guardedBarrierLoop]

/-- The guarded recursive barrier has a genuine infinite barrier trace. -/
theorem guardedBarrierLoop_trace (index : Nat) :
    infiniteTrace noBranches guardedBarrierLoop index = .barrier := by
  simp [infiniteTrace, guardedBarrierLoop_control, observe_guardedBarrierLoop]

/-- Finite Choreo observation, used to connect the coalgebraic trace to the
existing fuel approximants on the canonical recursive fixture. -/
def finiteEvents (branches : Nat → Bool) : Choreo R S → List (GlobalEvent R)
  | .done => []
  | .write replica _ continuation =>
      .write replica :: finiteEvents (fun n => branches (n + 1)) continuation
  | .read replica _ yes no =>
      if branches 0 then
        .read replica true :: finiteEvents (fun n => branches (n + 1)) yes
      else
        .read replica false :: finiteEvents (fun n => branches (n + 1)) no
  | .sync continuation =>
      .barrier :: finiteEvents (fun n => branches (n + 1)) continuation

theorem guardedBarrierLoop_finiteEvents (branches : Nat → Bool) (fuel : Nat) :
    finiteEvents branches (approximate fuel guardedBarrierLoop) =
      List.replicate fuel (.barrier : GlobalEvent Bool) := by
  induction fuel generalizing branches with
  | zero => simp [guardedBarrierLoop, finiteEvents]
  | succ fuel ih =>
      rw [guardedBarrierLoop_unfold]
      simp only [finiteEvents, List.replicate_succ]
      rw [ih (branches := fun n => branches (n + 1))]

theorem list_ofFn_const_eq_replicate {A : Type} (value : A) (length : Nat) :
    List.ofFn (fun _ : Fin length => value) = List.replicate length value := by
  induction length with
  | zero => rw [List.ofFn_zero]; rfl
  | succ length ih =>
      rw [List.ofFn_succ, List.replicate_succ, ih]

theorem guardedBarrierLoop_prefix (length : Nat) :
    finitePrefix noBranches guardedBarrierLoop length =
      List.replicate length (.barrier : GlobalEvent Bool) := by
  unfold finitePrefix
  have hfun :
      (fun index : Fin length =>
        infiniteTrace noBranches guardedBarrierLoop index) =
      (fun _ : Fin length => (.barrier : GlobalEvent Bool)) := by
    funext index
    exact guardedBarrierLoop_trace index
  rw [hfun]
  exact list_ofFn_const_eq_replicate _ _

/-- **Existing-fuel approximation agrees with every finite prefix** on the
canonical infinite recursive loop. -/
theorem guardedBarrierLoop_finite_prefix_approximation (fuel : Nat) :
    finitePrefix noBranches guardedBarrierLoop fuel =
      finiteEvents noBranches (approximate fuel guardedBarrierLoop) := by
  rw [guardedBarrierLoop_prefix, guardedBarrierLoop_finiteEvents]

@[simp] theorem observe_unguardedLoop (branch : Bool) :
    observe unguardedLoop branch = (.stuck, unguardedLoop) := by
  rfl

theorem unguardedLoop_stuck_at_zero :
    infiniteTrace noBranches unguardedLoop 0 = .stuck := by
  rfl

/-- Exact behavioral refutation: the guarded barrier loop is not bisimilar to
the rejected immediate self-loop. -/
theorem guardedBarrierLoop_not_bisimilar_unguarded :
    ¬ Bisimilar (infiniteTrace noBranches guardedBarrierLoop)
      (infiniteTrace noBranches unguardedLoop) := by
  intro h
  have hzero := h 0
  simp [guardedBarrierLoop_trace, unguardedLoop_stuck_at_zero] at hzero

/-! ## 4. Roster executions, fairness, delivery, and matching barriers -/

/-- A barrier is matching when the roster is nonempty and every listed
endpoint exposes a barrier at the same global behavior index. -/
def MatchingBarrier (roster : List R) (endpoints : R → EndpointEvent) : Prop :=
  roster ≠ [] ∧ ∀ replica ∈ roster, endpoints replica = .barrier

/-- The recursive behavior reaches a barrier on the selected read-branch
stream. This is stronger than action guardedness and is deliberately named. -/
def BarrierProductive (branches : Nat → Bool) (term : RecChoreo R S) : Prop :=
  Temporal.Eventually (fun event => event = .barrier)
    (infiniteTrace branches term)

/-- Whether an observation is the synchronization event. -/
def GlobalEvent.isBarrier : GlobalEvent R → Bool
  | .barrier => true
  | _ => false

theorem GlobalEvent.isBarrier_eq_true_iff (event : GlobalEvent R) :
    event.isBarrier = true ↔ event = .barrier := by
  cases event <;> simp [GlobalEvent.isBarrier]

/-- Executable search of one finite recursive trace prefix. `bound` is an event
count, not a duration. -/
def barrierWithin (branches : Nat → Bool) (term : RecChoreo R S) : Nat → Bool
  | 0 => false
  | bound + 1 =>
      (infiniteTrace branches term bound).isBarrier ||
        barrierWithin branches term bound

/-- A successful finite checker returns an actual event index at which the
recursive behavior reaches a barrier. -/
theorem barrierWithin_sound {branches : Nat → Bool} {term : RecChoreo R S}
    {bound : Nat} (h : barrierWithin branches term bound = true) :
    BarrierProductive branches term := by
  induction bound with
  | zero => simp [barrierWithin] at h
  | succ bound ih =>
      have hcases :
          (infiniteTrace branches term bound).isBarrier = true ∨
            barrierWithin branches term bound = true := by
        simpa [barrierWithin, Bool.or_eq_true] using h
      rcases hcases with hnow | hearlier
      · exact ⟨bound, (GlobalEvent.isBarrier_eq_true_iff _).1 hnow⟩
      · exact ih hearlier

/-- Accepted barrier-recursive behavior: ordinary guardedness plus a checked
finite-prefix witness of barrier reachability. This is stronger than action
guardedness without assuming the temporal conclusion as a proposition. -/
def BarrierWellFormed (term : RecChoreo R S) : Prop :=
  WellGuarded term ∧
    ∀ branches : Nat → Bool,
      ∃ bound, barrierWithin branches term bound = true

theorem BarrierWellFormed.guarded
    {term : RecChoreo R S} (h : BarrierWellFormed term) :
    WellGuarded term :=
  h.1

theorem BarrierWellFormed.productive {term : RecChoreo R S}
    (h : BarrierWellFormed term) (branches : Nat → Bool) :
    BarrierProductive branches term := by
  obtain ⟨bound, hchecked⟩ := h.2 branches
  exact barrierWithin_sound hchecked

/-- A roster execution samples the global infinite behavior according to an
explicit scheduler position and records whether the matching barrier's state
delivery has completed. -/
structure RosterExecution [DecidableEq R] (branches : Nat → Bool)
    (term : RecChoreo R S) where
  position : Temporal.Trace Nat
  endpoints : Temporal.Trace (R → EndpointEvent)
  delivered : Temporal.Trace Bool
  position_zero : position 0 = 0
  position_step : ∀ time,
    position (time + 1) = position time ∨
      position (time + 1) = position time + 1
  delivery_persistent : ∀ time,
    delivered time = true → delivered (time + 1) = true
  projection_exact : ∀ time replica,
    endpoints time replica =
      projectEvent replica (infiniteTrace branches term (position time))

/-- Scheduler fairness for this explicit execution: every global behavior
index is eventually exposed. This is an event-index coverage premise, not a
wall-clock bound. -/
def PrefixFair [DecidableEq R] {branches : Nat → Bool}
    {term : RecChoreo R S} (execution : RosterExecution branches term) : Prop :=
  ∀ index, Temporal.Eventually (fun current => current = index) execution.position

/-- Eventual delivery/release of each matching barrier. The predicate is a
deployment premise: projection and guardedness do not manufacture a network
delivery. -/
def EventualBarrierDelivery [DecidableEq R] {branches : Nat → Bool}
    {term : RecChoreo R S} (roster : List R)
    (execution : RosterExecution branches term) : Prop :=
  ∀ arrival,
    MatchingBarrier roster (execution.endpoints arrival) →
      ∃ release, arrival ≤ release ∧ execution.delivered release = true

/-- **Temporal deadlock freedom for recursive barriers.** Every accepted
barrier-recursive behavior reaches a matching roster barrier under prefix
fairness, and that barrier is eventually released under the separately named
delivery premise. -/
theorem temporal_deadlock_free [DecidableEq R]
    {branches : Nat → Bool} {term : RecChoreo R S} (roster : List R)
    (execution : RosterExecution branches term)
    (hroster : roster ≠ []) (hwell : BarrierWellFormed term)
    (hfair : PrefixFair execution)
    (hdelivery : EventualBarrierDelivery roster execution) :
    ∃ arrival release,
      arrival ≤ release ∧
      MatchingBarrier roster (execution.endpoints arrival) ∧
      execution.delivered release = true := by
  obtain ⟨index, hbarrier⟩ := hwell.productive branches
  obtain ⟨arrival, hposition⟩ := hfair index
  have hmatching : MatchingBarrier roster (execution.endpoints arrival) := by
    refine ⟨hroster, ?_⟩
    intro replica hreplica
    rw [execution.projection_exact, hposition, hbarrier]
    rfl
  obtain ⟨release, hle, hreleased⟩ := hdelivery arrival hmatching
  exact ⟨arrival, release, hle, hmatching, hreleased⟩

theorem guardedBarrierLoop_barrierWellFormed :
    BarrierWellFormed guardedBarrierLoop := by
  refine ⟨guardedBarrierLoop_wellGuarded, ?_⟩
  intro branches
  refine ⟨1, ?_⟩
  rfl

/-- Action guardedness alone does not promise a barrier: both branches of this
recursive read return immediately to the binder. -/
def guardedReadLoop : RecChoreo Bool Nat :=
  .mu (.read false (fun _ => false) .var .var)

theorem guardedReadLoop_wellGuarded : WellGuarded guardedReadLoop := by
  decide

@[simp] theorem observe_guardedReadLoop :
    observe guardedReadLoop false =
      (.read false false, guardedReadLoop) := by
  rfl

theorem guardedReadLoop_control (index : Nat) :
    controlAt noBranches guardedReadLoop index = guardedReadLoop := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simp [controlAt, ih, noBranches, observe_guardedReadLoop]

theorem guardedReadLoop_trace (index : Nat) :
    infiniteTrace noBranches guardedReadLoop index = .read false false := by
  simp [infiniteTrace, guardedReadLoop_control, noBranches,
    observe_guardedReadLoop]

theorem guardedReadLoop_no_barrier (bound : Nat) :
    barrierWithin noBranches guardedReadLoop bound = false := by
  induction bound with
  | zero => rfl
  | succ bound ih =>
      simp [barrierWithin, guardedReadLoop_trace, GlobalEvent.isBarrier, ih]

theorem guardedReadLoop_not_barrierWellFormed :
    ¬ BarrierWellFormed guardedReadLoop := by
  intro h
  obtain ⟨bound, hchecked⟩ := h.2 noBranches
  rw [guardedReadLoop_no_barrier] at hchecked
  contradiction

/-- A concrete fair, delivered infinite execution of the recursive barrier
loop. -/
def guardedBarrierExecution :
    RosterExecution noBranches guardedBarrierLoop where
  position := fun time => time
  endpoints := fun time replica =>
    projectEvent replica (infiniteTrace noBranches guardedBarrierLoop time)
  delivered := fun _ => true
  position_zero := rfl
  position_step := fun _ => Or.inr rfl
  delivery_persistent := fun _ _ => rfl
  projection_exact := fun _ _ => rfl

theorem guardedBarrierExecution_fair : PrefixFair guardedBarrierExecution :=
  fun index => ⟨index, rfl⟩

theorem guardedBarrierExecution_delivers :
    EventualBarrierDelivery boolRoster guardedBarrierExecution := by
  intro arrival _
  exact ⟨arrival, Nat.le_refl _, rfl⟩

theorem guardedBarrierExecution_deadlock_free :
    ∃ arrival release,
      arrival ≤ release ∧
      MatchingBarrier boolRoster (guardedBarrierExecution.endpoints arrival) ∧
      guardedBarrierExecution.delivered release = true :=
  temporal_deadlock_free boolRoster guardedBarrierExecution
    (by decide) guardedBarrierLoop_barrierWellFormed
    guardedBarrierExecution_fair guardedBarrierExecution_delivers

/-- The exact mismatched endpoint observation from `ChoreoRec`: one replica
waits at a barrier and the other has terminated. -/
def mismatchedEndpoints : Bool → EndpointEvent
  | false => .barrier
  | true => .halted

theorem mismatchedEndpoints_not_matching :
    ¬ MatchingBarrier boolRoster mismatchedEndpoints := by
  intro h
  have htrue := h.2 true (by simp [boolRoster])
  simp [mismatchedEndpoints] at htrue

/-- The old operational negative and the new temporal matching negative agree:
partial roster arrival is rejected, not hidden inside a fairness premise. -/
theorem mismatched_barrier_negative_fixture :
    Deadlocked boolRoster mismatchedBarrierRuntime ∧
      ¬ MatchingBarrier boolRoster mismatchedEndpoints :=
  ⟨mismatched_barrier_is_deadlocked, mismatchedEndpoints_not_matching⟩

end Uwueave.ChoreoTemporal
