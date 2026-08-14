import Uwueave.ChoreoTemporal

open Uwueave
open Uwueave.ChoreoRec
open Uwueave.ChoreoTemporal

universe u v

theorem debtClosure_U_0014
    {R : Type v} {S : Type u} [MergeState S] [DecidableEq R]
    {branches : Nat → Bool} {term : RecChoreo R S} (roster : List R)
    (execution : RosterExecution branches term)
    (hroster : roster ≠ []) (hwell : BarrierWellFormed term)
    (hfair : PrefixFair execution)
    (hdelivery : EventualBarrierDelivery roster execution) :
    ∃ arrival release,
      arrival ≤ release ∧
      MatchingBarrier roster (execution.endpoints arrival) ∧
      execution.delivered release = true ∧
    (WellGuarded guardedReadLoop ∧
      ¬ BarrierWellFormed guardedReadLoop) ∧
    (Deadlocked boolRoster mismatchedBarrierRuntime ∧
      ¬ MatchingBarrier boolRoster mismatchedEndpoints) := by
  obtain ⟨arrival, release, hle, hmatching, hreleased⟩ :=
    temporal_deadlock_free roster execution hroster hwell hfair hdelivery
  exact ⟨arrival, release, hle, hmatching, hreleased,
    ⟨guardedReadLoop_wellGuarded, guardedReadLoop_not_barrierWellFormed⟩,
    mismatched_barrier_negative_fixture⟩

#check Uwueave.ChoreoTemporal.guardedBarrierExecution_deadlock_free
#check Uwueave.ChoreoTemporal.mismatched_barrier_negative_fixture
#print axioms debtClosure_U_0014
