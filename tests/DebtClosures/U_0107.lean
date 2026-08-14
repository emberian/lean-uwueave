import Uwueave.RepairSynthesis

open Uwueave
open Uwueave.Repair (Promise Repair)
open Uwueave.RepairSynthesis
open Uwueave.RepairSynthesis.CheckedMergePolicy

#check @MergeRequest.result_legal
#check @Policy.evaluate
#check @Outcome.price_is_backed
#check @Outcome.refusal_is_exhaustive

theorem debtClosure_U_0107 :
    (freeOutcome.route = .accepted
      ∧ Repair.anythingGoesPromise.inv freeOutcome.mergeResult) ∧
    (pricedCeilingOutcome.route = .pricedExit
      ∧ pricedCeilingOutcome.exitId? = some ⟨40⟩
      ∧ pricedCeilingOutcome.price? = some
          (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 2).price
      ∧ ¬ RepairMenu.ceilingPromise.inv pricedCeilingOutcome.mergeResult) ∧
    (∃ (Q : Promise) (repair : Repair RepairMenu.ceilingPromise Q),
      pricedCeilingOutcome.price? = some repair.price) ∧
    (refusingCeilingOutcome.route = .refused
      ∧ refusingCeilingOutcome.price? = none
      ∧ ∀ candidate : Candidate RepairMenu.ceilingPromise,
          candidate ∈ refusingCeilingPolicy.choices.entries →
            ¬ candidate.applicable) ∧
    (pendingCeilingOutcome.route = .pending
      ∧ pendingCeilingOutcome.price? = none
      ∧ pendingCeilingOutcome.pendingObligations = [missingCeilingRoute]
      ∧ pendingCeilingOutcome.pendingObligations ≠ []) := by
  refine ⟨free_outcome_accepts_merge, priced_exit_fixture, ?_,
    finite_refusal_fixture, pending_obligation_fixture⟩
  have hprice := priced_exit_fixture.2.2.1
  obtain ⟨Q, repair, hrepair⟩ :=
    pricedCeilingOutcome.price_is_backed hprice
  refine ⟨Q, repair, ?_⟩
  rw [hrepair]
  exact hprice

#print axioms debtClosure_U_0107
