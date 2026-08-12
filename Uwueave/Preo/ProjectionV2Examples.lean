/-
# Uwueave.Preo.ProjectionV2Examples — checked V2 examples

The proof-originated full export and adversarial budget rows remain under their
historical `ProjectionV2.Examples` names, but are now explicit opt-ins. This is
the only V2 layer that imports proof-indexed `Export`; production V2 validation
and rendering do not. Exact large-string checks live in `ProjectionV2Fixtures`.
-/
import Uwueave.Preo.ProjectionV2
import Uwueave.Preo.Export

namespace Uwueave.Preo.ProjectionV2

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

namespace Examples

private def validationError? {alpha : Type} :
    ValidationResult alpha → Option ValidationError
  | .ok _ => none
  | .error error => some error

def config : ValidationConfig where
  bounds := {
    maxFields := 8
    maxInvariants := 8
    maxFutures := 8
    maxSessions := 8
    maxPlans := 8
    maxBudgets := 8
    maxObligationsPerSession := 8
    maxActionsPerPlan := 8
    maxProfileEntriesPerPlan := 5
    maxProfileEntriesPerBudget := 5
    maxParticipantsPerDemand := 8
    maxWitnessWords := 8 }

def fullEncoding : ArtifactEncoding :=
  Export.Examples.bundle.project.encoding

def fullExport : Projection := Projection.ofEncoding fullEncoding

/-- Acceptance exercises the proof-originated Export bundle with every row
family nonempty, including its exact five-currency budget. -/
theorem full_export_is_nonempty :
    fullEncoding.fields.length = 1
      ∧ fullEncoding.invariants.length = 1
      ∧ fullEncoding.futures.length = 1
      ∧ fullEncoding.sessions.length = 1
      ∧ fullEncoding.plans.length = 1
      ∧ fullEncoding.budgets.length = 1 := by decide

theorem full_export_validates : (validate config fullExport).isOk = true := by decide

def duplicateBudget : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets ++ fullEncoding.budgets } }

theorem duplicate_budget_refused :
    validationError? (validate config duplicateBudget) =
      some (.duplicateBudgetId 411) := by decide

def danglingBudgetSession : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with sessionId := 999 } } }

theorem dangling_budget_session_refused :
    validationError? (validate config danglingBudgetSession) =
      some (.danglingBudgetSession 411 999) := by decide

def danglingBudgetPlan : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with planId := 999 } } }

theorem dangling_budget_plan_refused :
    validationError? (validate config danglingBudgetPlan) =
      some (.danglingBudgetPlan 411 999) := by decide

def mismatchedBudgetSession : Projection :=
  { fullExport with encoding :=
      { fullEncoding with
        sessions := fullEncoding.sessions ++ fullEncoding.sessions.map fun session =>
          { session with id := 999 }
        budgets := fullEncoding.budgets.map fun budget =>
          { budget with sessionId := 999 } } }

theorem mismatched_budget_session_refused :
    validationError? (validate config mismatchedBudgetSession) =
      some (.budgetPlanSessionMismatch 411 999 407) := by decide

def zeroProfile : List (Currency × Nat) :=
  [(.peerBarrier, 0), (.arbiterCut, 0), (.networkRound, 0),
   (.userPrompt, 0), (.rollback, 0)]

def actionProfileLie : Projection :=
  { fullExport with encoding :=
      { fullEncoding with plans := fullEncoding.plans.map fun plan =>
          { plan with profile := zeroProfile } } }

theorem action_profile_lie_refused :
    validationError? (validate config actionProfileLie) =
      some (.planProfileMismatch 408 zeroProfile
        [(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
         (.userPrompt, 0), (.rollback, 0)]) := by decide

def mismatchedBudgetProfile : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with realizedProfile := zeroProfile } } }

theorem mismatched_budget_profile_refused :
    validationError? (validate config mismatchedBudgetProfile) =
      some (.budgetProfileMismatch 411 408) := by decide

def nonCanonicalBudgetLimits : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with limits := [] } } }

theorem noncanonical_budget_limits_refused :
    validationError? (validate config nonCanonicalBudgetLimits) =
      some (.nonCanonicalBudgetLimits 411 []) := by decide

def exceededBudgetLimit : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with limits := zeroProfile } } }

theorem exceeded_budget_limit_refused :
    validationError? (validate config exceededBudgetLimit) =
      some (.budgetLimitExceeded 411 .peerBarrier 2 0) := by decide

/-- Coverage is checked from session data to the exact referenced plan.  This
fabricated empty action list cannot cover either exported obligation even when
its profile is changed to an honest empty histogram. -/
def uncoveredObligation : Projection :=
  { fullExport with encoding :=
      { fullEncoding with
        plans := fullEncoding.plans.map fun plan =>
          { plan with actions := [], profile := zeroProfile }
        budgets := [] } }

theorem uncovered_obligation_refused :
    validationError? (validate config uncoveredObligation) =
      some (.uncoveredObligation 408 407 0) := by decide

def zeroBudgetBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxBudgets := 0 } }

theorem budget_bound_refused :
    validationError? (validate zeroBudgetBound fullExport) =
      some (.budgetListTooLarge .budgets 1 0) := by decide

def wrongSchema : Projection := { fullExport with schema := ProjectionV1.schema }

theorem wrong_schema_refused :
    validationError? (validate config wrongSchema) =
      some (.wrongSchema schema ProjectionV1.schema) := by decide

/-- The public renderer path preserves a precise refusal and therefore cannot
manufacture a private validated value as fallback. -/
theorem renderer_preserves_error :
    validateAndRender config exceededBudgetLimit =
      .error (.budgetLimitExceeded 411 .peerBarrier 2 0) := by
  rfl

end Examples

end Uwueave.Preo.ProjectionV2
