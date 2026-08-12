import Uwueave.Preo.Elab

namespace PreoBench.Export

open Uwueave Uwueave.Preo

def config : ProjectionV2.ValidationConfig where
  bounds := {
    maxFields := 8, maxInvariants := 8, maxFutures := 8,
    maxSessions := 8, maxPlans := 8, maxBudgets := 8,
    maxObligationsPerSession := 8, maxActionsPerPlan := 8,
    maxProfileEntriesPerPlan := 5, maxProfileEntriesPerBudget := 5,
    maxParticipantsPerDemand := 8, maxWitnessWords := 8 }

preo Subject where
  field marker : Counter
  invariant nonnegative : marker ≤ marker
  protocol P over Unit := Protocol.coalescingProtocol
  session S runs P at ()

preo_budget Accepted for Subject.S : Subject.S.plan.profile :=
  Subject.S.exactProfileUpperBound

preo_export Output from Subject : config :=
  declaration := { id := 100, stateType := 101, schema := 1 }
  | field marker := { id := 102, kind := 10, carrier := 101, key := none }
  | invariant nonnegative := {
    id := 103, carrier := 101, codec := Uwueave.Preo.Export.Examples.natCodec,
    answered := rfl }
  | budget Accepted for S := {
    id := 106, session := 104, plan := 105, samePlan := rfl }

end PreoBench.Export
