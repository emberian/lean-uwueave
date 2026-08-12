import Uwueave.Preo.PlanningSurface

namespace PreoBench.Wave26.Plan1

open Uwueave Uwueave.Preo
open Uwueave.Preo.Planning.Examples

preo_plan P00 for ProtocolSurface.NativeCoalescing over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} result

end PreoBench.Wave26.Plan1
