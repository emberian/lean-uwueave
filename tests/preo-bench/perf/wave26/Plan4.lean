import Uwueave.Preo.PlanningSurface

namespace PreoBench.Wave26.Plan4

open Uwueave Uwueave.Preo
open Uwueave.Preo.Planning.Examples

preo_plan P00 for ProtocolSurface.NativeCoalescing over (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions, maxChoices := 2,
  problem := scheduleRefusalProblem } result
preo_plan P01 for ProtocolSurface.NativeCoalescing over (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions, maxChoices := 2,
  problem := scheduleRefusalProblem } result
preo_plan P02 for ProtocolSurface.NativeCoalescing over (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions, maxChoices := 2,
  problem := scheduleRefusalProblem } result
preo_plan P03 for ProtocolSurface.NativeCoalescing over (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions, maxChoices := 2,
  problem := scheduleRefusalProblem } result

end PreoBench.Wave26.Plan4
