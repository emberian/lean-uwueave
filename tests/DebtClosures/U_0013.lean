import Uwueave.ChoreoTemporal

open Uwueave
open Uwueave.ChoreoRec
open Uwueave.ChoreoTemporal

theorem debtClosure_U_0013 :
    (∀ length,
      unfoldPrefix noBranches guardedBarrierLoop length =
        finitePrefix noBranches guardedBarrierLoop length) ∧
    (∀ length,
      PrefixApproximates length
        (finitePrefix noBranches guardedBarrierLoop length)
        (infiniteTrace noBranches guardedBarrierLoop)) ∧
    (∀ fuel,
      finitePrefix noBranches guardedBarrierLoop fuel =
        finiteEvents noBranches (approximate fuel guardedBarrierLoop)) ∧
    ¬ Bisimilar (infiniteTrace noBranches guardedBarrierLoop)
      (infiniteTrace noBranches unguardedLoop) ∧
    (∀ {left right : Temporal.Trace (GlobalEvent Bool)},
      Bisimilar left right → ∀ replica index,
        projectTrace replica left index = projectTrace replica right index) := by
  exact ⟨fun length => unfoldPrefix_eq_finitePrefix _ _ length,
    fun length => finitePrefix_approximates _ _ length,
    guardedBarrierLoop_finite_prefix_approximation,
    guardedBarrierLoop_not_bisimilar_unguarded,
    fun h replica index => project_bisim_congr h replica index⟩

#check Uwueave.ChoreoTemporal.project_bisim_congr
#print axioms debtClosure_U_0013
