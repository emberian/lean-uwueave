/-
U-0047 closes with a proof-carrying finite optimizer whose objective is exactly
`ForkGrade.liveCost`.  These checks retain the positive attained optimum, the
semantic refusal, the resource-first boundary, and the deployment premises in
their public types.
-/
import Uwueave.FiniteProductSearch

namespace Uwueave.DebtClosures.U0047

open Uwueave Uwueave.Cost Uwueave.SeamColoring Uwueave.ForkGrade

/- The acceptance text names the two downstream bounded interfaces.  Their
result payloads retain the width-minimal found branch and the exhaustive
refusal branch; the theorems below additionally certify the distinct
`ForkGrade.liveCost` objective. -/
#check FiniteProductSearch.synthesizeMinimumScenarioSeamCapped
#check FiniteProductSearch.synthesizeMinimumLiveSeamCapped
#check FiniteProductSearch.MinimumStrategy.least
#check FiniteProductSearch.StrategyResult.refused

theorem exact_live_cost_witness :
    match pinForkMinimumLiveSearch with
    | .found minimum =>
        liveCost minimum.strategy.seam pinStep pinForkScenario = 1
    | .refused _ => False :=
  pinForkMinimumLiveSearch_exact

theorem positive_fixture : pinForkMinimumLiveSearch.isFound = true :=
  pinForkMinimumLiveSearch_isFound

theorem negative_fixture : pinForkOneColorSearch.isFound = false :=
  pinForkOneColorSearch_isFound

theorem negative_is_exhaustive :
    ∀ strategy : LiveStrategy pinInv pinStep pinForkScenario Bool,
      ¬ UsesOnly pinStates [false] strategy.seam :=
  pinForkOneColorSearch_exhaustive

theorem cap_precedes_enumeration :
    synthesizeMinimumLiveStrategyCapped pinInv pinStep pinForkScenario
      pinStates pinStates_complete [false, true] false
      pinForkTightLiveLimits =
        CappedLiveSearch.tooLarge LiveSearchLimitAxis.colorings 16 15 :=
  pinForkLiveSearch_cap_exact

#print axioms exact_live_cost_witness
#print axioms negative_is_exhaustive
#print axioms cap_precedes_enumeration

end Uwueave.DebtClosures.U0047
