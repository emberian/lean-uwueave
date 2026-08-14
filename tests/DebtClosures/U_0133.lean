import Uwueave.FiniteProductClosure

open Uwueave

/-- U-0133 independently closes the bounded solver gap. The admitted coupled
search finds a usable row, the same boundary refuses before enumeration at a
small cap, and code membership is exactly applicability. Consequently a false
residual is filtered rather than misreported as exhaustive success. -/
theorem debtClosure_U_0133 :
    (FiniteProductClosure.fourTokenClosedScope.synthesizeCoupledCapped
      FiniteProductClosure.fixtureCoupling
      FiniteProductSearch.generousLimits).isReady = true
    ∧ (FiniteProductSearch.synthesizeProduct
      FiniteProductClosure.fixtureCoupledProblem).isFound = true
    ∧ FiniteProductClosure.fixtureUsableRepairPrice?.isSome = true
    ∧ (∀ (scope : FiniteProductClosure.ClosedScope) (code : scope.Code),
      code ∈ scope.codeAxis.values ↔
        (scope.entry code).candidate.applicable)
    ∧ FiniteProductClosure.inapplicableCatalog.minimum?
        FiniteProductClosure.zeroValuation = none
    ∧ (FiniteProductClosure.fourTokenClosedScope.synthesizeCoupledCapped
      FiniteProductClosure.fixtureCoupling
      FiniteProductSearch.tinyLimits).refusalAxis? = some .products := by
  refine
    ⟨by decide,
      FiniteProductClosure.coupled_product_finds_a_compatible_pair,
      FiniteProductClosure.coupled_product_exposes_usable_repair,
      ?_,
      FiniteProductClosure.inapplicable_candidate_is_not_returned,
      FiniteProductClosure.coupled_product_resource_refusal_precedes_enumeration⟩
  intro scope code
  exact ⟨scope.codeAxis.sound code, scope.codeAxis.complete code⟩

#print axioms debtClosure_U_0133
