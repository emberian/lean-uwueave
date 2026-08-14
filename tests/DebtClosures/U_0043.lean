import Uwueave.FiniteProductClosure

open Uwueave

theorem debtClosure_U_0043 :
    (∀ (scope : FiniteProductClosure.ClosedScope)
        (entry : FiniteRepairMenu.MenuCandidate
          (Preo.Planning.sharedBudgetPromise scope.space.budget)),
      entry ∈ scope.menuEntries ↔
        ∃ code : scope.Code, scope.entry code = entry)
      ∧ (FiniteProductSearch.synthesizeProduct
          FiniteProductClosure.fixtureCoupledProblem).isFound = true
      ∧ FiniteProductClosure.fixtureUsableRepairPrice?.isSome = true
      ∧ (FiniteProductClosure.fourTokenClosedScope.synthesizeCoupledCapped
          FiniteProductClosure.fixtureCoupling
          FiniteProductSearch.tinyLimits).refusalAxis? = some .products := by
  exact ⟨FiniteProductClosure.ClosedScope.mem_menuEntries_iff,
    FiniteProductClosure.coupled_product_finds_a_compatible_pair,
    FiniteProductClosure.coupled_product_exposes_usable_repair,
    FiniteProductClosure.coupled_product_resource_refusal_precedes_enumeration⟩
