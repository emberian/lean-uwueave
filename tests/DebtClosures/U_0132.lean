import Uwueave.FiniteProductClosure

open Uwueave

/-- U-0132 claims completeness only for the declared, resource-admitted
four-constructor grammar. It does not quantify over arbitrary `Repair` values. -/
theorem debtClosure_U_0132 :
    (∀ (scope : FiniteProductClosure.ClosedScope)
        (entry : FiniteRepairMenu.MenuCandidate
          (Preo.Planning.sharedBudgetPromise scope.space.budget)),
      entry ∈ scope.menuEntries ↔
        ∃ code : scope.Code, scope.entry code = entry)
    ∧ (∀ (scope : FiniteProductClosure.ClosedScope)
        (candidate : RepairSynthesis.Candidate
          (Preo.Planning.sharedBudgetPromise scope.space.budget)),
      candidate ∈ scope.catalog.entries ↔
        ∃ code : scope.Code, (scope.entry code).candidate = candidate)
    ∧ FiniteProductClosure.fourTokenClosedScope.menuEntries.length = 6 := by
  exact
    ⟨FiniteProductClosure.ClosedScope.mem_menuEntries_iff,
      FiniteProductClosure.ClosedScope.mem_catalog_iff,
      FiniteProductClosure.four_constructor_catalog_has_six_rows⟩

#print axioms debtClosure_U_0132
