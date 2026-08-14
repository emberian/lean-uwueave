import Uwueave.FiniteProductClosure

open Uwueave

theorem debtClosure_U_0045 :
    (∀ (scope : FiniteProductClosure.ClosedScope)
        (entry : FiniteRepairMenu.MenuCandidate
          (Preo.Planning.sharedBudgetPromise scope.space.budget)),
      entry ∈ scope.menuEntries ↔
        ∃ code : scope.Code, scope.entry code = entry)
      ∧ (∀ (scope : FiniteProductClosure.ClosedScope)
        (candidate : RepairSynthesis.Candidate
          (Preo.Planning.sharedBudgetPromise scope.space.budget)),
      candidate ∈ scope.catalog.entries ↔
        ∃ code : scope.Code, (scope.entry code).candidate = candidate) := by
  exact ⟨FiniteProductClosure.ClosedScope.mem_menuEntries_iff,
    FiniteProductClosure.ClosedScope.mem_catalog_iff⟩
