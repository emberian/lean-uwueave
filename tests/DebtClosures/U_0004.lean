import Uwueave.Budget

open Uwueave Uwueave.Budget Uwueave.Cost

/-! U-0004 closes at the exact boundary promised by the source marker: maximum
forced-floor search over an explicit finite decomposition universe, with
semantic evidence in both search branches and a cap checked before search. -/

#check IsForcedDecomposition.forcedFloor
#check MaximumForcedFloor.forcedFloor
#check MaximumForcedFloor.greatest
#check MaximumForcedFloorResult.refused
#check maximumForcedFloorCapped_eq_ready_of_le
#check maximumForcedFloorCapped_is_tooLarge_of_lt

theorem debtClosure_U_0004 :
    (∃ maximum : MaximumForcedFloor budgetDecompositionFoundUniverse,
      maximum.blocks = budgetBlocks
        ∧ ForcedFloor budgetWorkload maximum.blocks.length
        ∧ (∀ other : List (List Nat),
          other ∈ budgetDecompositionFoundUniverse.candidates →
          IsForcedDecomposition budgetWorkload other →
          other.length ≤ maximum.blocks.length))
      ∧ (∀ blocks : List (List Nat),
        blocks ∈ budgetDecompositionRefusalUniverse.candidates →
        ¬ IsForcedDecomposition budgetWorkload blocks)
      ∧ (maximumForcedFloor budgetDecompositionFoundUniverse).blocks? =
        some budgetBlocks
      ∧ (maximumForcedFloorCapped budgetDecompositionFoundUniverse 3).isReady = true
      ∧ (maximumForcedFloorCapped budgetDecompositionFoundUniverse 3).isFound = true
      ∧ (maximumForcedFloorCapped budgetDecompositionFoundUniverse 3).maximumLength? =
        some 3
      ∧ (maximumForcedFloorCapped budgetDecompositionRefusalUniverse 3).isReady = true
      ∧ (maximumForcedFloorCapped budgetDecompositionRefusalUniverse 3).isFound = false
      ∧ (maximumForcedFloorCapped budgetDecompositionFoundUniverse 2).isReady = false
      ∧ (maximumForcedFloorCapped budgetDecompositionFoundUniverse 2).capRefusal? =
        some (3, 2) := by
  refine ⟨budgetDecompositionFound_evidence,
    budgetDecompositionRefusal_exhaustive,
    budgetDecompositionFound_exact.1,
    budgetDecompositionFound_exact.2.1,
    budgetDecompositionFound_exact.2.2.1,
    budgetDecompositionFound_exact.2.2.2,
    budgetDecompositionRefusal_exact.1,
    budgetDecompositionRefusal_exact.2.1,
    budgetDecompositionCap_exact.1,
    budgetDecompositionCap_exact.2.2.2⟩

#print axioms debtClosure_U_0004
