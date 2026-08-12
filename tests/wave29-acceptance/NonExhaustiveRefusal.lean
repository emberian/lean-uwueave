import Uwueave.FiniteRepairMenu

namespace Canary.Wave29.NonExhaustiveRefusal

open Uwueave Uwueave.FiniteRepairMenu
open Uwueave.FiniteRepairMenu.Examples

-- The computed result proves each listed row inapplicable.  That negation
-- cannot be used as a positive applicability witness.
example : (unavailable 50).candidate.applicable := by
  exact impossible_refusal_is_exactly_exhaustive (unavailable 50)
    (by simp [refusedScope, refusedInput])

end Canary.Wave29.NonExhaustiveRefusal
