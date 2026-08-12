import Uwueave.FiniteRepairMenu

namespace Canary.Wave29.WrongLeastMenu

open Uwueave Uwueave.FiniteRepairMenu
open Uwueave.FiniteRepairMenu.Examples

-- Canonical authored order selects stable id 20, not the later applicable row.
example : positiveResult.foundId? = some ⟨40⟩ := by
  decide

end Canary.Wave29.WrongLeastMenu
