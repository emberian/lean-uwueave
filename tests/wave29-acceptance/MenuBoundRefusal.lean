import Uwueave.FiniteRepairMenu

namespace Canary.Wave29.MenuBoundRefusal

open Uwueave Uwueave.FiniteRepairMenu
open Uwueave.FiniteRepairMenu.Examples

example : (checkUniverse tooLargeInput).isAccepted = true := by
  decide

end Canary.Wave29.MenuBoundRefusal
