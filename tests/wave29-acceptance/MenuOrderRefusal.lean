import Uwueave.FiniteRepairMenu

namespace Canary.Wave29.MenuOrderRefusal

open Uwueave Uwueave.FiniteRepairMenu
open Uwueave.FiniteRepairMenu.Examples

example : (checkUniverse nonCanonicalInput).isAccepted = true := by
  decide

end Canary.Wave29.MenuOrderRefusal
