import Uwueave.FiniteRepairMenu

namespace Canary.Wave29.WrongFullPrice

open Uwueave Uwueave.FiniteRepairMenu
open Uwueave.FiniteRepairMenu.Examples

-- The complete eight-axis repair price is retained; it cannot be replaced by
-- the free price merely because the finite choice was ID-ordered.
example : positiveResult.price? = some Repair.Price.free := by
  decide

end Canary.Wave29.WrongFullPrice
