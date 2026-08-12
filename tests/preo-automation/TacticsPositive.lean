import PreoAutomationSupport
import Uwueave.Tactics.Verdict

namespace Canary.PreoAutomation.TacticsPositive

open Uwueave Uwueave.Catalog Uwueave.Spec Uwueave.Tactics
open PreoAutomationSupport

/-! Automatic finite classification is allowed exactly at the 64-state cap. -/
set_option maxRecDepth 10000 in
example : IConfluent (S := GSet (Fin 6)) (fun s => s 0 = s 1) := by
  classify

set_option maxRecDepth 10000 in
example : Verdict (S := GSet (Fin 6)) (fun s => s 0 = s 1) := by
  verdict

/-! The explicit value-level route is deliberately uncapped. -/
def explicit128 : Verdict (S := GSet (Fin 7)) (fun s => s 0 = s 1) :=
  classifyFinite (fun s : GSet (Fin 7) => s 0 = s 1)

#assert_decl explicit128

end Canary.PreoAutomation.TacticsPositive
