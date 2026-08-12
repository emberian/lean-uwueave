import PreoAutomationSupport
import Uwueave.Tactics.Verdict

namespace Canary.PreoAutomation.AutomaticCapVerdict

open Uwueave Uwueave.Catalog Uwueave.Spec

example : Verdict (S := GSet (Fin 7)) (fun s => s 0 = s 1) := by
  verdict

end Canary.PreoAutomation.AutomaticCapVerdict
