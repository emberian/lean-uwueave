import PreoAutomationSupport
import Uwueave.Tactics.Core

namespace Canary.PreoAutomation.AutomaticCapClassify

open Uwueave Uwueave.Catalog

example : IConfluent (S := GSet (Fin 7)) (fun s => s 0 = s 1) := by
  classify

end Canary.PreoAutomation.AutomaticCapClassify
