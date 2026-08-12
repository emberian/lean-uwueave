import PreoAutomationSupport
import Uwueave.Tactics.Core

namespace Canary.PreoAutomation.PoolCap

open Uwueave Uwueave.Catalog

example : ¬ IConfluent (S := GSet Nat) (fun _ => True) := by
  classify using (List.replicate 65 (fun _ => false))

end Canary.PreoAutomation.PoolCap
