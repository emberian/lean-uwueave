import PreoAutomationSupport
import Uwueave.Tactics.Verdict

namespace Canary.PreoAutomation.NoVerdictTactic

open Uwueave Uwueave.Catalog Uwueave.Spec

example : Verdict (S := GSet Nat) (fun s => s 0 = s 1) := by
  verdict using ([] : List (GSet Nat))

end Canary.PreoAutomation.NoVerdictTactic
