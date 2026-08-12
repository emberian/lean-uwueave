import PreoAutomationSupport
import Uwueave.Preo.Elab

namespace Canary.PreoAutomation.Sorry

open Uwueave Uwueave.Catalog Uwueave.Preo Uwueave.Spec

def badVerdict : Verdict (fun s : GSet Nat => s 0 = true) := by
  sorry

preo Rejected where
  field notes : GrowSet Nat
  invariant has_genesis : notes 0 = true := badVerdict

end Canary.PreoAutomation.Sorry
