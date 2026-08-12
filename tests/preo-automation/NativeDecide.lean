import PreoAutomationSupport
import Uwueave.Preo.Elab

namespace Canary.PreoAutomation.NativeDecide

open Uwueave Uwueave.Catalog Uwueave.Preo Uwueave.Spec

theorem compiledTruth : True := by
  native_decide

def badVerdict : Verdict (fun s : GSet Nat => s 0 = true) :=
  .free ((fun _ : True => Uwueave.Catalog.gset_mem_iconfluent 0) compiledTruth)

preo Rejected where
  field notes : GrowSet Nat
  invariant has_genesis : notes 0 = true := badVerdict

end Canary.PreoAutomation.NativeDecide
