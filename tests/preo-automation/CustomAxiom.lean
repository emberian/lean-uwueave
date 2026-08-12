import PreoAutomationSupport
import Uwueave.Preo.Elab

namespace Canary.PreoAutomation.CustomAxiom

open Uwueave Uwueave.Catalog Uwueave.Preo Uwueave.Spec

axiom unsound : False

def badVerdict : Verdict (fun s : GSet Nat => s 0 = true) :=
  .free (False.elim unsound)

preo Rejected where
  field notes : GrowSet Nat
  invariant has_genesis : notes 0 = true := badVerdict

end Canary.PreoAutomation.CustomAxiom
