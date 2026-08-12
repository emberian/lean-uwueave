import PreoAutomationSupport
import Uwueave.Preo.Elab

namespace Canary.PreoAutomation.Positive

open Uwueave Uwueave.Catalog Uwueave.Preo Uwueave.Spec
open PreoAutomationSupport

preo Built where
  field notes : GrowSet Nat
  invariant has_genesis : notes 0 = true

#assert_decl Built.State
#assert_decl Built.has_genesis
#assert_decl Built.has_genesis.verdict
#assert_decl Built.has_genesis.classification
#assert_decl Built.has_genesis.onState

end Canary.PreoAutomation.Positive
