import PreoAutomationSupport
import Uwueave.Preo.Elab

namespace Canary.PreoAutomation.NoVerdict

open Uwueave Uwueave.Preo Uwueave.Spec
open PreoAutomationSupport

preo Silent where
  field notes : GrowSet Nat
  invariant equal_bits : notes 0 = notes 1

#assert_decl Silent.State
#assert_decl Silent.equal_bits
#assert_decl Silent.equal_bits.obligation
#assert_decl Silent.equal_bits.classification
#assert_no_decl Silent.equal_bits.verdict
#assert_no_decl Silent.equal_bits.onState

example : Silent.equal_bits.classification.answer = none := rfl

end Canary.PreoAutomation.NoVerdict
