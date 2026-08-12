import RuntimeAuthV4Common

namespace Canary.Wave27.WrongV4Capability

open Uwueave
open Canary.Wave27.RuntimeAuthV4Common

def deny (_ : Uwueave.RuntimeAuthV4.SignedRequest) : Prop := False

example : Uwueave.RuntimeAuthV4.ReadyForExecution verification resolver
    deny allow [] request := by
  refine
    { verified := ready.verified
      resolved := ready.resolved
      fresh := ready.fresh
      authorized := ?_
      isMember := trivial }
  exact trivial

end Canary.Wave27.WrongV4Capability
