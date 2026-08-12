import PreoAutomationSupport
import Uwueave.Tactics.Core

namespace Canary.PreoAutomation.InternalError

open Lean Elab Tactic Uwueave.Tactics.Classify

elab "force_internal_route_error" : tactic => do
  discard <| (RouteOutcome.internalError "canary route" m!"synthetic invariant failure").toBoolFor
    "acceptance"

example : True := by
  force_internal_route_error

end Canary.PreoAutomation.InternalError
