import Uwueave.AuthenticatedWorldContext

namespace Canary.Wave27.WrongCausalOrigin

open Uwueave
open Uwueave.AuthenticatedWorldContext

example : Nonempty (ContextualPositionClaim exactPositionClaim
    wrongOriginConsumption usedDelegate positionHolder) := by
  exact wrong_origin_refuses_position

end Canary.Wave27.WrongCausalOrigin
