import Uwueave.AuthenticatedWorldContext

namespace Canary.Wave27.StaleWorldVersion

open Uwueave
open Uwueave.AuthenticatedWorldContext

example : Nonempty (ContextualPositionClaim exactPositionClaim
    alternateConsumption usedDelegate positionHolder) := by
  exact stale_base_refuses_position

end Canary.Wave27.StaleWorldVersion
