import AuthenticatedFrontierCommon

namespace Canary.Wave27.WrongProgressOrigin

open Uwueave
open Canary.Wave27.AuthenticatedFrontierCommon

-- The signed issuer/source is exactly 7; unsigned caller metadata cannot
-- relabel it as source 8.
example : progress.acceptedEvent.event.actor = 8 := by
  decide

end Canary.Wave27.WrongProgressOrigin
