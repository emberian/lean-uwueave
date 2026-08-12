import AuthenticatedFrontierCommon

namespace Canary.Wave27.OrdinaryEventIsNotProgress

open Uwueave
open Canary.Wave27.AuthenticatedFrontierCommon

-- The progress domain is reserved kind 6, disjoint from ordinary kind 1.
example : progress.acceptedEvent.event.kind = 1 := by
  decide

end Canary.Wave27.OrdinaryEventIsNotProgress
