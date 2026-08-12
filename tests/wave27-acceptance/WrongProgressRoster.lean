import AuthenticatedFrontierCommon

namespace Canary.Wave27.WrongProgressRoster

open Uwueave
open Canary.Wave27.AuthenticatedFrontierCommon

-- `AuthenticatedProgress` retained membership in `[7]`; it cannot be
-- re-indexed to an empty roster.
example : progress.acceptedEvent.record.issuer ∈
    ([] : List Evidence.Source) := by
  simp

end Canary.Wave27.WrongProgressRoster
