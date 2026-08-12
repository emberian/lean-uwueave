import AuthenticatedFrontierCommon

namespace Canary.Wave27.StaleFrontier

open Uwueave

-- A frontier with no open point cannot move backward to reopen source 7 at
-- time 0.  An authenticated event does not manufacture this order premise.
example : Frontier.AdvancesTo (Frontier.empty (Frontier.Point Nat))
    (Frontier.singleton ⟨7, 0⟩) := by
  intro time covered
  exact covered

end Canary.Wave27.StaleFrontier
