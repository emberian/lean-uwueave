import AuthenticatedFrontierCommon

namespace Canary.Wave27.AdvanceWithoutDelivery

open Uwueave Uwueave.Catalog

-- Advancing the frontier alone cannot claim completeness for an issued event
-- that was never delivered.
example : Frontier.DeliveryComplete Frontier.sourceZeroAtOne
    Frontier.tinyStamp Frontier.loneIssued Frontier.noneDelivered := by
  intro event issued _
  have exactEvent : event = (7, 0) := of_decide_eq_true issued
  subst event
  rfl

end Canary.Wave27.AdvanceWithoutDelivery
