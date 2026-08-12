import FiniteHistoryDeliveryCommon

namespace Canary.Wave29.HistoryCollisionRefusal

open Uwueave Uwueave.Histories Uwueave.HistoryRuntime
open Uwueave.PersistentRuntime Uwueave.PersistentHistoryRuntime
open Canary.Wave29.FiniteHistoryDeliveryCommon

-- Same stable id, different proof-indexed version payload: replay refuses.
example : applyRecord (deliverySchema Nat LVer) causalCursor collisionEvent =
    some causalCursor := by
  decide

end Canary.Wave29.HistoryCollisionRefusal
