import FiniteHistoryDeliveryCommon
import Uwueave.TrustFloor

namespace Canary.Wave29.PositiveFiniteHistoryDelivery

open Uwueave Uwueave.Histories Uwueave.HistoryRuntime
open Uwueave.PersistentRuntime
open Uwueave.FiniteHistoryDelivery
open Canary.Wave29.FiniteHistoryDeliveryCommon

example (version : LVer) :
    HistoryPolicy.viewOf HistoryPolicy.lvExplicit lockHistory version =
      lockHistory.state version :=
  growth.view_eq_state version

example : causalDelivery.cursor.accepted = events := rfl
example : reverseDelivery.cursor.accepted = reverseEvents := rfl
example : causalDelivery.cursor.state.pending = [] := causalDelivery.settled
example : reverseDelivery.cursor.state.pending = [] := reverseDelivery.settled

example : SameEventSet causalCursor.state.materialized
    reverseCursor.state.materialized :=
  causalDelivery.sameEventSet reverseDelivery

example : eventSetView causalCursor.state.materialized =
    eventSetView reverseCursor.state.materialized :=
  causalDelivery.eventSetView_eq reverseDelivery

example : applyRecord (PersistentHistoryRuntime.deliverySchema Nat LVer)
    causalCursor joinEvent = some causalCursor := duplicate_retry

#audit_floor_prefix Uwueave.FiniteHistoryDelivery
#audit_floor_prefix Canary.Wave29.FiniteHistoryDeliveryCommon

end Canary.Wave29.PositiveFiniteHistoryDelivery
