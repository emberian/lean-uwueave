import FiniteHistoryDeliveryCommon

namespace Canary.Wave29.HistorySelfParentRefusal

open Uwueave Uwueave.Histories Uwueave.HistoryRuntime
open Uwueave.PersistentRuntime Uwueave.PersistentHistoryRuntime
open Canary.Wave29.FiniteHistoryDeliveryCommon

example : applyRecord (deliverySchema Nat LVer) causalCursor selfParentEvent =
    some causalCursor := by
  decide

end Canary.Wave29.HistorySelfParentRefusal
