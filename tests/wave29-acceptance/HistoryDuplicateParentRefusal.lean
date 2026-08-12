import FiniteHistoryDeliveryCommon

namespace Canary.Wave29.HistoryDuplicateParentRefusal

open Uwueave Uwueave.Histories Uwueave.HistoryRuntime
open Uwueave.PersistentRuntime Uwueave.PersistentHistoryRuntime
open Canary.Wave29.FiniteHistoryDeliveryCommon

example : applyRecord (deliverySchema Nat LVer) causalCursor
    duplicateParentEvent = some causalCursor := by
  decide

end Canary.Wave29.HistoryDuplicateParentRefusal
