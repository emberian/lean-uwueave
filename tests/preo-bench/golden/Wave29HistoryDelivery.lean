import Bench.Wave29HistoryDeliveryFixture

namespace PreoBench.Golden.Wave29HistoryDelivery

open Uwueave.HistoryRuntime Uwueave.PersistentRuntime
open Uwueave.PersistentHistoryRuntime
open PreoBench.Wave29.HistoryDeliveryFixture

def causalArrivalIds : List Nat := causalDelivery.arrivals.map Event.id
def reverseArrivalIds : List Nat := reverseDelivery.arrivals.map Event.id
def causalMaterializedIds : List Nat :=
  causalDelivery.cursor.state.materialized.accepted.map Event.id
def reverseMaterializedIds : List Nat :=
  reverseDelivery.cursor.state.materialized.accepted.map Event.id

def retryAccepted : Bool := decide
  (applyRecord (deliverySchema Nat Uwueave.Histories.LVer)
    causalCursor joinEvent = some causalCursor)

def refusalOutputs : List Bool :=
  [ decide (applyRecord (deliverySchema Nat Uwueave.Histories.LVer)
      causalCursor forgedJoin = none),
    decide (applyRecord (deliverySchema Nat Uwueave.Histories.LVer)
      (emptyDeliveryCursor Nat Uwueave.Histories.LVer 0) joinEvent = none) ]

#guard causalArrivalIds = [0, 1, 2, 3, 4, 5]
#guard reverseArrivalIds = [5, 4, 3, 2, 1, 0]
#guard causalMaterializedIds = [0, 1, 2, 3, 4, 5]
#guard reverseMaterializedIds = [0, 2, 1, 4, 3, 5]
#guard retryAccepted
#guard refusalOutputs = [true, true]

example : Uwueave.HistoryRuntime.eventSetView
    causalDelivery.cursor.state.materialized =
    Uwueave.HistoryRuntime.eventSetView
      reverseDelivery.cursor.state.materialized :=
  causalDelivery.eventSetView_eq reverseDelivery

#eval causalArrivalIds
#eval reverseArrivalIds
#eval causalMaterializedIds
#eval reverseMaterializedIds
#eval retryAccepted
#eval refusalOutputs

end PreoBench.Golden.Wave29HistoryDelivery
