import Uwueave.WovenOperational

open Uwueave Uwueave.Wellformed Uwueave.WovenOperational

theorem debtClosure_U_0148 :
    (forall (log : DeliveryLog) (id : EditId),
      deliver (deliver log id) id = deliver log id) /\
    (forall {n root : Nat} (catalog : EditCatalog n root)
      (base : WovenDoc), WellFormed n root base ->
      forall (left right : EditHistory), Fair catalog left ->
        Fair catalog right ->
        WellFormed n root
            (deliveryView catalog base
              (runDeliveries emptyDelivery left)) /\
          WellFormed n root
            (deliveryView catalog base
              (runDeliveries emptyDelivery right)) /\
          deliveryView catalog base (runDeliveries emptyDelivery left) =
            deliveryView catalog base
              (runDeliveries emptyDelivery right)) /\
    (WellFormed 5 9
        (deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryLeft)) /\
      WellFormed 5 9
        (deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryRight)) /\
      deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryLeft) =
        deliveryView concurrentXY docX
          (runDeliveries emptyDelivery deliveryRight)) := by
  exact ⟨deliver_duplicate, fair_interleavings_preserve_and_converge,
    concurrent_delivery_fixture⟩
