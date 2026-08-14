import Uwueave.Repair

open Uwueave
open Uwueave.Repair

/-- U-0126 keeps `Price.add` in its honest role: accumulating two bills at one
fixed strategy. The true session minimum is the achieved close of the composed
profile, and the strict fixture refutes sum-of-independent-minima. -/
theorem debtClosure_U_0126 :
    (∀ (Strategy : Type) (left right : RepairPriceProfile Strategy)
        (strategy : Strategy),
      RepairPriceProfile.comp left right strategy =
        Price.add (left strategy) (right strategy))
    ∧ (∀ {P Q R : Promise} (first : Repair P Q) (second : Repair Q R),
      (first.comp second).price = Price.add first.price second.price)
    ∧ ((RepairPriceProfile.close CoordEffect.pinSpace
          RepairPriceProfile.seamCrossingValuation
          RepairPriceProfile.pinTruePriceProfile = 0
        ∧ RepairPriceProfile.close CoordEffect.pinSpace
          RepairPriceProfile.seamCrossingValuation
          RepairPriceProfile.pinFalsePriceProfile = 0)
      ∧ RepairPriceProfile.close CoordEffect.pinSpace
          RepairPriceProfile.seamCrossingValuation
          (RepairPriceProfile.comp RepairPriceProfile.pinTruePriceProfile
            RepairPriceProfile.pinFalsePriceProfile) = 1)
    ∧ RepairPriceProfile.close CoordEffect.pinSpace
          RepairPriceProfile.seamCrossingValuation
          RepairPriceProfile.pinTruePriceProfile
        + RepairPriceProfile.close CoordEffect.pinSpace
          RepairPriceProfile.seamCrossingValuation
          RepairPriceProfile.pinFalsePriceProfile
      < RepairPriceProfile.close CoordEffect.pinSpace
          RepairPriceProfile.seamCrossingValuation
          (RepairPriceProfile.comp RepairPriceProfile.pinTruePriceProfile
            RepairPriceProfile.pinFalsePriceProfile) := by
  exact
    ⟨fun _ left right strategy =>
      RepairPriceProfile.comp_apply left right strategy,
      Repair.comp_price,
      RepairPriceProfile.shared_strategy_price_exact,
      RepairPriceProfile.shared_strategy_price_strictness⟩

#print axioms debtClosure_U_0126
