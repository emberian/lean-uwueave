import Uwueave.Repair

open Uwueave
open Uwueave.Repair

/-- U-0122 closes over an explicit finite shared-strategy space and an explicit
caller valuation. The minimum is achieved by one full `Price`; it is not a
componentwise fiction assembled from independently chosen strategies. -/
theorem debtClosure_U_0122 :
    (∀ (Strategy : Type) (space : CoordEffect.Admissible Strategy)
        (valuation : Price → Nat)
        (left right : RepairPriceProfile Strategy),
      ∃ strategy ∈ space.toList,
        RepairPriceProfile.close space valuation
            (RepairPriceProfile.comp left right) =
          valuation (Price.add (left strategy) (right strategy))
        ∧ ∀ other ∈ space.toList,
            valuation (Price.add (left strategy) (right strategy)) ≤
              valuation (Price.add (left other) (right other)))
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
    ⟨fun _ space valuation left right =>
      RepairPriceProfile.comp_close_is_least_achievable
        space valuation left right,
      RepairPriceProfile.shared_strategy_price_exact,
      RepairPriceProfile.shared_strategy_price_strictness⟩

#print axioms debtClosure_U_0122
