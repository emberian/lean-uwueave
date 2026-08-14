import Uwueave.RepairMenu

open Uwueave
open Uwueave.Repair (Promise)
open Uwueave.Exits (Exit)
open Uwueave.RepairMenu

/-- U-0130 closes only with present, typed impossibility rows carrying
universal refutations. An absent row or a single failed quota cannot inhabit
this conjunction. -/
theorem debtClosure_U_0130 :
    (∀ q : Bool → Nat,
      ¬ (Exit.escrow (S := Cost.PinSet) Bool q Exits.pinCharge).Applies
          ceilingPromise.inv)
    ∧ (∀ q : Nat → Nat,
      ¬ (Exit.escrow (S := Authority.GrantSet) Nat q Exits.grantCharge).Applies
          duelPromise.inv)
    ∧ ceilingEscrowRow.shape = Shape.impossible
    ∧ duelEscrowRow.shape = Shape.impossible
    ∧ ceilingEscrowRow ∈ ceilingMenu.rows
    ∧ duelEscrowRow ∈ duelMenu.rows
    ∧ ceilingSeamRow.shape = Shape.available
    ∧ (balanceSeamRow Nat Exits.balTotal).shape = Shape.conditional
    ∧ atMostOneSeamRow.shape = Shape.impossible := by
  exact
    ⟨ceiling_escrow_refutation_is_universal,
      duel_escrow_refutation_is_universal,
      ceilingEscrowRow_is_impossible,
      duelEscrowRow_is_impossible,
      ceilingEscrowRow_is_present,
      duelEscrowRow_is_present,
      seam_row_takes_all_three_constructors.1,
      seam_row_takes_all_three_constructors.2.1,
      seam_row_takes_all_three_constructors.2.2⟩

#print axioms debtClosure_U_0130
