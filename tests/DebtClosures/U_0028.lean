import Uwueave.EraCertificate

open Uwueave

theorem debtClosure_U_0028 :
    (∀ {world : EraCertificate.EraWorld}
        (_settled : EraCertificate.Settled world) (user : Nat),
      Holes.Stable (EraCertificate.arriving world user)
        (EraCertificate.roleAnswer user world))
      ∧ (∀ {world : EraCertificate.EraWorld}
        (_settled : EraCertificate.Settled world) (user : Nat),
      ∀ arrival, EraCertificate.arriving world user arrival →
        Holes.SealsTo (EraCertificate.roleAnswer user world ⊔ arrival)
          ((EraCertificate.finalView world).role user)) := by
  exact ⟨EraCertificate.era_cut_licenses_the_collapse,
    EraCertificate.era_seal_survives⟩
