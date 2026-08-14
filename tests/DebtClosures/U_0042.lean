import Uwueave.EraCertificate

open Uwueave

universe u

theorem debtClosure_U_0042 :
    (∀ {alpha : Type u} {s t : Evidence.ResultEvidence alpha},
      Evidence.Closed s → s ⊑ t → Evidence.Admits s t →
        Evidence.candidates t = Evidence.candidates s) ∧
    (∀ {w : EraCertificate.EraWorld}
      (_settled : EraCertificate.Settled w) (user : Nat),
      Holes.Stable (EraCertificate.arriving w user)
        (EraCertificate.roleAnswer user w)) ∧
    (∀ {w : EraCertificate.EraWorld}
      (_settled : EraCertificate.Settled w) (user : Nat),
      ∀ arrivingAnswer,
        EraCertificate.arriving w user arrivingAnswer →
        Holes.SealsTo
          (EraCertificate.roleAnswer user w ⊔ arrivingAnswer)
          ((EraCertificate.finalView w).role user)) := by
  exact ⟨Evidence.closed_freezes,
    EraCertificate.era_cut_licenses_the_collapse,
    EraCertificate.era_seal_survives⟩
