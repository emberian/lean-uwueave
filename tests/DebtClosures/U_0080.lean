import Uwueave.EraCertificate

open Uwueave

theorem debtClosure_U_0080 :
    (∀ {w : EraCertificate.EraWorld} (_hs : EraCertificate.Settled w) (u : Nat),
      Holes.Stable (EraCertificate.arriving w u) (EraCertificate.roleAnswer u w)) ∧
    (∀ {w : EraCertificate.EraWorld} (_hs : EraCertificate.Settled w) (u : Nat),
      ∀ Q, EraCertificate.arriving w u Q →
        Holes.SealsTo (EraCertificate.roleAnswer u w ⊔ Q)
          ((EraCertificate.finalView w).role u)) ∧
    (¬ Holes.Stable
      (EraCertificate.arrivingCut EraCertificate.wAll Era.alice)
      (EraCertificate.roleAnswer Era.alice EraCertificate.wAll)) ∧
    (¬ Holes.SealsTo
      (EraCertificate.roleAnswer Era.alice EraCertificate.wAll ⊔
        EraCertificate.roleAnswer Era.alice EraCertificate.wAheadAll)
      Era.admin) := by
  exact ⟨EraCertificate.era_cut_licenses_the_collapse,
    EraCertificate.era_seal_survives,
    EraCertificate.the_cut_axis_breaks_the_seal,
    EraCertificate.the_unlicensed_collapse_is_a_lie⟩
