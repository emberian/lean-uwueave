import Uwueave.EraCertificate

open Uwueave

universe u

theorem debtClosure_U_0012 :
    (∀ {α : Type u} (w : WorldFuture.World α),
      Holes.Stable (CertificateScope.arriving w)
          (Evidence.values (WorldFuture.observe w)) ↔
        Evidence.FreeTermination WorldFuture.DeliveryFuture
          (fun next => Evidence.values (WorldFuture.observe next)) w) ∧
    (∀ {w : EraCertificate.EraWorld} (_hs : EraCertificate.Settled w) (u : Nat),
      Holes.Stable (EraCertificate.arriving w u)
        (EraCertificate.roleAnswer u w)) ∧
    (∀ {w : EraCertificate.EraWorld} (_hs : EraCertificate.Settled w) (u : Nat),
      ∀ Q, EraCertificate.arriving w u Q →
        Holes.SealsTo (EraCertificate.roleAnswer u w ⊔ Q)
          ((EraCertificate.finalView w).role u)) := by
  exact ⟨CertificateScope.stable_iff_freeTermination_values,
    EraCertificate.era_cut_licenses_the_collapse,
    EraCertificate.era_seal_survives⟩
