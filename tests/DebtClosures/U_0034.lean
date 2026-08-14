import Uwueave.FiniteCertificateClassifier
import Uwueave.BoundedEraAnnouncement

open Uwueave

universe uW uR uK

/-! Mixed-universe compile canaries for the formerly fixed carrier chain. -/
#check Holes.Partial Type
#check Evidence.FreeTermination (S := Nat) (β := Type)
#check Evidence.FreeTermination (S := Type) (β := Nat)
#check WorldFuture.World Type

theorem debtClosure_U_0034 :
    (∀ {W : Type uW} {R : Type uR} (future : Evidence.Future W)
        (eval : W → R) (world : W),
      Evidence.FreeTermination future eval world ↔
        Holes.SealsTo
          (CertificateScope.residualSet eval future world) (eval world))
      ∧ (∀ {W : Type uW} {R : Type uR} {K : Type uK}
        {key : W → K} {eval : W → R} {future : W → W → Prop}
        (_sufficient : CertificateScope.SufficientKey key eval future)
        {source target : W} (_sameKey : key source = key target)
        (_targetRefl : future target target)
        (_sourceStable : Evidence.FreeTermination future eval source),
      Evidence.FreeTermination future eval target)
      ∧ (∀ {W : Type uW} {R : Type uR} [BEq R] [LawfulBEq R]
        (spec : FiniteCertificateClassifier.Spec W R)
        {K : Type uK} [BEq K] [LawfulBEq K] (key : W → K),
      spec.sufficientB key = true ↔ spec.SufficientKeyWithin key)
      ∧ (∀ {W : Type uW} {R : Type uR}
        (spec : FiniteCertificateClassifier.Spec W R)
        {K : Type uK} (key : W → K)
        (_coverage : spec.CoversOrigins)
        (_within : spec.SufficientKeyWithin key),
      CertificateScope.SufficientKey key spec.eval spec.future)
      ∧ (∀ {available : List Era.Cut}
        {world : EraCertificate.EraWorld} (_wf : EraCertificate.Wf world),
      BoundedEraAnnouncement.traceStableB available world = true ↔
        Evidence.FreeTermination
          (BoundedEraAnnouncement.AnnouncementWithin available)
          BoundedEraAnnouncement.finalTrace world)
      ∧ (∀ {world : EraCertificate.EraWorld}
        (_wf : EraCertificate.Wf world) (available : List Era.Cut),
      ¬ BoundedEraAnnouncement.CoversUnrestricted available world) := by
  exact ⟨CertificateScope.freeTermination_iff_sealsTo_residualSet,
    CertificateScope.key_licenses_reuse,
    FiniteCertificateClassifier.sufficientB_eq_true_iff,
    FiniteCertificateClassifier.sufficientKey_of_within_of_coverage,
    BoundedEraAnnouncement.traceStableB_iff_freeTermination,
    BoundedEraAnnouncement.no_finite_pool_covers_unrestricted⟩
