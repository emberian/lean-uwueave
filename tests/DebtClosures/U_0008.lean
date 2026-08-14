import Uwueave.EraCertificate

theorem debtClosure_U_0008 :
    Uwueave.CertificateScope.KeyCertSound
        Uwueave.EraCertificate.eraKey
        Uwueave.EraCertificate.finalView
        Uwueave.EraCertificate.Delivery
        Uwueave.EraCertificate.settledCert
      ∧ Uwueave.CertificateScope.SufficientKeyOn
        Uwueave.EraCertificate.Wf
        Uwueave.EraCertificate.eraKey
        Uwueave.EraCertificate.finalView
        Uwueave.EraCertificate.Delivery
      ∧ (¬ Uwueave.EraCertificate.Quiesced Uwueave.EraCertificate.wPre
        ∧ Uwueave.EraCertificate.Settled Uwueave.EraCertificate.wPre
        ∧ Uwueave.Evidence.FreeTermination
          Uwueave.EraCertificate.Delivery
          Uwueave.EraCertificate.finalView
          Uwueave.EraCertificate.wPre
        ∧ ¬ Uwueave.Evidence.FreeTermination
          Uwueave.EraCertificate.Delivery
          Uwueave.EraCertificate.fullView
          Uwueave.EraCertificate.wPre) := by
  exact ⟨Uwueave.EraCertificate.era_finalisation_is_a_sound_certificate,
    Uwueave.EraCertificate.eraKey_sufficient_on_wf,
    Uwueave.EraCertificate.era_stops_before_quiescence⟩
