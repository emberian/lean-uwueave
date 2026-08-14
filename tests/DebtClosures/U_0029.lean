import Uwueave.EraCertificate

theorem debtClosure_U_0029 :
    Uwueave.CertificateScope.KeyCertSound
        Uwueave.EraCertificate.eraKey
        Uwueave.EraCertificate.finalView
        Uwueave.EraCertificate.Delivery
        Uwueave.EraCertificate.settledCert
      ∧ Uwueave.CertificateScope.SufficientKeyOn
        Uwueave.EraCertificate.Wf
        Uwueave.EraCertificate.eraKey
        Uwueave.EraCertificate.finalView
        Uwueave.EraCertificate.Delivery := by
  exact ⟨Uwueave.EraCertificate.era_finalisation_is_a_sound_certificate,
    Uwueave.EraCertificate.eraKey_sufficient_on_wf⟩
