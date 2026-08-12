import AuthenticatedEraCertificateCommon
import Uwueave.TrustFloor

namespace Canary.Wave28.PositiveAuthenticatedEraCertificate

open Uwueave Uwueave.Catalog
open Uwueave.AuthenticatedEraCertificate
open Canary.Wave28.AuthenticatedEraCertificateCommon

example : verification = Fixtures.verification := rfl

example : Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
    Authenticity.noRevocations Fixtures.progress.acceptedEvent.record :=
  verification.accepted

example : Authenticity.WasIssued Fixtures.announcementIssued
    Fixtures.progress.acceptedEvent.record :=
  verification.wasIssued

example : EraCertificate.Announcement EraCertificate.wAll EraCertificate.wAll :=
  verification.announcement

example : EraCertificate.Settled EraCertificate.wAll :=
  verification.settled

example : reusable.key = EraCertificate.eraKey EraCertificate.wAll := rfl

example : EraCertificate.settledCert reusable.key := reusable.accepts

example : CertificateScope.KeyCertSound EraCertificate.eraKey
    EraCertificate.finalView EraCertificate.Delivery reusable.Matches :=
  reusable.sound

example (user : Nat) :
    ∀ answer, EraCertificate.arriving EraCertificate.wAll user answer →
      Holes.SealsTo
        (EraCertificate.roleAnswer user EraCertificate.wAll ⊔ answer)
        ((EraCertificate.finalView EraCertificate.wAll).role user) :=
  verification.sealSurvives user

#audit_floor_prefix Uwueave.AuthenticatedEraCertificate
#audit_floor_prefix Canary.Wave28.AuthenticatedEraCertificateCommon

end Canary.Wave28.PositiveAuthenticatedEraCertificate
