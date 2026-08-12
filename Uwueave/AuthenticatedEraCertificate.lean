/-
# Uwueave.AuthenticatedEraCertificate — signed ERA cuts and scoped certificates

This leaf module joins two boundaries without collapsing them.  An
`AuthenticatedFrontier.AuthenticatedProgress` proves that one exact
domain-separated ERA event was received, accepted, genuinely issued, authored
by its signed issuer, and roster-admitted.  `CompleteAnnouncement` separately
proves that the worlds, cut, issued pool, delivered log, and frontier decoded
from that same event form a truthful and delivery-complete ERA announcement.

A signature does not prove frontier lawfulness or ERA finality.  Conversely,
the semantic completeness premise does not authenticate its source.  Only the
`Verification` conjunction yields `EraCertificate.Settled` and hence a
delivery-scoped final-view certificate.

The reusable artifact is deliberately smaller than a verification: it retains
only an ERA delivery key and proof that `settledCert` accepts that key.  It has
no signed record, signature, issuer, roster, or received-trace field.  Reuse is
licensed by exact key equality and `EraCertificate`'s existing universal
certificate theorem, not by replaying the original verification.

This module proves no cryptographic hardness and manufactures no deployed
record, trace, issuance oracle, progress message, frontier, or cut.
-/
import Uwueave.AuthenticatedFrontier
import Uwueave.EraCertificate

namespace Uwueave.AuthenticatedEraCertificate

open Uwueave Uwueave.Catalog

/-! ## Exact decoding from the signed progress event -/

/-- Decode both frontier semantics and the exact ERA announcement from one
complete signed event.  These functions are authored bindings, not hashes or
independent metadata. -/
structure EraCodec (T : Type) [Frontier.PartialOrder T]
    extends AuthenticatedFrontier.ProgressCodec Era.Event T where
  /-- Timestamp of each candidate ERA event in the decoded frontier. -/
  eventTimeOf : Era.Event → T
  /-- The exact cut announced by the signed progress event. -/
  cutOf : Era.Event → Era.Cut
  /-- ERA world immediately before the decoded announcement. -/
  beforeWorldOf : Era.Event → EraCertificate.EraWorld
  /-- ERA world immediately after the decoded announcement. -/
  afterWorldOf : Era.Event → EraCertificate.EraWorld

namespace EraCodec

/-- Canonical attributed frontier candidate.  Its source is the ERA event's
actor and its timestamp comes from the same codec as the announcement. -/
def candidate {T : Type} [Frontier.PartialOrder T] (codec : EraCodec T)
    (event : Era.Event) : AuthenticatedFrontier.CandidateEvent Era.Event T :=
  (⟨event, codec.eventTimeOf event⟩, event.actor)

end EraCodec

/-! ## Authentication and semantic completeness remain separate -/

section Bridge

variable {T : Type} [Frontier.PartialOrder T]
  {scheme : Authenticity.SignatureScheme}
  {keys : Authenticity.Keyring scheme}
  {keyRevocations : Authenticity.Revocations}
  {issued : Authenticity.Issued}
  {received : Authenticity.SignedRecord scheme → Prop}
  {roster : List Evidence.Source}
  {codec : EraCodec T}
  {progress : AuthenticatedFrontier.AuthenticatedProgress scheme keys
    keyRevocations issued received roster}

abbrev SignedEvent : Era.Event := progress.acceptedEvent.event

abbrev BeforeWorld : EraCertificate.EraWorld :=
  codec.beforeWorldOf progress.acceptedEvent.event

abbrev AfterWorld : EraCertificate.EraWorld :=
  codec.afterWorldOf progress.acceptedEvent.event

abbrev AnnouncedCut : Era.Cut := codec.cutOf progress.acceptedEvent.event

/-- The independent semantic price of interpreting the authenticated progress
event as one ERA cut announcement.  Every world/set equality is tied to the
same codec event used by the signed record.

`finalized_complete` is intentionally not derived from the signature.  It
connects ERA finalisation to the ordered frontier; the lawful advance then
proves that every such issued candidate has actually been delivered. -/
structure CompleteAnnouncement
    (advance : AuthenticatedFrontier.AuthenticatedAdvance
      codec.toProgressCodec progress) : Prop where
  announcement : EraCertificate.Announcement
    (codec.beforeWorldOf progress.acceptedEvent.event)
    (codec.afterWorldOf progress.acceptedEvent.event)
  announced_cut : codec.cutOf progress.acceptedEvent.event ∈
    (codec.afterWorldOf progress.acceptedEvent.event).cuts
  issued_exact : ∀ event,
    event ∈ (codec.afterWorldOf progress.acceptedEvent.event).pool ↔
      advance.issued (codec.candidate event) = true
  delivered_exact : ∀ event,
    event ∈ (codec.afterWorldOf progress.acceptedEvent.event).log ↔
      advance.deliveredAfter (codec.candidate event) = true
  finalized_complete : ∀ event,
    event ∈ (codec.afterWorldOf progress.acceptedEvent.event).pool →
    Era.finalized (codec.afterWorldOf progress.acceptedEvent.event).cuts event = true →
    Frontier.Settled (codec.afterOf progress.acceptedEvent.event)
      event.actor (codec.eventTimeOf event)

namespace CompleteAnnouncement

/-- Frontier delivery completeness discharges exactly ERA's settled-cut
premise once pool/log membership has been tied to the decoded world. -/
theorem settled
    {advance : AuthenticatedFrontier.AuthenticatedAdvance
      codec.toProgressCodec progress}
    (law : CompleteAnnouncement advance) :
    EraCertificate.Settled
      (codec.afterWorldOf progress.acceptedEvent.event) := by
  intro event inPool finalized
  have issuedCandidate : advance.issued (codec.candidate event) = true :=
    (law.issued_exact event).mp inPool
  have settledCandidate := law.finalized_complete event inPool finalized
  have deliveredCandidate := advance.lawful.complete_after
    (codec.candidate event) issuedCandidate settledCandidate
  exact (law.delivered_exact event).mpr deliveredCandidate

end CompleteAnnouncement

/-- Exact conjunction of authenticated issuance and the independent lawful,
complete ERA announcement.  Authentication lives in the `progress` index;
semantic completeness is the sole stored field. -/
structure Verification
    (advance : AuthenticatedFrontier.AuthenticatedAdvance
      codec.toProgressCodec progress) : Prop where
  complete : CompleteAnnouncement advance

namespace Verification

variable {advance : AuthenticatedFrontier.AuthenticatedAdvance
  codec.toProgressCodec progress}

/-- The signed record really contains the exact event decoded by every bridge
projection. -/
theorem payload_exact (_verification : Verification advance) :
    progress.acceptedEvent.record.payload =
      .event progress.acceptedEvent.event :=
  progress.acceptedEvent.payload_eq

/-- Acceptance is retained at the exact key and revocation views. -/
theorem accepted (_verification : Verification advance) :
    Authenticity.Accepted scheme keys keyRevocations
      progress.acceptedEvent.record :=
  progress.acceptedEvent.accepted

/-- Genuine issuance is retained separately from signature acceptance. -/
theorem wasIssued (_verification : Verification advance) :
    Authenticity.WasIssued issued progress.acceptedEvent.record :=
  progress.wasIssued

/-- Source identity is neither decoded from the cut tuple nor supplied as free
metadata: ERA actor, signed issuer, and authenticated source coincide. -/
theorem source_exact (_verification : Verification advance) :
    progress.acceptedEvent.event.actor =
      progress.acceptedEvent.record.issuer ∧
    progress.source = progress.acceptedEvent.record.issuer :=
  ⟨progress.source_eq_issuer, rfl⟩

/-- The exact signed issuer belongs to the exact roster indexing progress. -/
theorem issuer_mem_roster (_verification : Verification advance) :
    progress.acceptedEvent.record.issuer ∈ roster :=
  progress.issuer_mem_roster

/-- The cut projection is retained in the exact decoded after-world. -/
theorem cut_mem (verification : Verification advance) :
    codec.cutOf progress.acceptedEvent.event ∈
      (codec.afterWorldOf progress.acceptedEvent.event).cuts :=
  verification.complete.announced_cut

/-- The signed event names one exact before/after ERA announcement. -/
theorem announcement (verification : Verification advance) :
    EraCertificate.Announcement
      (codec.beforeWorldOf progress.acceptedEvent.event)
      (codec.afterWorldOf progress.acceptedEvent.event) :=
  verification.complete.announcement

/-- The independently checked frontier and world bindings establish the ERA
settled premise at the exact decoded after-world. -/
theorem settled (verification : Verification advance) :
    EraCertificate.Settled
      (codec.afterWorldOf progress.acceptedEvent.event) :=
  verification.complete.settled

/-- The exact ERA delivery key is accepted by the reusable certificate
predicate. -/
theorem settledCert (verification : Verification advance) :
    EraCertificate.settledCert
      (EraCertificate.eraKey
        (codec.afterWorldOf progress.acceptedEvent.event)) :=
  (EraCertificate.settledCert_iff _).mpr verification.settled

/-- Certificate scope is deliberately delivery only.  Announcements are the
known axis on which ERA's finalised view may change. -/
theorem deliveryScope (verification : Verification advance) :
    Evidence.FreeTermination EraCertificate.Delivery EraCertificate.finalView
      (codec.afterWorldOf progress.acceptedEvent.event) :=
  EraCertificate.era_final_view_free_terminating verification.settled

/-- The same settled after-world also carries ERA's concrete role seal: no
later delivery answer can contradict the final role selected at this cut. -/
theorem sealSurvives (verification : Verification advance) (user : Nat) :
    ∀ answer,
      EraCertificate.arriving
          (codec.afterWorldOf progress.acceptedEvent.event) user answer →
        Holes.SealsTo
          (EraCertificate.roleAnswer user
              (codec.afterWorldOf progress.acceptedEvent.event) ⊔ answer)
          ((EraCertificate.finalView
              (codec.afterWorldOf progress.acceptedEvent.event)).role user) :=
  EraCertificate.era_seal_survives verification.settled user

end Verification

end Bridge

/-! ## A reusable certificate is not its verification -/

/-- The exact key carrier used by ERA's finalisation certificate. -/
abbrev EraKey := GSet Era.Cut × GSet Era.Event × GSet Era.Event

/-- A record-free reusable certificate.  It contains only a delivery key and
the semantic acceptance proof for that key. -/
structure ReusableCertificate : Type where
  key : EraKey
  accepts : EraCertificate.settledCert key

namespace ReusableCertificate

/-- This certificate accepts exactly worlds carrying its retained ERA key. -/
def Matches (certificate : ReusableCertificate) (key : EraKey) : Prop :=
  key = certificate.key

/-- Exact-key matching makes the record-free artifact a sound reusable
delivery certificate. -/
theorem sound (certificate : ReusableCertificate) :
    CertificateScope.KeyCertSound EraCertificate.eraKey
      EraCertificate.finalView EraCertificate.Delivery certificate.Matches := by
  intro world hmatches
  apply EraCertificate.era_finalisation_is_a_sound_certificate world
  rw [hmatches]
  exact certificate.accepts

end ReusableCertificate

namespace Verification

/-- Forget the one-time authenticated verification and retain only the
record-free certificate reusable by exact ERA-key equality. -/
def toReusableCertificate
    {T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    {codec : EraCodec T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress scheme keys
      keyRevocations issued received roster}
    {advance : AuthenticatedFrontier.AuthenticatedAdvance
      codec.toProgressCodec progress}
    (verification : Verification advance) : ReusableCertificate where
  key := EraCertificate.eraKey
    (codec.afterWorldOf progress.acceptedEvent.event)
  accepts := verification.settledCert

@[simp] theorem toReusableCertificate_key
    {T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    {codec : EraCodec T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress scheme keys
      keyRevocations issued received roster}
    {advance : AuthenticatedFrontier.AuthenticatedAdvance
      codec.toProgressCodec progress}
    (verification : Verification advance) :
    verification.toReusableCertificate.key =
      EraCertificate.eraKey
        (codec.afterWorldOf progress.acceptedEvent.event) := rfl

end Verification

/-! ## Executed model fixtures and refusal boundaries -/

namespace Fixtures

/-- A toy signed inner progress event.  Its outer signature domain remains
`Payload.event`; kind `6` is the reserved inner progress discriminator. -/
def announcementEvent : Era.Event :=
  ⟨1, AuthenticatedFrontier.progressKind, 7, 1, 0⟩

def announcementIssued : Authenticity.Issued :=
  fun issuer epoch payload =>
    issuer = 7 ∧ epoch = 1 ∧ payload = .event announcementEvent

def announcementRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 7 1
    (.event announcementEvent)

def announcementReceived : Authenticity.SignedRecord Authenticity.toyScheme → Prop :=
  fun record => record = announcementRecord

theorem announcementRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations announcementRecord := by
  apply Authenticity.signRecord_accepted
  · simp [Authenticity.toyKeys]
  · rfl

theorem announcement_trace_authentic :
    Authenticity.AuthenticIssuer Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations announcementIssued announcementReceived := by
  intro record received _
  subst record
  exact ⟨rfl, rfl, rfl⟩

def acceptedAnnouncement : AuthenticatedAdmission.AcceptedEvent
    Authenticity.toyScheme Authenticity.toyKeys Authenticity.noRevocations :=
  ⟨announcementRecord, announcementEvent, rfl, announcementRecord_accepted⟩

abbrev roster : List Evidence.Source := [7]

def progress : AuthenticatedFrontier.AuthenticatedProgress
    Authenticity.toyScheme Authenticity.toyKeys Authenticity.noRevocations
      announcementIssued announcementReceived roster :=
  AuthenticatedFrontier.AuthenticatedProgress.ofAuthenticIssuer
    acceptedAnnouncement rfl announcement_trace_authentic rfl rfl
      (by simp [roster, acceptedAnnouncement, announcementRecord,
        Authenticity.signRecord])

/-- Exact finite encoding of ERA list membership into attributed candidates.
The timestamp and source equalities prevent malformed candidates from entering
the set merely because their event payload appears in the list. -/
def candidates (events : List Era.Event) :
    GSet (AuthenticatedFrontier.CandidateEvent Era.Event Nat) :=
  fun candidate => decide (
    candidate.1.value ∈ events ∧
    candidate.1.timestamp = 0 ∧
    candidate.2 = candidate.1.value.actor)

/-- The positive fixture uses the quiesced ERA world, so an empty frontier is
truthful: every issued candidate is already delivered. -/
def codec : EraCodec Nat where
  timeOf := fun _ => 0
  beforeOf := fun _ => Frontier.empty (Frontier.Point Nat)
  afterOf := fun _ => Frontier.empty (Frontier.Point Nat)
  issuedOf := fun _ => candidates EraCertificate.wAll.pool
  deliveredBeforeOf := fun _ => candidates EraCertificate.wAll.log
  deliveredAfterOf := fun _ => candidates EraCertificate.wAll.log
  eventTimeOf := fun _ => 0
  cutOf := fun event => (event.target, event.eid)
  beforeWorldOf := fun _ => EraCertificate.wAll
  afterWorldOf := fun _ => EraCertificate.wAll

def advance : AuthenticatedFrontier.AuthenticatedAdvance
    codec.toProgressCodec progress where
  source_settled := Frontier.complete_empty _
  lawful := {
    delivered_mono := leq_refl _
    frontier_advance := Frontier.advances_refl _
    complete_after := by
      intro candidate issued _
      exact issued }

def complete : CompleteAnnouncement advance where
  announcement := EraCertificate.delivery_is_announcement
    (EraCertificate.delivery_refl (by decide))
  announced_cut := by decide
  issued_exact := by
    intro event
    simp [AuthenticatedFrontier.AuthenticatedAdvance.issued, codec,
      EraCodec.candidate, candidates]
  delivered_exact := by
    intro event
    simp [AuthenticatedFrontier.AuthenticatedAdvance.deliveredAfter, codec,
      EraCodec.candidate, candidates]
  finalized_complete := by
    intro event inPool finalized
    exact Frontier.complete_empty _

def verification : Verification advance := ⟨complete⟩

def reusable : ReusableCertificate := verification.toReusableCertificate

/-- Positive whole-row acceptance: authentication, genuine issuance, exact
source/roster/cut/world binding, semantic settlement, and delivery scope all
refer to the same signed event. -/
theorem verified_row :
    Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
        Authenticity.noRevocations progress.acceptedEvent.record
      ∧ Authenticity.WasIssued announcementIssued progress.acceptedEvent.record
      ∧ progress.acceptedEvent.event.actor =
          progress.acceptedEvent.record.issuer
      ∧ progress.acceptedEvent.record.issuer ∈ roster
      ∧ codec.cutOf progress.acceptedEvent.event ∈
          (codec.afterWorldOf progress.acceptedEvent.event).cuts
      ∧ EraCertificate.Announcement
          (codec.beforeWorldOf progress.acceptedEvent.event)
          (codec.afterWorldOf progress.acceptedEvent.event)
      ∧ EraCertificate.Settled
          (codec.afterWorldOf progress.acceptedEvent.event)
      ∧ EraCertificate.settledCert reusable.key
      ∧ Evidence.FreeTermination EraCertificate.Delivery
          EraCertificate.finalView
          (codec.afterWorldOf progress.acceptedEvent.event) :=
  ⟨verification.accepted, verification.wasIssued,
    verification.source_exact.1, verification.issuer_mem_roster,
    verification.cut_mem, verification.announcement, verification.settled,
    reusable.accepts, verification.deliveryScope⟩

/-- The reserved progress domain refuses every ordinary ERA group/lifecycle
kind; in particular the signed announcement is not an ordinary join event. -/
theorem signed_progress_is_not_ordinary :
    progress.acceptedEvent.event.kind ≠ 0 ∧
      progress.acceptedEvent.event.kind ≠ 1 ∧
      progress.acceptedEvent.event.kind ≠ 2 ∧
      progress.acceptedEvent.event.kind ≠ 3 ∧
      progress.acceptedEvent.event.kind ≠ 4 :=
  progress.refuses_ordinary_kind

/-! ### Accepted is not issued -/

def unissuedEvent : Era.Event :=
  ⟨2, AuthenticatedFrontier.progressKind, 7, 1, 0⟩

/-- The toy scheme intentionally permits constructing another accepting
signature.  The issuance transcript still refuses its exact payload. -/
def unissuedRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 7 1 (.event unissuedEvent)

theorem unissuedRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations unissuedRecord := by
  apply Authenticity.signRecord_accepted
  · simp [Authenticity.toyKeys]
  · rfl

theorem unissuedRecord_not_issued :
    ¬ Authenticity.WasIssued announcementIssued unissuedRecord := by
  simp [Authenticity.WasIssued, announcementIssued, unissuedRecord,
    announcementEvent, unissuedEvent, Authenticity.signRecord]

def attackReceived : Authenticity.SignedRecord Authenticity.toyScheme → Prop :=
  fun record => record = announcementRecord ∨ record = unissuedRecord

/-- Signature acceptance alone cannot inhabit authenticated progress for an
unissued record: the retained `wasIssued` field exposes the contradiction. -/
theorem accepted_unissued_cannot_be_progress :
    ¬ ∃ forged : AuthenticatedFrontier.AuthenticatedProgress
        Authenticity.toyScheme Authenticity.toyKeys
          Authenticity.noRevocations announcementIssued attackReceived roster,
      forged.acceptedEvent.record = unissuedRecord := by
  rintro ⟨forged, exact⟩
  apply unissuedRecord_not_issued
  simpa only [exact] using forged.wasIssued

/-! ### Authentication is not cut completeness -/

/-- The same signed event can be decoded toward an ERA world whose finalised
pool is incomplete.  Authentication remains unchanged; only the independent
semantic world decoder differs. -/
def incompleteCodec : EraCodec Nat :=
  { codec with afterWorldOf := fun _ => EraCertificate.wAhead }

/-- No `CompleteAnnouncement` can be manufactured for that decoder.  If one
existed, the generic bridge would prove the concretely false ERA `Settled`
predicate at `wAhead`. -/
theorem authentication_does_not_manufacture_complete_cut :
    ¬ CompleteAnnouncement (codec := incompleteCodec) (progress := progress)
      advance := by
  intro claimed
  have settled := claimed.settled
  exact (by decide : ¬ EraCertificate.Settled EraCertificate.wAhead) settled

/-- Reuse is now independent of the original signature record: the record-free
artifact is sound for every world carrying its exact ERA key. -/
theorem reusable_is_delivery_scoped :
    CertificateScope.KeyCertSound EraCertificate.eraKey
      EraCertificate.finalView EraCertificate.Delivery reusable.Matches :=
  reusable.sound

/-- The verified after-world's user-level ERA seal is tied to the same decoded
world as its cut, settled certificate, and delivery scope. -/
theorem verified_world_seal (user : Nat) :
    ∀ answer, EraCertificate.arriving EraCertificate.wAll user answer →
      Holes.SealsTo
        (EraCertificate.roleAnswer user EraCertificate.wAll ⊔ answer)
        ((EraCertificate.finalView EraCertificate.wAll).role user) :=
  verification.sealSurvives user

end Fixtures

end Uwueave.AuthenticatedEraCertificate
