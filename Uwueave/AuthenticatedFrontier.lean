/-
# Uwueave.AuthenticatedFrontier — authenticated, lawful frontier progress.

This module deliberately separates two obligations.  Authentication proves
who issued an exact signed ERA event; `Frontier.DeliveryAdvance` proves that
the frontier named by that event is a truthful delivery-complete advance.
Neither fact manufactures the other, a deployed signature scheme, an issuance
log, or a received network trace.

Progress uses a reserved *inner* `Era.Event.kind`.  The outer signed payload is
still `Authenticity.Payload.event`; this file does not pretend Authenticity has
a fourth outer payload domain.  A caller supplies the semantic decoder from
the complete signed event to its timestamp, two frontiers, issued pool, and
old/new delivered pools.
-/
import Uwueave.AuthenticatedAdmission
import Uwueave.Frontier

namespace Uwueave.AuthenticatedFrontier

open Uwueave Uwueave.Catalog

/-- Reserved inner ERA event kind for frontier-progress claims. -/
def progressKind : Nat := 6

/-- Progress is disjoint from ERA's ordinary group/lifecycle kinds `0..4`. -/
theorem progressKind_not_ordinary :
    progressKind ≠ 0 ∧ progressKind ≠ 1 ∧ progressKind ≠ 2 ∧
      progressKind ≠ 3 ∧ progressKind ≠ 4 := by
  decide

/-- Progress is also disjoint from the authenticated-context position kind. -/
theorem progressKind_ne_positionKind : progressKind ≠ 5 := by
  decide

/-- A timestamp travels with the candidate value.  Its attributed source is
the second component of `CandidateEvent`, exactly the shape consumed by
`Frontier.DeliveryAdvance`. -/
structure TimestampedCandidate (alpha T : Type) where
  value : alpha
  timestamp : T

/-- The exact attributed event carrier checked by a frontier advance. -/
abbrev CandidateEvent (alpha T : Type) :=
  TimestampedCandidate alpha T × Evidence.Source

/-- The timestamp is a projection from the candidate carrier, not caller
metadata threaded separately through the advance theorem. -/
def candidateStamp {alpha T : Type} (candidate : CandidateEvent alpha T) : T :=
  candidate.1.timestamp

/-- Semantic decoding of a complete signed progress event.  This is an
authored binding codec, not a cryptographic digest or an observation claim. -/
structure ProgressCodec (alpha T : Type) [Frontier.PartialOrder T] where
  timeOf : Era.Event → T
  beforeOf : Era.Event → Frontier.SourceFrontier T
  afterOf : Era.Event → Frontier.SourceFrontier T
  issuedOf : Era.Event → GSet (CandidateEvent alpha T)
  deliveredBeforeOf : Era.Event → GSet (CandidateEvent alpha T)
  deliveredAfterOf : Era.Event → GSet (CandidateEvent alpha T)

/-- An accepted progress event with trace membership and genuine issuance.
`Accepted` alone is intentionally insufficient. -/
structure AuthenticatedProgress
    (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop)
    (roster : List Evidence.Source) where
  acceptedEvent : AuthenticatedAdmission.AcceptedEvent
    scheme keys keyRevocations
  received_exact : received acceptedEvent.record
  wasIssued : Authenticity.WasIssued issued acceptedEvent.record
  progress_domain : acceptedEvent.event.kind = progressKind
  source_eq_issuer : acceptedEvent.event.actor = acceptedEvent.record.issuer
  issuer_mem_roster : acceptedEvent.record.issuer ∈ roster

namespace AuthenticatedProgress

/-- The only constructor transport that derives genuine issuance: caller
supplies exact trace membership and issuer authenticity for that trace. -/
def ofAuthenticIssuer
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    (acceptedEvent : AuthenticatedAdmission.AcceptedEvent
      scheme keys keyRevocations)
    (received_exact : received acceptedEvent.record)
    (authentic : Authenticity.AuthenticIssuer scheme keys keyRevocations
      issued received)
    (progress_domain : acceptedEvent.event.kind = progressKind)
    (source_eq_issuer : acceptedEvent.event.actor = acceptedEvent.record.issuer)
    (issuer_mem_roster : acceptedEvent.record.issuer ∈ roster) :
    AuthenticatedProgress scheme keys keyRevocations issued received roster :=
  {
    acceptedEvent
    received_exact
    wasIssued := authentic acceptedEvent.record received_exact
      acceptedEvent.accepted
    progress_domain
    source_eq_issuer
    issuer_mem_roster
  }

/-- The signed source retained by the progress witness. -/
abbrev source
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    (progress : AuthenticatedProgress scheme keys keyRevocations issued
      received roster) : Evidence.Source :=
  progress.acceptedEvent.record.issuer

/-- Ordinary ERA/lifecycle events cannot inhabit the progress envelope. -/
theorem refuses_ordinary_kind
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    (progress : AuthenticatedProgress scheme keys keyRevocations issued
      received roster) :
    progress.acceptedEvent.event.kind ≠ 0 ∧
      progress.acceptedEvent.event.kind ≠ 1 ∧
      progress.acceptedEvent.event.kind ≠ 2 ∧
      progress.acceptedEvent.event.kind ≠ 3 ∧
      progress.acceptedEvent.event.kind ≠ 4 := by
  rw [progress.progress_domain]
  exact progressKind_not_ordinary

end AuthenticatedProgress

/-- Authentication plus the independent semantic proof of one exact frontier
transition.  The signed event is decoded definitionally into the exact old and
new frontiers and issued/delivered sets used by `lawful`; none is free metadata
on this witness. -/
structure AuthenticatedAdvance
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    (codec : ProgressCodec alpha T)
    (progress : AuthenticatedProgress scheme keys keyRevocations authIssued
      received roster) where
  source_settled : Frontier.Settled
    (codec.afterOf progress.acceptedEvent.event)
    progress.source (codec.timeOf progress.acceptedEvent.event)
  lawful : Frontier.DeliveryAdvance candidateStamp
    (codec.issuedOf progress.acceptedEvent.event)
    (codec.beforeOf progress.acceptedEvent.event)
    (codec.afterOf progress.acceptedEvent.event)
    (codec.deliveredBeforeOf progress.acceptedEvent.event)
    (codec.deliveredAfterOf progress.acceptedEvent.event)

namespace AuthenticatedAdvance

/-- The issued pool decoded from the exact signed event. -/
def issued
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    {codec : ProgressCodec alpha T}
    {progress : AuthenticatedProgress scheme keys keyRevocations authIssued
      received roster}
    (_ : AuthenticatedAdvance codec progress) :
    GSet (CandidateEvent alpha T) :=
  codec.issuedOf progress.acceptedEvent.event

/-- The old delivered set decoded from the exact signed event. -/
def deliveredBefore
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    {codec : ProgressCodec alpha T}
    {progress : AuthenticatedProgress scheme keys keyRevocations authIssued
      received roster}
    (_ : AuthenticatedAdvance codec progress) :
    GSet (CandidateEvent alpha T) :=
  codec.deliveredBeforeOf progress.acceptedEvent.event

/-- The new delivered set decoded from the exact signed event. -/
def deliveredAfter
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    {codec : ProgressCodec alpha T}
    {progress : AuthenticatedProgress scheme keys keyRevocations authIssued
      received roster}
    (_ : AuthenticatedAdvance codec progress) :
    GSet (CandidateEvent alpha T) :=
  codec.deliveredAfterOf progress.acceptedEvent.event

/-- Forget authentication and recover the exact lawful delivery advance. -/
theorem toDeliveryAdvance
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    {codec : ProgressCodec alpha T}
    {progress : AuthenticatedProgress scheme keys keyRevocations authIssued
      received roster}
    (advance : AuthenticatedAdvance (alpha := alpha) codec progress) :
    Frontier.DeliveryAdvance candidateStamp advance.issued
      (codec.beforeOf progress.acceptedEvent.event)
      (codec.afterOf progress.acceptedEvent.event)
      advance.deliveredBefore advance.deliveredAfter :=
  advance.lawful

end AuthenticatedAdvance

end Uwueave.AuthenticatedFrontier
