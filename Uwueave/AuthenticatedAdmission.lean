/-
# Uwueave.AuthenticatedAdmission — signed admission into Byzantine evidence and gates

`Authenticity`, `Byzantine`, and `Gated` deliberately stop at different model
boundaries.  This module supplies the minimal explicit transports between them:

* accepted signed event payloads are projected through a caller-supplied
  `(sequence, block-id)` codec into `Causality.EntrySet`;
* `Authenticity.AuthenticIssuer` derives — rather than assumes —
  `Byzantine.SignatureAuthentic` for that admitted set; and
* a domain-separated signed `Authenticity.MoveClaim` is admitted only when it
  is accepted, genuinely issued, bound to the grant holder, and independently
  accepted by `Gated.gatedOps`.

Authentication and authorization remain different checks.  The concrete tests
show both directions fail without the conjunction: Mallory can honestly sign a
move citing Alice's live grant and pass the old gate while failing holder
binding; Bob can present a valid, genuinely issued signature and still fail the
gate after his grant is revoked.

This is not shipping-kernel authentication.  FORMAT v3 and `Exec.Op` carry no
submitter, signature, or key epoch.  Nothing below claims that the FFI request
was assembled from this admitted feed.
-/
import Uwueave.Authenticity
import Uwueave.Byzantine
import Uwueave.Gated

namespace Uwueave.AuthenticatedAdmission

open Uwueave Uwueave.Catalog

/-! ## §1. Accepted signed events become authenticated fork observations -/

/-- The deployment-supplied projection from a fully signed ERA event to the
two coordinates Causality needs in addition to the signed issuer.  No name is
hashed and no field is guessed: a deployment may use a causal sequence and a
content hash, while finite examples may use any explicit functions. -/
structure EventTripleCodec where
  sequenceOf : Era.Event → Nat
  blockIdOf : Era.Event → Nat

/-- The exact binding relation used by the transport.  It witnesses that the
triple's author is the signed issuer and that sequence/id came from the signed
event payload through the supplied codec. -/
def EventTripleCodec.Binds {scheme : Authenticity.SignatureScheme}
    (codec : EventTripleCodec) (record : Authenticity.SignedRecord scheme)
    (entry : Nat × Nat × Nat) : Prop :=
  ∃ event, record.payload = .event event ∧
    entry = (record.issuer, codec.sequenceOf event, codec.blockIdOf event)

/-- One accepted event record.  The payload equality is retained rather than
re-decoded from a report tag, and acceptance is checked under the exact key and
key-revocation views supplied as indices. -/
structure AcceptedEvent (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations) where
  record : Authenticity.SignedRecord scheme
  event : Era.Event
  payload_eq : record.payload = .event event
  accepted : Authenticity.Accepted scheme keys keyRevocations record

namespace AcceptedEvent

def entry {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    (codec : EventTripleCodec)
    (accepted : AcceptedEvent scheme keys keyRevocations) : Nat × Nat × Nat :=
  (accepted.record.issuer, codec.sequenceOf accepted.event,
    codec.blockIdOf accepted.event)

theorem binds {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    (codec : EventTripleCodec)
    (accepted : AcceptedEvent scheme keys keyRevocations) :
    codec.Binds accepted.record (accepted.entry codec) :=
  ⟨accepted.event, accepted.payload_eq, rfl⟩

end AcceptedEvent

/-- The received trace corresponding to a finite admitted-event list. -/
def receivedEvents {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    (events : List (AcceptedEvent scheme keys keyRevocations)) :
    Authenticity.SignedRecord scheme → Prop :=
  fun record => ∃ accepted ∈ events, accepted.record = record

/-- Accepted signed events as Causality's grow-only observation set. -/
def observations {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    (codec : EventTripleCodec)
    (events : List (AcceptedEvent scheme keys keyRevocations)) :
    Causality.EntrySet :=
  fun entry => decide (entry ∈ events.map (AcceptedEvent.entry codec))

/-- The exact triple-level issuance relation induced by the same event codec
and Authenticity issuance transcript. -/
def issuedEntries (codec : EventTripleCodec)
    (issued : Authenticity.Issued) : Byzantine.IssuedBy :=
  fun issuer sequence blockId =>
    ∃ keyEpoch event,
      issued issuer keyEpoch (.event event)
        ∧ codec.sequenceOf event = sequence
        ∧ codec.blockIdOf event = blockId

/-- Every admitted observation retains an accepted record and the exact signed
payload-to-triple binding. -/
theorem observation_has_accepted_binding
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    (codec : EventTripleCodec)
    (events : List (AcceptedEvent scheme keys keyRevocations))
    {entry : Nat × Nat × Nat} (h : observations codec events entry = true) :
    ∃ accepted ∈ events,
      accepted.entry codec = entry
        ∧ codec.Binds accepted.record entry
        ∧ Authenticity.Accepted scheme keys keyRevocations accepted.record := by
  have hmem : entry ∈ events.map (AcceptedEvent.entry codec) :=
    of_decide_eq_true h
  obtain ⟨accepted, hin, heq⟩ := List.mem_map.mp hmem
  exact ⟨accepted, hin, heq, heq ▸ accepted.binds codec, accepted.accepted⟩

/-- **The authenticity transport.** Fork-observation authenticity is derived
from issuer authenticity over the accepted signed-record trace.  Positive
users never assume `Byzantine.SignatureAuthentic`: this theorem manufactures
it from `Authenticity.AuthenticIssuer`. -/
theorem authenticIssuer_to_signatureAuthentic
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    (codec : EventTripleCodec)
    (events : List (AcceptedEvent scheme keys keyRevocations))
    (hauth : Authenticity.AuthenticIssuer scheme keys keyRevocations issued
      (receivedEvents events)) :
    Byzantine.SignatureAuthentic (observations codec events)
      (issuedEntries codec issued) := by
  intro issuer sequence blockId hobserved
  obtain ⟨accepted, hin, heq, -, haccepted⟩ :=
    observation_has_accepted_binding codec events hobserved
  have hreceived : receivedEvents events accepted.record :=
    ⟨accepted, hin, rfl⟩
  have hissued := hauth accepted.record hreceived haccepted
  unfold Authenticity.WasIssued at hissued
  rw [accepted.payload_eq] at hissued
  have hcoords :
      accepted.record.issuer = issuer
        ∧ codec.sequenceOf accepted.event = sequence
        ∧ codec.blockIdOf accepted.event = blockId := by
    simpa [AcceptedEvent.entry] using heq
  exact ⟨accepted.record.keyEpoch, accepted.event,
    hcoords.1 ▸ hissued, hcoords.2.1, hcoords.2.2⟩

/-! ## §2. Honest signed equivocation, and the framing control -/

/-- The finite witness uses one explicit slot and the signed event id as its
block id.  This codec is a test fixture, not a hash claim. -/
def forkCodec : EventTripleCodec where
  sequenceOf := fun _ => 4
  blockIdOf := Era.Event.eid

def forkEventA : Era.Event := Era.writeEv 101 7
def forkEventB : Era.Event := Era.writeEv 102 7

def forkIssued : Authenticity.Issued :=
  fun issuer epoch payload =>
    issuer = 7 ∧ epoch = 1 ∧
      (payload = .event forkEventA ∨ payload = .event forkEventB)

def forkRecordA : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 7 1 (.event forkEventA)

def forkRecordB : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 7 1 (.event forkEventB)

theorem forkRecordA_accepted :
    Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations forkRecordA := by
  apply Authenticity.signRecord_accepted
  · simp [Authenticity.toyKeys]
  · rfl

theorem forkRecordB_accepted :
    Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations forkRecordB := by
  apply Authenticity.signRecord_accepted
  · simp [Authenticity.toyKeys]
  · rfl

def forkAcceptedA : AcceptedEvent Authenticity.toyScheme Authenticity.toyKeys
    Authenticity.noRevocations :=
  ⟨forkRecordA, forkEventA, rfl, forkRecordA_accepted⟩

def forkAcceptedB : AcceptedEvent Authenticity.toyScheme Authenticity.toyKeys
    Authenticity.noRevocations :=
  ⟨forkRecordB, forkEventB, rfl, forkRecordB_accepted⟩

def forkEvents : List (AcceptedEvent Authenticity.toyScheme Authenticity.toyKeys
    Authenticity.noRevocations) := [forkAcceptedA, forkAcceptedB]

theorem honest_fork_trace_authentic :
    Authenticity.AuthenticIssuer Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations forkIssued (receivedEvents forkEvents) := by
  intro record hreceived _
  obtain ⟨accepted, hin, rfl⟩ := hreceived
  simp [forkEvents] at hin
  rcases hin with rfl | rfl
  · exact ⟨rfl, rfl, Or.inl rfl⟩
  · exact ⟨rfl, rfl, Or.inr rfl⟩

theorem honest_fork_signatureAuthentic :
    Byzantine.SignatureAuthentic (observations forkCodec forkEvents)
      (issuedEntries forkCodec forkIssued) :=
  authenticIssuer_to_signatureAuthentic forkCodec forkEvents
    honest_fork_trace_authentic

theorem honest_fork_evidence :
    Causality.ForkEvidence (observations forkCodec forkEvents) 7 :=
  ⟨4, 101, 102, by decide, by decide, by decide⟩

/-- **Honest equivocation attributes the author.** The attribution premise is
derived from `AuthenticIssuer` above, never postulated for this test. -/
theorem honest_equivocation_attributes_author :
    Byzantine.Equivocated (issuedEntries forkCodec forkIssued) 7 :=
  Byzantine.fork_evidence_attributes_author honest_fork_signatureAuthentic
    honest_fork_evidence

/-- Omitting authentic admission retains Byzantine's exact framing attack. -/
theorem omitted_authenticity_permits_framing :
    Causality.ForkEvidence Byzantine.forkedGossip 17
      ∧ ¬ Byzantine.Equivocated Byzantine.honestIssuance 17
      ∧ ¬ Byzantine.SignatureAuthentic Byzantine.forkedGossip
        Byzantine.honestIssuance :=
  Byzantine.forged_branch_can_frame_without_authentication

/-! ## §3. Signed moves meet the ordinary grant gate -/

/-- Forget the neutral signed wrapper into the gate's operation carrier. -/
def moveClaimToGOp (claim : Authenticity.MoveClaim) : Gated.GOp :=
  ⟨claim.t, claim.node, claim.dest, claim.cite⟩

/-- The deployment's explicit bearer/holder policy.  It answers who may sign a
submission citing a grant; `Gated.permitted` intentionally answers only whether
the grant chain is active and covers the node. -/
abbrev GrantHolder := Nat → Nat → Prop

/-- An authenticated and authorized operation.  All five checks remain
visible: receipt, signature acceptance, genuine issuance, holder binding, and
the ordinary capability gate. -/
structure AuthenticatedGatedOp
    (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop)
    (holder : GrantHolder) (state : Gated.GatedState) where
  record : Authenticity.SignedRecord scheme
  claim : Authenticity.MoveClaim
  payload_eq : record.payload = .move claim
  received_record : received record
  accepted_record : Authenticity.Accepted scheme keys keyRevocations record
  wasIssued : Authenticity.WasIssued issued record
  holdsCitation : holder record.issuer claim.cite
  gated : Gated.gatedOps state (moveClaimToGOp claim)

namespace AuthenticatedGatedOp

/-- Build the conjunction only from issuer authenticity plus the independent
holder and gate checks. -/
def ofAuthenticIssuer
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {holder : GrantHolder} {state : Gated.GatedState}
    (hauth : Authenticity.AuthenticIssuer scheme keys keyRevocations issued received)
    (record : Authenticity.SignedRecord scheme) (claim : Authenticity.MoveClaim)
    (payload_eq : record.payload = .move claim)
    (hreceived : received record)
    (haccepted : Authenticity.Accepted scheme keys keyRevocations record)
    (hholder : holder record.issuer claim.cite)
    (hgated : Gated.gatedOps state (moveClaimToGOp claim)) :
    AuthenticatedGatedOp scheme keys keyRevocations issued received holder state :=
  ⟨record, claim, payload_eq, hreceived, haccepted,
    hauth record hreceived haccepted, hholder, hgated⟩

theorem authentic
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {holder : GrantHolder} {state : Gated.GatedState}
    (op : AuthenticatedGatedOp scheme keys keyRevocations issued received holder state) :
    Authenticity.WasIssued issued op.record := op.wasIssued

theorem authorized
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {holder : GrantHolder} {state : Gated.GatedState}
    (op : AuthenticatedGatedOp scheme keys keyRevocations issued received holder state) :
    Gated.gatedOps state (moveClaimToGOp op.claim) := op.gated

end AuthenticatedGatedOp

/-! ## §4. Concrete admission and refusal tests -/

/-- One toy key per demo actor, all intentionally sharing the toy secret 11. -/
def moveKeys : Authenticity.Keyring Authenticity.toyScheme :=
  fun issuer epoch =>
    if epoch = 1 ∧ (issuer = Era.alice ∨ issuer = Era.bob ∨ issuer = 3)
    then some 11 else none

/-- Alice holds grant 1; Bob holds delegated grant 2; Mallory holds neither. -/
def demoGrantHolder : GrantHolder :=
  fun issuer cite =>
    (issuer = Era.alice ∧ cite = 1) ∨ (issuer = Era.bob ∧ cite = 2)

def aliceClaim : Authenticity.MoveClaim := ⟨1, 7, none, 1⟩
def bobClaim : Authenticity.MoveClaim := ⟨2, 3, some 7, 2⟩
def malloryClaim : Authenticity.MoveClaim := ⟨99, 7, none, 1⟩

theorem aliceClaim_toGOp : moveClaimToGOp aliceClaim = Gated.opAlice := rfl
theorem bobClaim_toGOp : moveClaimToGOp bobClaim = Gated.opBob := rfl
theorem malloryClaim_toGOp :
    moveClaimToGOp malloryClaim = Byzantine.mallorySubmission.op := rfl

def aliceRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 Era.alice 1 (.move aliceClaim)

def aliceIssued : Authenticity.Issued :=
  fun issuer epoch payload =>
    issuer = Era.alice ∧ epoch = 1 ∧ payload = .move aliceClaim

def aliceReceived : Authenticity.SignedRecord Authenticity.toyScheme → Prop :=
  fun record => record = aliceRecord

theorem aliceRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme moveKeys
      Authenticity.noRevocations aliceRecord := by
  apply Authenticity.signRecord_accepted
  · simp [moveKeys, Era.alice]
  · rfl

theorem alice_trace_authentic :
    Authenticity.AuthenticIssuer Authenticity.toyScheme moveKeys
      Authenticity.noRevocations aliceIssued aliceReceived := by
  intro record hreceived _
  subst record
  exact ⟨rfl, rfl, rfl⟩

/-- Alice's own signed, issued, holder-bound move passes the gate. -/
def alice_authenticated_move :
    AuthenticatedGatedOp Authenticity.toyScheme moveKeys
      Authenticity.noRevocations aliceIssued aliceReceived demoGrantHolder
      Gated.synced :=
  AuthenticatedGatedOp.ofAuthenticIssuer alice_trace_authentic aliceRecord
    aliceClaim rfl rfl aliceRecord_accepted
    (by simp [demoGrantHolder, aliceRecord, aliceClaim,
      Authenticity.signRecord, Era.alice, Era.bob])
    (aliceClaim_toGOp ▸ Gated.story_alice_survives)

theorem alice_signed_own_grant_is_accepted :
    Authenticity.WasIssued aliceIssued alice_authenticated_move.record
      ∧ Gated.gatedOps Gated.synced
        (moveClaimToGOp alice_authenticated_move.claim) :=
  ⟨alice_authenticated_move.authentic, alice_authenticated_move.authorized⟩

def malloryRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 3 1 (.move malloryClaim)

theorem malloryRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme moveKeys
      Authenticity.noRevocations malloryRecord := by
  apply Authenticity.signRecord_accepted
  · simp [moveKeys, Era.alice, Era.bob]
  · rfl

/-- Mallory's signature is valid and the old gate accepts the cited grant, but
the explicit holder policy rejects the borrowed citation. -/
theorem mallory_fails_holder_even_when_gate_passes :
    Authenticity.Accepted Authenticity.toyScheme moveKeys
        Authenticity.noRevocations malloryRecord
      ∧ Gated.gatedOps Byzantine.malloryGateState (moveClaimToGOp malloryClaim)
      ∧ ¬ demoGrantHolder malloryRecord.issuer malloryClaim.cite := by
  refine ⟨malloryRecord_accepted, ?_, ?_⟩
  · rw [malloryClaim_toGOp]
    exact Byzantine.unauthenticated_submission_can_pass_the_gate.2
  · simp [demoGrantHolder, malloryRecord, malloryClaim,
      Authenticity.signRecord, Era.alice, Era.bob]

/-- A move forged under Alice's name.  The toy scheme permits manufacturing
the accepting signature without calling `signRecord`. -/
def forgedAsAlice : Authenticity.SignedRecord Authenticity.toyScheme where
  issuer := Era.alice
  keyEpoch := 1
  payload := .move malloryClaim
  signature := 11 :: Authenticity.signingMessage Era.alice 1 (.move malloryClaim)

theorem forgedAsAlice_accepted :
    Authenticity.Accepted Authenticity.toyScheme moveKeys
      Authenticity.noRevocations forgedAsAlice := by
  refine ⟨11, by simp [moveKeys, forgedAsAlice, Era.alice], rfl, ?_⟩
  simp [Authenticity.toyScheme, forgedAsAlice]

theorem forgedAsAlice_not_issued :
    ¬ Authenticity.WasIssued aliceIssued forgedAsAlice := by
  simp [Authenticity.WasIssued, aliceIssued, forgedAsAlice,
    aliceClaim, malloryClaim]

def aliceAttackReceived : Authenticity.SignedRecord Authenticity.toyScheme → Prop :=
  fun record => record = aliceRecord ∨ record = forgedAsAlice

theorem forged_as_alice_breaks_authenticity :
    ¬ Authenticity.AuthenticIssuer Authenticity.toyScheme moveKeys
      Authenticity.noRevocations aliceIssued aliceAttackReceived := by
  intro hauth
  exact forgedAsAlice_not_issued
    (hauth forgedAsAlice (Or.inr rfl) forgedAsAlice_accepted)

/-- The generic constructive handoff produces the exact cryptographic
reduction input for the forged move. -/
theorem forged_as_alice_yields_forgeryWitness :
    ∃ witness : Authenticity.ForgeryWitness Authenticity.toyScheme moveKeys
        Authenticity.noRevocations aliceIssued,
      aliceAttackReceived witness.record :=
  Authenticity.authenticity_violation_extracts_forgery
    forged_as_alice_breaks_authenticity

def bobRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 Era.bob 1 (.move bobClaim)

def bobIssued : Authenticity.Issued :=
  fun issuer epoch payload =>
    issuer = Era.bob ∧ epoch = 1 ∧ payload = .move bobClaim

theorem bobRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme moveKeys
      Authenticity.noRevocations bobRecord := by
  apply Authenticity.signRecord_accepted
  · simp [moveKeys, Era.alice, Era.bob]
  · rfl

theorem bobRecord_wasIssued : Authenticity.WasIssued bobIssued bobRecord :=
  ⟨rfl, rfl, rfl⟩

/-- Signature validity and genuine issuance do not override capability
revocation: Bob's cited grant is revoked in `Gated.synced`, so authorization
still fails. -/
theorem valid_signature_over_revoked_grant_fails_authorization :
    Authenticity.Accepted Authenticity.toyScheme moveKeys
        Authenticity.noRevocations bobRecord
      ∧ Authenticity.WasIssued bobIssued bobRecord
      ∧ demoGrantHolder bobRecord.issuer bobClaim.cite
      ∧ ¬ Gated.gatedOps Gated.synced (moveClaimToGOp bobClaim) := by
  refine ⟨bobRecord_accepted, bobRecord_wasIssued,
    by simp [demoGrantHolder, bobRecord, bobClaim,
      Authenticity.signRecord, Era.alice, Era.bob], ?_⟩
  rw [bobClaim_toGOp]
  exact Gated.story_bob_gated_out

end Uwueave.AuthenticatedAdmission
