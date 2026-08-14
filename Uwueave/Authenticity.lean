/-
# Uwueave.Authenticity — the constructive authentication boundary.

`Authority.UniqueGrant` and `Sequence.UniqueAnchor` turn a uniqueness failure
into a concrete hash-collision witness. ERA's finality boundary needs the
signature analogue: if a replica accepts a grant, event, or move attributed to an
issuer, but that issuer did not issue it, the bad state must hand a
cryptographic reduction a concrete forgery candidate rather than merely carry
the word "authentic" as a premise.

This module supplies that handoff. It does **not** implement a cryptographic
primitive and proves no hardness claim.

  * `SignatureScheme` names the ordinary key generation boundary, signing,
    verification, and honest-signature correctness. Security is deliberately
    not a field: putting "unforgeable" in a structure would not prove it.
  * `Payload` and `signingMessage` bind a protocol/version prefix, a distinct
    grant/event/move domain tag, the issuer, the key epoch, and every payload field.
    `grant_event_domain_separated` makes the cross-domain separation a theorem.
  * `AuthenticIssuer` is the safety property over records that actually reached
    a deployment trace. `EUFStylePremise` says that trace contains no accepted,
    unissued signed record. `authenticity_violation_extracts_forgery` is the
    constructive handoff: every authenticity violation yields the exact record,
    registered public key, successful verification, and non-issuance proof.
  * `accepted_antitone_revocation` proves growing the revoked-key set can only
    remove accepted records. `rotation_rejects_older_record` states the separate
    current-key policy: after advancing an issuer's epoch, old records remain
    historical evidence but cannot be accepted as current issuance.
  * The final section is satisfiable and refutable. `toyScheme` is deliberately
    insecure (its public key is its signing secret), so it supports one honest
    trace and also a concrete forged grant. The example demonstrates the
    vocabulary; it is emphatically not evidence for a deployed scheme.

## TRANSPORTS row owed by this module

**Accepted signed record → authentic issuer** ⚠ · *transport*
`eufStyle_implies_authenticIssuer` · *needs* the trace-relative
`EUFStylePremise` for the deployed signature scheme, the exact registered key,
and the domain-separated `signingMessage` · *without it*
`attack_not_authentic` and `attack_extracts_forgery` exhibit an accepted grant
the named issuer never issued.

**Authentic issuer → authenticated admission** · *transports*
`AuthenticatedAdmission.authenticIssuer_to_signatureAuthentic` derives
Byzantine triple authenticity from accepted signed event records through an
explicit event-triple codec;
`AuthenticatedAdmission.AuthenticatedGatedOp.ofAuthenticIssuer` derives genuine
issuance for a received, accepted signed move before conjoining explicit grant
holder binding and the ordinary gate. Both consume `AuthenticIssuer`; neither
manufactures it.

## Honest boundary

⟨TERMINAL⟩ The extractor, domain separation, honest-signature correctness
transport, revocation antitonicity, and key-epoch rejection are theorems of the
model below.

⟨PREMISE U-0001 at the deployment-cryptography boundary⟩ A deployment must instantiate
`SignatureScheme`, its key registry, key rotation, and its issuance log, then
justify `EUFStylePremise` by an actual EUF-CMA-style reduction for the chosen
signature scheme. `AuthenticatedAdmission.authenticIssuer_to_signatureAuthentic`
and `AuthenticatedGatedOp.ofAuthenticIssuer` now close the model-level admission
transports once `AuthenticIssuer` is supplied; they do not supply it. This file
has no security parameter, probabilistic adversary, query bound, side-channel
model, key-generation entropy, byte codec, or theorem about
Ed25519/ML-DSA/another concrete primitive. The deterministic trace predicate is
the *conclusion* a computational proof must supply, not that proof wearing a new
name.
-/

import Uwueave.Authority
import Uwueave.Era

namespace Uwueave.Authenticity

/-! ## §1. Domain-separated deployed messages -/

/-- The message carrier at the model boundary. A deployed codec replaces each
`Nat` with a canonical fixed-width or length-delimited byte encoding. -/
abbrev Message := List Nat

/-- ASCII `UWEAVE` as a numeric protocol tag. It is a domain constant, not a
cryptographic digest. -/
def protocolTag : Nat := 0x555745415645

/-- Version of this signing envelope. Versioning is inside the signed bytes. -/
def encodingVersion : Nat := 1

/-- ASCII `GRANT`, separating authority grants from every other payload. -/
def grantDomain : Nat := 0x4752414e54

/-- ASCII `EVENT`, separating ERA events from every other payload. -/
def eventDomain : Nat := 0x4556454e54

/-- ASCII `MOVE`, separating signed move submissions from grants and ERA
events. -/
def moveDomain : Nat := 0x4d4f5645

/-- The neutral move payload signed at the admission boundary.  It repeats the
four semantic fields of `Gated.GOp` without importing the gate (and therefore
without creating an authentication/authorization import cycle).  The outer
`SignedRecord.issuer` is the submitter identity. -/
structure MoveClaim where
  t : Nat
  node : Nat
  dest : Option Nat
  cite : Nat
  deriving DecidableEq, Repr

/-- The authenticated objects this bridge currently carries. The grant is
`(id, parent, scope)` from `Authority`; the event is ERA's complete five-field
group-management event; and a move binds every field later read by `Gated`. -/
inductive Payload where
  | grant (value : Authority.Grant)
  | event (value : Era.Event)
  | move (value : MoveClaim)
  deriving DecidableEq, Repr

/-- Canonical field-level encoding with a protocol prefix, encoding version,
and object-domain tag. No field is omitted. -/
def encodePayload : Payload → Message
  | .grant g =>
      [protocolTag, encodingVersion, grantDomain, g.1, g.2.1, g.2.2]
  | .event e =>
      [protocolTag, encodingVersion, eventDomain,
       e.eid, e.kind, e.actor, e.target, e.role]
  | .move op =>
      [protocolTag, encodingVersion, moveDomain, op.t, op.node,
       match op.dest with | none => 0 | some _ => 1,
       op.dest.getD 0, op.cite]

/-- The signature covers attribution and rotation metadata as well as the
payload. An envelope cannot change issuer or key epoch while retaining the
same signed message. -/
def signingMessage (issuer keyEpoch : Nat) (payload : Payload) : Message :=
  [protocolTag, encodingVersion, issuer, keyEpoch] ++ encodePayload payload

/-- Grant bytes and event bytes are distinct even when every numeric payload
field happens to agree. This is the cross-protocol substitution barrier. -/
theorem grant_event_domain_separated (g : Authority.Grant) (e : Era.Event) :
    encodePayload (.grant g) ≠ encodePayload (.event e) := by
  simp [encodePayload, grantDomain, eventDomain]

/-- Domain separation survives the outer issuer/key-epoch envelope. -/
theorem signingMessage_grant_ne_event (issuer keyEpoch : Nat)
    (g : Authority.Grant) (e : Era.Event) :
    signingMessage issuer keyEpoch (.grant g) ≠
      signingMessage issuer keyEpoch (.event e) := by
  simp [signingMessage, encodePayload, grantDomain, eventDomain]

/-- Equality of two signed grant messages pins the issuer, key epoch, and all
three grant fields. The envelope is a binding, not an unsigned label. -/
theorem signingMessage_grant_injective
    {issuer keyEpoch issuer' keyEpoch' : Nat}
    {g g' : Authority.Grant}
    (h : signingMessage issuer keyEpoch (.grant g) =
      signingMessage issuer' keyEpoch' (.grant g')) :
    issuer = issuer' ∧ keyEpoch = keyEpoch' ∧ g = g' := by
  rcases g with ⟨gid, gparent, gscope⟩
  rcases g' with ⟨gid', gparent', gscope'⟩
  simp [signingMessage, encodePayload] at h ⊢
  exact h

/-- Equality of two signed ERA messages pins the issuer, key epoch, and every
event field. -/
theorem signingMessage_event_injective
    {issuer keyEpoch issuer' keyEpoch' : Nat}
    {e e' : Era.Event}
    (h : signingMessage issuer keyEpoch (.event e) =
      signingMessage issuer' keyEpoch' (.event e')) :
    issuer = issuer' ∧ keyEpoch = keyEpoch' ∧ e = e' := by
  cases e
  cases e'
  simp [signingMessage, encodePayload] at h ⊢
  exact h

/-- Move submissions occupy neither the grant nor the event signing domain. -/
theorem move_domain_separated (op : MoveClaim) (g : Authority.Grant)
    (e : Era.Event) :
    encodePayload (.move op) ≠ encodePayload (.grant g)
      ∧ encodePayload (.move op) ≠ encodePayload (.event e) := by
  constructor <;> simp [encodePayload, moveDomain, grantDomain, eventDomain]

/-- Equality of signed move messages pins the submitter, key epoch, and all
four operation fields.  In particular, `cite` is signed data rather than
unsigned routing metadata. -/
theorem signingMessage_move_injective
    {issuer keyEpoch issuer' keyEpoch' : Nat}
    {op op' : MoveClaim}
    (h : signingMessage issuer keyEpoch (.move op) =
      signingMessage issuer' keyEpoch' (.move op')) :
    issuer = issuer' ∧ keyEpoch = keyEpoch' ∧ op = op' := by
  rcases op with ⟨t, node, dest, cite⟩
  rcases op' with ⟨t', node', dest', cite'⟩
  cases dest <;> cases dest' <;>
    simp [signingMessage, encodePayload] at h ⊢ <;> exact h

/-! ## §2. A named signature scheme, without a hardness theorem -/

/-- An abstract signature scheme with the one algebraic fact honest operation
needs: a signature made by `sk` verifies under its public key. No security
property is smuggled into the structure. -/
structure SignatureScheme where
  /-- Signing-key carrier. -/
  SecretKey : Type
  /-- Verification-key carrier. -/
  PublicKey : Type
  /-- Signature carrier. -/
  Signature : Type
  /-- Public-key derivation. -/
  publicKey : SecretKey → PublicKey
  /-- Sign one complete domain-separated message. -/
  sign : SecretKey → Message → Signature
  /-- Verify one complete domain-separated message. -/
  verify : PublicKey → Message → Signature → Bool
  /-- Correctness for honestly generated signatures. -/
  correct : ∀ sk message, verify (publicKey sk) message (sign sk message) = true

/-- A signed protocol record. Both attribution fields occur again inside
`signingMessage`; they are not unsigned routing metadata. -/
structure SignedRecord (scheme : SignatureScheme) where
  /-- Claimed issuer identity. -/
  issuer : Nat
  /-- Version of the issuer's verification key. -/
  keyEpoch : Nat
  /-- Grant, event, or move being authenticated. -/
  payload : Payload
  /-- Signature over `signingMessage issuer keyEpoch payload`. -/
  signature : scheme.Signature

/-- Registry lookup by `(issuer, key epoch)`. Rotation adds a new binding; it
does not silently reinterpret signatures made for an old key. -/
abbrev Keyring (scheme : SignatureScheme) :=
  Nat → Nat → Option scheme.PublicKey

/-- Grow-only revocation view, indexed exactly like the key registry. -/
abbrev Revocations := Nat → Nat → Bool

/-- The external issuance log/oracle transcript: did this issuer, under this
key epoch, authorize this exact payload? -/
abbrev Issued := Nat → Nat → Payload → Prop

/-- A record verifies under its exact registered, non-revoked key. -/
def Accepted (scheme : SignatureScheme) (keys : Keyring scheme)
    (revoked : Revocations) (record : SignedRecord scheme) : Prop :=
  ∃ key,
    keys record.issuer record.keyEpoch = some key
      ∧ revoked record.issuer record.keyEpoch = false
      ∧ scheme.verify key
          (signingMessage record.issuer record.keyEpoch record.payload)
          record.signature = true

/-- The issuance-log reading of one record. -/
def WasIssued (issued : Issued) {scheme : SignatureScheme}
    (record : SignedRecord scheme) : Prop :=
  issued record.issuer record.keyEpoch record.payload

/-- Construct a correctly signed record. -/
def signRecord (scheme : SignatureScheme) (sk : scheme.SecretKey)
    (issuer keyEpoch : Nat) (payload : Payload) : SignedRecord scheme where
  issuer := issuer
  keyEpoch := keyEpoch
  payload := payload
  signature := scheme.sign sk (signingMessage issuer keyEpoch payload)

/-- Honest signing produces an accepted record when the exact public key is
registered and has not been revoked. -/
theorem signRecord_accepted {scheme : SignatureScheme} {keys : Keyring scheme}
    {revoked : Revocations} (sk : scheme.SecretKey) (issuer keyEpoch : Nat)
    (payload : Payload)
    (hkey : keys issuer keyEpoch = some (scheme.publicKey sk))
    (hactive : revoked issuer keyEpoch = false) :
    Accepted scheme keys revoked (signRecord scheme sk issuer keyEpoch payload) := by
  refine ⟨scheme.publicKey sk, hkey, hactive, ?_⟩
  simpa [signRecord] using scheme.correct sk (signingMessage issuer keyEpoch payload)

/-! ## §3. Authentic issuer and the EUF-style handoff -/

/-- A complete forgery candidate extracted from a bad trace: exact record,
exact registered key, successful verification, and proof that the claimed
issuer did not issue the payload under that key epoch. This is what a
computational reduction consumes. -/
structure ForgeryWitness (scheme : SignatureScheme) (keys : Keyring scheme)
    (revoked : Revocations) (issued : Issued) where
  /-- The adversarially supplied record. -/
  record : SignedRecord scheme
  /-- Public key under which it verified. -/
  publicKey : scheme.PublicKey
  /-- The verification key is the deployment's registered key for this issuer
  and epoch. -/
  keyRegistered :
    keys record.issuer record.keyEpoch = some publicKey
  /-- The key had not been revoked at acceptance time. -/
  keyNotRevoked : revoked record.issuer record.keyEpoch = false
  /-- Verification accepts the complete domain-separated message. -/
  verifies : scheme.verify publicKey
    (signingMessage record.issuer record.keyEpoch record.payload)
    record.signature = true
  /-- The signing oracle/issuer did not authorize this payload. -/
  notIssued : ¬ WasIssued issued record

/-- A forgery witness is, in particular, an accepted record. -/
theorem ForgeryWitness.accepted {scheme : SignatureScheme}
    {keys : Keyring scheme} {revoked : Revocations} {issued : Issued}
    (w : ForgeryWitness scheme keys revoked issued) :
    Accepted scheme keys revoked w.record :=
  ⟨w.publicKey, w.keyRegistered, w.keyNotRevoked, w.verifies⟩

/-- Issuer authenticity over a concrete reachable/received trace. It says no
accepted record in that trace lies about having been issued. -/
def AuthenticIssuer (scheme : SignatureScheme) (keys : Keyring scheme)
    (revoked : Revocations) (issued : Issued)
    (received : SignedRecord scheme → Prop) : Prop :=
  ∀ record, received record → Accepted scheme keys revoked record →
    WasIssued issued record

/-- The deterministic, trace-relative conclusion supplied by an EUF-style
security argument: the trace contains no accepted unissued record. This is not
the probabilistic/PPT security game itself; see the module boundary. -/
def EUFStylePremise (scheme : SignatureScheme) (keys : Keyring scheme)
    (revoked : Revocations) (issued : Issued)
    (received : SignedRecord scheme → Prop) : Prop :=
  ¬ ∃ w : ForgeryWitness scheme keys revoked issued, received w.record

/-- Authenticity is exactly absence of a received forgery witness. The reverse
direction packages an accepted, unissued record into the constructive object a
cryptographic reduction expects. -/
theorem authenticIssuer_iff_no_received_forgery
    (scheme : SignatureScheme) (keys : Keyring scheme)
    (revoked : Revocations) (issued : Issued)
    (received : SignedRecord scheme → Prop) :
    AuthenticIssuer scheme keys revoked issued received ↔
      EUFStylePremise scheme keys revoked issued received := by
  constructor
  · intro ha ⟨w, hreceived⟩
    exact w.notIssued (ha w.record hreceived w.accepted)
  · intro hno record hreceived haccepted
    apply Classical.byContradiction
    intro hnot
    obtain ⟨key, hkey, hactive, hverify⟩ := haccepted
    exact hno ⟨{
      record := record
      publicKey := key
      keyRegistered := hkey
      keyNotRevoked := hactive
      verifies := hverify
      notIssued := hnot
    }, hreceived⟩

/-- **The signature analogue of the collision extractors.** Negating issuer
authenticity constructs a concrete accepted forgery from the bad trace. No
cryptographic hardness is concluded; a deployed EUF reduction is what makes
the existence of this witness negligibly likely. -/
theorem authenticity_violation_extracts_forgery
    {scheme : SignatureScheme} {keys : Keyring scheme}
    {revoked : Revocations} {issued : Issued}
    {received : SignedRecord scheme → Prop}
    (hbad : ¬ AuthenticIssuer scheme keys revoked issued received) :
    ∃ w : ForgeryWitness scheme keys revoked issued, received w.record := by
  apply Classical.byContradiction
  intro hnone
  exact hbad ((authenticIssuer_iff_no_received_forgery
    scheme keys revoked issued received).2 hnone)

/-- The externally justified EUF-style premise closes the authenticity
boundary. This theorem transports the premise; it does not prove it. -/
theorem eufStyle_implies_authenticIssuer
    {scheme : SignatureScheme} {keys : Keyring scheme}
    {revoked : Revocations} {issued : Issued}
    {received : SignedRecord scheme → Prop}
    (heuf : EUFStylePremise scheme keys revoked issued received) :
    AuthenticIssuer scheme keys revoked issued received :=
  (authenticIssuer_iff_no_received_forgery
    scheme keys revoked issued received).2 heuf

/-! ## §4. Revocation and rotation -/

/-- Revocation views only grow. -/
def RevocationsGrow (old new : Revocations) : Prop :=
  ∀ issuer keyEpoch, old issuer keyEpoch = true →
    new issuer keyEpoch = true

/-- Growing the revocation set can only remove accepted records. If a record
still verifies under the larger set, it verified under the smaller set too. -/
theorem accepted_antitone_revocation
    {scheme : SignatureScheme} {keys : Keyring scheme}
    {old new : Revocations} (hgrows : RevocationsGrow old new)
    {record : SignedRecord scheme}
    (haccepted : Accepted scheme keys new record) :
    Accepted scheme keys old record := by
  obtain ⟨key, hkey, hnew, hverify⟩ := haccepted
  refine ⟨key, hkey, ?_, hverify⟩
  cases hold : old record.issuer record.keyEpoch with
  | false => rfl
  | true =>
      have h := hgrows record.issuer record.keyEpoch hold
      rw [h] at hnew
      contradiction

/-- Add one `(issuer, key epoch)` to the grow-only revocation view. -/
def revokeKey (revoked : Revocations) (issuer keyEpoch : Nat) : Revocations :=
  fun i k => revoked i k || (decide (i = issuer) && decide (k = keyEpoch))

/-- `revokeKey` really grows the revocation view. -/
theorem revokeKey_grows (revoked : Revocations) (issuer keyEpoch : Nat) :
    RevocationsGrow revoked (revokeKey revoked issuer keyEpoch) := by
  intro i k h
  simp [revokeKey, h]

/-- A record is rejected after revoking its exact bound key epoch, regardless
of its signature bytes. -/
theorem revokeKey_rejects {scheme : SignatureScheme} {keys : Keyring scheme}
    (revoked : Revocations) (record : SignedRecord scheme) :
    ¬ Accepted scheme keys
      (revokeKey revoked record.issuer record.keyEpoch) record := by
  intro haccepted
  obtain ⟨_, _, hactive, _⟩ := haccepted
  simp [revokeKey] at hactive

/-- The currently authorized signing epoch for each issuer. Historical
verification and current issuance are intentionally separate notions. -/
abbrev CurrentEpoch := Nat → Nat

/-- Does a record use its issuer's current key epoch? -/
def UsesCurrentKey {scheme : SignatureScheme} (current : CurrentEpoch)
    (record : SignedRecord scheme) : Prop :=
  current record.issuer = record.keyEpoch

/-- Current-policy acceptance: signature-valid, non-revoked, and made under
the issuer's current key epoch. -/
def AcceptedCurrent (scheme : SignatureScheme) (keys : Keyring scheme)
    (revoked : Revocations) (current : CurrentEpoch)
    (record : SignedRecord scheme) : Prop :=
  Accepted scheme keys revoked record ∧ UsesCurrentKey current record

/-- Advance one issuer's current signing-key epoch. -/
def rotateCurrent (current : CurrentEpoch) (issuer nextEpoch : Nat) : CurrentEpoch :=
  fun i => if i = issuer then nextEpoch else current i

/-- After rotation to a strictly newer epoch, a record from the old epoch
cannot be accepted as *current*. It may remain valid historical evidence until
that old key is revoked; this theorem does not erase history. -/
theorem rotation_rejects_older_record
    {scheme : SignatureScheme} {keys : Keyring scheme}
    {revoked : Revocations} {current : CurrentEpoch}
    {record : SignedRecord scheme} {issuer nextEpoch : Nat}
    (hissuer : record.issuer = issuer)
    (holder : record.keyEpoch < nextEpoch) :
    ¬ AcceptedCurrent scheme keys revoked
      (rotateCurrent current issuer nextEpoch) record := by
  intro haccepted
  have hcurrent := haccepted.2
  unfold UsesCurrentKey rotateCurrent at hcurrent
  simp [hissuer] at hcurrent
  omega

/-! ## §5. Inhabited and refutable: an intentionally insecure scheme -/

/-- A correctness-satisfying but completely insecure scheme: a signature is
the public key consed onto the message, and the public key equals the secret.
It exists only to demonstrate that the boundary predicates have both positive
and negative models. -/
abbrev toyScheme : SignatureScheme where
  SecretKey := Nat
  PublicKey := Nat
  Signature := List Nat
  publicKey := id
  sign sk message := sk :: message
  verify pk message signature := decide (signature = pk :: message)
  correct := by intro sk message; simp

/-- Issuer 7's epoch-1 toy verification key. -/
def toyKeys : Keyring toyScheme :=
  fun issuer epoch => if issuer = 7 ∧ epoch = 1 then some 11 else none

/-- Initially no toy key is revoked. -/
def noRevocations : Revocations := fun _ _ => false

/-- One genuinely issued ERA event. -/
def honestEvent : Era.Event := Era.promoteEv 31 7 8 Era.writer

/-- The toy issuer's exact issuance transcript. -/
def honestIssued : Issued :=
  fun issuer epoch payload =>
    issuer = 7 ∧ epoch = 1 ∧ payload = .event honestEvent

/-- The correctly signed event. -/
def honestRecord : SignedRecord toyScheme :=
  signRecord toyScheme 11 7 1 (.event honestEvent)

theorem honestRecord_accepted :
    Accepted toyScheme toyKeys noRevocations honestRecord := by
  apply signRecord_accepted
  · simp [toyKeys]
  · rfl

/-- A trace containing only the actually issued event. -/
def honestReceived : SignedRecord toyScheme → Prop :=
  fun record => record = honestRecord

/-- The authenticity property is satisfiable. -/
theorem honest_trace_authentic :
    AuthenticIssuer toyScheme toyKeys noRevocations honestIssued honestReceived := by
  intro record hreceived _
  subst record
  exact ⟨rfl, rfl, rfl⟩

/-- Consequently the trace-relative EUF conclusion is satisfiable too, even
though the toy scheme is globally insecure. Reachability is part of the
premise, not an afterthought. -/
theorem honest_trace_euf_style :
    EUFStylePremise toyScheme toyKeys noRevocations honestIssued honestReceived :=
  (authenticIssuer_iff_no_received_forgery
    toyScheme toyKeys noRevocations honestIssued honestReceived).1
    honest_trace_authentic

/-- A grant the toy issuer never issued. -/
def forgedGrant : Authority.Grant := (41, 0, 9)

/-- Anyone knowing the toy public key can manufacture this accepting signature.
The definition intentionally does not call `toyScheme.sign`. -/
def forgedRecord : SignedRecord toyScheme where
  issuer := 7
  keyEpoch := 1
  payload := .grant forgedGrant
  signature := 11 :: signingMessage 7 1 (.grant forgedGrant)

theorem forgedRecord_accepted :
    Accepted toyScheme toyKeys noRevocations forgedRecord := by
  refine ⟨11, by simp [toyKeys, forgedRecord], rfl, ?_⟩
  simp [toyScheme, forgedRecord]

theorem forgedRecord_not_issued : ¬ WasIssued honestIssued forgedRecord := by
  simp [WasIssued, honestIssued, forgedRecord]

/-- Domain separation prevents replaying the honest event signature as the
forged grant signature. The explicit forged signature above must instead sign
the grant-domain message. -/
theorem toy_cross_domain_replay_rejected :
    toyScheme.verify 11 (signingMessage 7 1 (.grant forgedGrant))
      honestRecord.signature = false := by
  decide

/-- The attack trace contains the honest record and the forged grant. -/
def attackReceived : SignedRecord toyScheme → Prop :=
  fun record => record = honestRecord ∨ record = forgedRecord

/-- The authenticity property is refutable on a concrete accepted forgery. -/
theorem attack_not_authentic :
    ¬ AuthenticIssuer toyScheme toyKeys noRevocations honestIssued attackReceived := by
  intro hauthentic
  exact forgedRecord_not_issued
    (hauthentic forgedRecord (Or.inr rfl) forgedRecord_accepted)

/-- Running the general extractor on the concrete attack produces the full
forgery-witness object. -/
theorem attack_extracts_forgery :
    ∃ w : ForgeryWitness toyScheme toyKeys noRevocations honestIssued,
      attackReceived w.record :=
  authenticity_violation_extracts_forgery attack_not_authentic

/-- The deliberately insecure toy scheme fails the EUF-style premise on the
attack trace; this is why correctness alone never licenses authenticity. -/
theorem toy_euf_style_refuted :
    ¬ EUFStylePremise toyScheme toyKeys noRevocations honestIssued attackReceived := by
  intro heuf
  exact attack_not_authentic (eufStyle_implies_authenticIssuer heuf)

end Uwueave.Authenticity
