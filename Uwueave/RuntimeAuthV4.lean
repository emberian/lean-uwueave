/-
# Uwueave.RuntimeAuthV4 — an honest authenticated FORMAT-v4 foundation

This module specifies the smallest byte-level record which could sit in front
of `Exec` without confusing authentication with authorization or persistence.
It is deliberately not wired into the shipping FORMAT v3 entry point.

The signed bytes bind a document id, genesis id, signature-algorithm tag,
issuer, key epoch, nonce, one move payload, stable operation/node ids, and the
exact numeric fields later projected into `Exec.Op`.  There is no independent
actor field: the kernel replica is definitionally the signed issuer.  Every
variable-length identifier is length-prefixed by the reused artifact wire
codec; every field has a distinct tag; and the whole record has magic, version,
and kind bytes.

`Verified` is an explicit deployment premise over the exact signing bytes and
signature bytes.  No theorem here claims signature unforgeability, key
ownership, authorization, membership, execution by compiled code, successful
append, flush behavior, or crash durability.  Those stages remain separate
premises and outcomes below.
-/
import Uwueave.Exec
import Uwueave.Preo.ArtifactDurable

namespace Uwueave.RuntimeAuthV4

open Uwueave
open Uwueave.Preo.ArtifactDurable

set_option autoImplicit false

abbrev Bytes := Durable.Bytes
abbrev StableId := Bytes
abbrev SignatureBytes := Bytes

/-! ## §1. Reusable tagged prefix codecs -/

/-- Parse an exact constant prefix and return the unconsumed suffix. -/
def parsePrefix : Bytes → Bytes → Option Bytes
  | [], bytes => some bytes
  | _ :: _, [] => none
  | expected :: rest, actual :: bytes =>
      if actual = expected then parsePrefix rest bytes else none

theorem parsePrefix_append (framing trailing : Bytes) :
    parsePrefix framing (framing ++ trailing) = some trailing := by
  induction framing with
  | nil => rfl
  | cons byte rest ih => simp [parsePrefix, ih]

/-- Put an exact constant prefix in front of any compositional wire codec. -/
def prefixedWire {α : Type} (framing : Bytes) (codec : WireCodec α) :
    WireCodec α where
  encode value := framing ++ codec.encode value
  parse bytes := do
    let trailing ← parsePrefix framing bytes
    codec.parse trailing
  parse_encode_append := by
    intro value trailing
    simp [List.append_assoc, parsePrefix_append, codec.parse_encode_append]

/-- A one-byte field tag.  The value codec supplies its own unambiguous end or
length; in particular `stableIdWire` below is explicitly length-prefixed. -/
def fieldWire {α : Type} (tag : UInt8) (codec : WireCodec α) : WireCodec α :=
  prefixedWire [tag] codec

/-- Stable ids are arbitrary bytes with a canonical unary length followed by
exactly that many literal bytes. -/
def stableIdWire : WireCodec StableId := WireCodec.list byteWire

/-- UInt64 values use their exact natural value.  The retraction is lossless
because `toNat` is injective on UInt64. -/
def uint64Wire : WireCodec UInt64 :=
  natWire.xmap UInt64.toNat UInt64.ofNat (by intro value; simp)

/-! ## §2. The one signed move record -/

/-- A stable node identity paired with the current request-local index which
the FORMAT v3 execution kernel consumes.  A deployment must separately prove
that its resolver gave this stable id this index for the bound document and
genesis. -/
structure NodeRef where
  stable : StableId
  kernelIndex : Nat
  deriving DecidableEq, Repr

def nodeRefWire : WireCodec NodeRef :=
  ((fieldWire 49 stableIdWire).prod (fieldWire 50 natWire)).xmap
    (fun node => (node.stable, node.kernelIndex))
    (fun raw => ⟨raw.1, raw.2⟩)
    (by intro node; cases node; rfl)

/-- The only v4 payload presently admitted.  There is intentionally no actor
or replica field.  `operationId`, `child.stable`, and the destination stable
id are signed even though FORMAT v3 currently executes request-local indices. -/
structure MovePayload where
  operationId : StableId
  lamport : UInt64
  child : NodeRef
  dest : Option NodeRef
  cite : Nat
  deriving DecidableEq, Repr

private abbrev MoveRaw :=
  StableId × (UInt64 × (NodeRef × (Option NodeRef × Nat)))

def movePayloadWire : WireCodec MovePayload :=
  ((fieldWire 65 stableIdWire).prod
    ((fieldWire 66 uint64Wire).prod
      ((fieldWire 67 nodeRefWire).prod
        ((fieldWire 68 (WireCodec.option nodeRefWire)).prod
          (fieldWire 69 natWire))))).xmap
    (fun move : MovePayload =>
      (move.operationId, (move.lamport, (move.child, (move.dest, move.cite)))))
    (fun raw : MoveRaw =>
      ⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2⟩)
    (by intro move; cases move; rfl)

/-- Everything covered by the signature.  Document and genesis are separate:
an operation from another document or another genesis cannot be substituted. -/
structure SignedContent where
  document : StableId
  genesis : StableId
  signatureAlgorithm : UInt8
  issuer : UInt64
  keyEpoch : UInt64
  nonce : StableId
  move : MovePayload
  deriving DecidableEq, Repr

private abbrev ContentRaw :=
  StableId ×
    (StableId × (UInt8 × (UInt64 × (UInt64 × (StableId × MovePayload)))))

def signedContentWire : WireCodec SignedContent :=
  ((fieldWire 81 stableIdWire).prod
    ((fieldWire 82 stableIdWire).prod
      ((fieldWire 83 byteWire).prod
        ((fieldWire 84 uint64Wire).prod
          ((fieldWire 85 uint64Wire).prod
            ((fieldWire 86 stableIdWire).prod
              (fieldWire 87 movePayloadWire))))))).xmap
    (fun content : SignedContent =>
      (content.document,
        (content.genesis,
          (content.signatureAlgorithm,
            (content.issuer, (content.keyEpoch, (content.nonce, content.move)))))))
    (fun raw : ContentRaw =>
      ⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2.1,
        raw.2.2.2.2.2.1, raw.2.2.2.2.2.2⟩)
    (by intro content; cases content; rfl)

/-- Neutral signature bytes accompany, but are not part of, the signing
message.  Their interpretation belongs to `VerificationBoundary`. -/
structure SignedRequest where
  content : SignedContent
  signature : SignatureBytes
  deriving DecidableEq, Repr

def requestPayloadWire : WireCodec SignedRequest :=
  ((fieldWire 97 signedContentWire).prod
    (fieldWire 98 stableIdWire)).xmap
    (fun request => (request.content, request.signature))
    (fun raw => ⟨raw.1, raw.2⟩)
    (by intro request; cases request; rfl)

/-- ASCII-ish `UWV4`; a framing constant, not a digest. -/
def protocolMagic : Bytes := [85, 87, 86, 52]
def versionV4 : UInt8 := 4
def moveKind : UInt8 := 1
def responseKind : UInt8 := 2

def requestPrefixAt (version kind : UInt8) : Bytes :=
  protocolMagic ++ [version, kind]

def requestWireAt (version kind : UInt8) : WireCodec SignedRequest :=
  prefixedWire (requestPrefixAt version kind) requestPayloadWire

def requestCodecAt (version kind : UInt8) : Durable.CanonicalCodec SignedRequest :=
  canonicalCodecOfWire (requestWireAt version kind)

def requestCodecV4 : Durable.CanonicalCodec SignedRequest :=
  requestCodecAt versionV4 moveKind

def encodeRequestAt (version kind : UInt8) (request : SignedRequest) : Bytes :=
  (requestCodecAt version kind).encode request

def encodeRequestV4 (request : SignedRequest) : Bytes :=
  requestCodecV4.encode request

/-- The exact bytes submitted to signature verification: the complete v4
prefix and signed content, excluding the signature field itself. -/
def signingCodecAt (version kind : UInt8) :
    Durable.CanonicalCodec SignedContent :=
  canonicalCodecOfWire
    (prefixedWire (requestPrefixAt version kind)
      (fieldWire 97 signedContentWire))

def signingBytesAt (version kind : UInt8) (content : SignedContent) : Bytes :=
  (signingCodecAt version kind).encode content

def signingBytesV4 : SignedContent → Bytes := signingBytesAt versionV4 moveKind

theorem request_roundtrip (request : SignedRequest) :
    requestCodecV4.decode (encodeRequestV4 request) = some request :=
  requestCodecV4.decode_encode request

theorem request_encode_injective : Function.Injective encodeRequestV4 := by
  intro left right h
  apply Option.some.inj
  calc
    some left = requestCodecV4.decode (encodeRequestV4 left) :=
      (request_roundtrip left).symm
    _ = requestCodecV4.decode (encodeRequestV4 right) := congrArg _ h
    _ = some right := request_roundtrip right

theorem signing_roundtrip (content : SignedContent) :
    (signingCodecAt versionV4 moveKind).decode (signingBytesV4 content) =
      some content :=
  (signingCodecAt versionV4 moveKind).decode_encode content

/-- Equality of v4 signing bytes pins every signed field, independently of
signature interpretation. -/
theorem signingBytesV4_injective : Function.Injective signingBytesV4 := by
  intro left right h
  apply Option.some.inj
  calc
    some left = (signingCodecAt versionV4 moveKind).decode
        (signingBytesV4 left) := (signing_roundtrip left).symm
    _ = (signingCodecAt versionV4 moveKind).decode
        (signingBytesV4 right) := congrArg _ h
    _ = some right := signing_roundtrip right

theorem signing_cross_document_separated {left right : SignedContent}
    (hdocument : left.document ≠ right.document) :
    signingBytesV4 left ≠ signingBytesV4 right := by
  intro hbytes
  apply hdocument
  exact congrArg SignedContent.document (signingBytesV4_injective hbytes)

/-- Changing the document while holding the remaining record arbitrary changes
the canonical record bytes. -/
theorem cross_document_separated {left right : SignedRequest}
    (hdocument : left.content.document ≠ right.content.document) :
    encodeRequestV4 left ≠ encodeRequestV4 right := by
  intro hbytes
  apply hdocument
  exact congrArg (fun request => request.content.document)
    (request_encode_injective hbytes)

/-- Version bytes cannot alias, independently of record contents. -/
theorem cross_version_separated {version version' kind : UInt8}
    (hversion : version ≠ version') (left right : SignedRequest) :
    encodeRequestAt version kind left ≠ encodeRequestAt version' kind right := by
  intro hbytes
  have atVersion := congrArg (fun bytes : Bytes => bytes[4]?) hbytes
  apply hversion
  simpa [encodeRequestAt, requestCodecAt, canonicalCodecOfWire, requestWireAt,
    prefixedWire, requestPrefixAt, protocolMagic] using atVersion

/-- Object-kind bytes cannot alias, independently of record contents. -/
theorem cross_kind_separated {version kind kind' : UInt8}
    (hkind : kind ≠ kind') (left right : SignedRequest) :
    encodeRequestAt version kind left ≠ encodeRequestAt version kind' right := by
  intro hbytes
  have atKind := congrArg (fun bytes : Bytes => bytes[5]?) hbytes
  apply hkind
  simpa [encodeRequestAt, requestCodecAt, canonicalCodecOfWire, requestWireAt,
    prefixedWire, requestPrefixAt, protocolMagic] using atKind

/-! ## §3. Bounded syntax and semantic-shape refusal -/

inductive DecodeRefusal where
  | tooLarge
  | badMagic
  | unsupportedVersion
  | wrongKind
  | malformed
  deriving DecidableEq, Repr

inductive DecodeOutcome where
  | refused (reason : DecodeRefusal)
  | accepted (request : SignedRequest)
  deriving DecidableEq, Repr

/-- Header classification runs before the canonical parser so version and kind
fail loudly instead of collapsing into a generic malformed result. -/
def headerRefusal? (bytes : Bytes) : Option DecodeRefusal :=
  if bytes.take protocolMagic.length ≠ protocolMagic then some .badMagic
  else if bytes[protocolMagic.length]? ≠ some versionV4 then
    some .unsupportedVersion
  else if bytes[protocolMagic.length + 1]? ≠ some moveKind then
    some .wrongKind
  else none

/-- The parser is entered only after an explicit input-size bound.  This is a
logical control over the supplied list; it is not a claim about host allocation
before bytes reach Lean. -/
def decodeBounded (maximumBytes : Nat) (bytes : Bytes) : DecodeOutcome :=
  if bytes.length ≤ maximumBytes then
    match headerRefusal? bytes with
    | some reason => .refused reason
    | none =>
        match requestCodecV4.decode bytes with
        | none => .refused .malformed
        | some request => .accepted request
  else
    .refused .tooLarge

theorem bounded_roundtrip (maximumBytes : Nat) (request : SignedRequest)
    (hbound : (encodeRequestV4 request).length ≤ maximumBytes) :
    decodeBounded maximumBytes (encodeRequestV4 request) = .accepted request := by
  unfold decodeBounded
  rw [if_pos hbound]
  have hheader : headerRefusal? (encodeRequestV4 request) = none := by
    simp [headerRefusal?, encodeRequestV4, requestCodecV4, requestCodecAt,
      canonicalCodecOfWire, requestWireAt, prefixedWire, requestPrefixAt,
      protocolMagic, versionV4, moveKind]
  rw [hheader, request_roundtrip]

theorem oversized_refused (maximumBytes : Nat) (bytes : Bytes)
    (h : ¬ bytes.length ≤ maximumBytes) :
    decodeBounded maximumBytes bytes = .refused .tooLarge := by
  simp [decodeBounded, h]

inductive ShapeRefusal where
  | emptyDocument
  | emptyGenesis
  | emptyNonce
  | emptyOperationId
  | emptyChildId
  | emptyDestinationId
  | emptySignature
  deriving DecidableEq, Repr

/-- Syntax roundtrips empty byte strings because they are canonical lists;
runtime admission refuses every identifier/signature whose semantic role
requires nonemptiness. -/
def validateShape (request : SignedRequest) : Except ShapeRefusal SignedRequest :=
  if request.content.document.isEmpty then .error .emptyDocument
  else if request.content.genesis.isEmpty then .error .emptyGenesis
  else if request.content.nonce.isEmpty then .error .emptyNonce
  else if request.content.move.operationId.isEmpty then .error .emptyOperationId
  else if request.content.move.child.stable.isEmpty then .error .emptyChildId
  else match request.content.move.dest with
    | some destination =>
        if destination.stable.isEmpty then .error .emptyDestinationId
        else if request.signature.isEmpty then .error .emptySignature
        else .ok request
    | none =>
        if request.signature.isEmpty then .error .emptySignature
        else .ok request

/-! ## §4. Verification and nonce boundaries -/

/-- A deployment chooses what it means for signature bytes to verify.  This
module only passes the exact canonical signing bytes and signature bytes to
that relation. -/
structure VerificationBoundary where
  Accepts : UInt8 → Bytes → SignatureBytes → Prop

/-- `Verified` has no constructor derived from bytes alone.  A caller must
provide the verification-boundary premise for the exact v4 message. -/
structure Verified (boundary : VerificationBoundary)
    (request : SignedRequest) : Prop where
  accepted : boundary.Accepts request.content.signatureAlgorithm
    (signingBytesV4 request.content) request.signature

structure NonceKey where
  document : StableId
  genesis : StableId
  issuer : UInt64
  keyEpoch : UInt64
  nonce : StableId
  deriving DecidableEq, Repr

def nonceKey (request : SignedRequest) : NonceKey :=
  ⟨request.content.document, request.content.genesis, request.content.issuer,
    request.content.keyEpoch, request.content.nonce⟩

/-- Same scoped nonce and exactly the same signed content is a duplicate
delivery.  Signature bytes are intentionally not compared: randomized or
re-wrapped signatures over identical content remain one replay. -/
def NonceReplay (prior current : SignedRequest) : Prop :=
  nonceKey prior = nonceKey current ∧ prior.content = current.content

/-- Same scoped nonce bound to any different signed-content field is an
explicit collision.  This includes algorithm, ids, and move fields. -/
def NonceCollision (prior current : SignedRequest) : Prop :=
  nonceKey prior = nonceKey current ∧ prior.content ≠ current.content

inductive NonceDecision where
  | fresh
  | replay
  | collision
  deriving DecidableEq, Repr

def compareNonce (prior current : SignedRequest) : NonceDecision :=
  if nonceKey prior = nonceKey current then
    if prior.content = current.content then .replay else .collision
  else .fresh

theorem compareNonce_replay_iff (prior current : SignedRequest) :
    compareNonce prior current = .replay ↔ NonceReplay prior current := by
  unfold compareNonce NonceReplay
  by_cases hkey : nonceKey prior = nonceKey current
  · by_cases hcontent : prior.content = current.content <;>
      simp [hkey, hcontent]
  · simp [hkey]

theorem compareNonce_collision_iff (prior current : SignedRequest) :
    compareNonce prior current = .collision ↔ NonceCollision prior current := by
  unfold compareNonce NonceCollision
  by_cases hkey : nonceKey prior = nonceKey current
  · by_cases hcontent : prior.content = current.content <;>
      simp [hkey, hcontent]
  · simp [hkey]

def NonceFresh (seen : List SignedRequest) (request : SignedRequest) : Prop :=
  ∀ prior ∈ seen, nonceKey prior ≠ nonceKey request

/-! ## §5. Exact projection to the current kernel -/

def destinationIndex : Option NodeRef → Int
  | none => -1
  | some node => Int.ofNat node.kernelIndex

/-- The v4-authenticated move projected into all five FORMAT-v3 `Exec.Op`
fields.  Stable ids are resolved before this projection; no signed numeric
kernel field is guessed or supplied out of band. -/
def toExecOp (request : SignedRequest) : Exec.Op where
  lamport := request.content.move.lamport
  replica := request.content.issuer
  child := request.content.move.child.kernelIndex
  dest := destinationIndex request.content.move.dest
  cite := request.content.move.cite

theorem toExecOp_exact_fields (request : SignedRequest) :
    (toExecOp request).lamport = request.content.move.lamport
      ∧ (toExecOp request).replica = request.content.issuer
      ∧ (toExecOp request).child = request.content.move.child.kernelIndex
      ∧ (toExecOp request).dest = destinationIndex request.content.move.dest
      ∧ (toExecOp request).cite = request.content.move.cite := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- There is no actor/replica ambiguity: the execution replica is the issuer
whose identity occurs in the signed content. -/
theorem replica_is_signed_issuer (request : SignedRequest) :
    (toExecOp request).replica = request.content.issuer := rfl

/-- Resolution of stable ids is also an explicit premise, scoped to the
signed document and genesis. -/
structure ResolverBoundary where
  Resolve : StableId → StableId → StableId → Option Nat

structure Resolved (resolver : ResolverBoundary)
    (request : SignedRequest) : Prop where
  child : resolver.Resolve request.content.document request.content.genesis
      request.content.move.child.stable =
    some request.content.move.child.kernelIndex
  destination : ∀ node ∈ request.content.move.dest,
    resolver.Resolve request.content.document request.content.genesis node.stable =
      some node.kernelIndex

/-! ## §6. Layered runtime outcomes and premise receipts -/

inductive AuthenticityOutcome where
  | notChecked
  | refused
  | verified
  deriving DecidableEq, Repr

inductive AuthorityOutcome where
  | notChecked
  | refused
  | permitted
  deriving DecidableEq, Repr

inductive MembershipOutcome where
  | notChecked
  | refused
  | member
  deriving DecidableEq, Repr

inductive ExecutionOutcome where
  | notAttempted
  | refused
  | executed
  deriving DecidableEq, Repr

inductive StorageOutcome where
  | notAttempted
  | appendRefused
  | appended
  | durabilityPremiseAccepted
  deriving DecidableEq, Repr

structure LayeredOutcome where
  authenticity : AuthenticityOutcome
  authority : AuthorityOutcome
  membership : MembershipOutcome
  execution : ExecutionOutcome
  storage : StorageOutcome
  deriving DecidableEq, Repr

/-- A trace is well-layered when downstream success implies every upstream
success.  This is a predicate to enforce, not a theorem about arbitrary host
traces. -/
def WellLayered (outcome : LayeredOutcome) : Prop :=
  (outcome.authority = .permitted → outcome.authenticity = .verified)
    ∧ (outcome.membership = .member → outcome.authenticity = .verified)
    ∧ (outcome.execution = .executed →
        outcome.authenticity = .verified
          ∧ outcome.authority = .permitted
          ∧ outcome.membership = .member)
    ∧ ((outcome.storage = .appended ∨
        outcome.storage = .durabilityPremiseAccepted) →
          outcome.execution = .executed)

/-- The independent semantic premises required before invoking `Exec`. -/
structure ReadyForExecution (boundary : VerificationBoundary)
    (resolver : ResolverBoundary) (authority membership : SignedRequest → Prop)
    (seen : List SignedRequest) (request : SignedRequest) : Prop where
  verified : Verified boundary request
  resolved : Resolved resolver request
  fresh : NonceFresh seen request
  authorized : authority request
  isMember : membership request

/-- Storage and durability are deployment predicates over the exact canonical
record bytes.  The latter is not derived from the former. -/
structure StorageBoundary where
  Appended : Bytes → Prop
  DurableObservation : Bytes → Prop

structure StorageReceipt (storage : StorageBoundary)
    (request : SignedRequest) : Prop where
  appended : storage.Appended (encodeRequestV4 request)
  durablePremise : storage.DurableObservation (encodeRequestV4 request)

/-! ## §7. Versioned response and negative fixtures -/

inductive ResponseCode where
  | accepted
  | decodeRefused
  | authenticityRefused
  | nonceRefused
  | authorityRefused
  | membershipRefused
  | executionRefused
  | storageRefused
  deriving DecidableEq, Repr

def responseCodeTag : ResponseCode → UInt8
  | .accepted => 0
  | .decodeRefused => 1
  | .authenticityRefused => 2
  | .nonceRefused => 3
  | .authorityRefused => 4
  | .membershipRefused => 5
  | .executionRefused => 6
  | .storageRefused => 7

/-- Unlike FORMAT v3's empty refusal, every v4 response is nonempty and binds
the response kind and format version. -/
def encodeResponse (code : ResponseCode) : Bytes :=
  protocolMagic ++ [versionV4, responseKind, responseCodeTag code]

theorem response_nonempty (code : ResponseCode) : encodeResponse code ≠ [] := by
  simp [encodeResponse, protocolMagic]

theorem response_binds_version (code : ResponseCode) :
    (encodeResponse code)[4]? = some versionV4 := by
  simp [encodeResponse, protocolMagic]

def fixtureNodeA : NodeRef := ⟨[10, 11], 3⟩
def fixtureNodeB : NodeRef := ⟨[12, 13], 4⟩

def fixtureMove : MovePayload :=
  ⟨[21], 9, fixtureNodeA, some fixtureNodeB, 7⟩

def fixtureContent : SignedContent :=
  ⟨[1, 2], [3, 4], 1, 17, 2, [5, 6], fixtureMove⟩

def fixtureRequest : SignedRequest := ⟨fixtureContent, [99, 100]⟩

def otherDocumentRequest : SignedRequest :=
  ⟨{ fixtureContent with document := [8, 8] }, fixtureRequest.signature⟩

def otherGenesisRequest : SignedRequest :=
  ⟨{ fixtureContent with genesis := [9, 9] }, fixtureRequest.signature⟩

def otherIssuerRequest : SignedRequest :=
  ⟨{ fixtureContent with issuer := 18 }, fixtureRequest.signature⟩

def otherAlgorithmRequest : SignedRequest :=
  ⟨{ fixtureContent with signatureAlgorithm := 2 }, fixtureRequest.signature⟩

def otherEpochRequest : SignedRequest :=
  ⟨{ fixtureContent with keyEpoch := 3 }, fixtureRequest.signature⟩

def otherNonceRequest : SignedRequest :=
  ⟨{ fixtureContent with nonce := [5, 7] }, fixtureRequest.signature⟩

def otherChildIdentityRequest : SignedRequest :=
  ⟨{ fixtureContent with move :=
      { fixtureMove with child := ⟨[10, 12], fixtureNodeA.kernelIndex⟩ } },
    fixtureRequest.signature⟩

def collidingNonceRequest : SignedRequest :=
  ⟨{ fixtureContent with move := { fixtureMove with cite := 8 } },
    fixtureRequest.signature⟩

def alternateSignatureRequest : SignedRequest :=
  ⟨fixtureContent, [101, 102, 103]⟩

theorem fixture_roundtrip :
    requestCodecV4.decode (encodeRequestV4 fixtureRequest) = some fixtureRequest :=
  request_roundtrip fixtureRequest

theorem fixture_document_substitution_refused :
    encodeRequestV4 fixtureRequest ≠ encodeRequestV4 otherDocumentRequest := by
  apply cross_document_separated
  decide

theorem fixture_genesis_substitution_changes_bytes :
    encodeRequestV4 fixtureRequest ≠ encodeRequestV4 otherGenesisRequest := by
  intro h
  have equal := request_encode_injective h
  have := congrArg (fun request => request.content.genesis) equal
  contradiction

theorem fixture_issuer_substitution_changes_bytes :
    encodeRequestV4 fixtureRequest ≠ encodeRequestV4 otherIssuerRequest := by
  intro h
  have equal := request_encode_injective h
  have := congrArg (fun request => request.content.issuer) equal
  contradiction

theorem fixture_algorithm_substitution_changes_signing_bytes :
    signingBytesV4 fixtureRequest.content ≠
      signingBytesV4 otherAlgorithmRequest.content := by
  intro h
  have equal := signingBytesV4_injective h
  have := congrArg SignedContent.signatureAlgorithm equal
  contradiction

theorem fixture_epoch_substitution_changes_signing_bytes :
    signingBytesV4 fixtureRequest.content ≠
      signingBytesV4 otherEpochRequest.content := by
  intro h
  have equal := signingBytesV4_injective h
  have := congrArg SignedContent.keyEpoch equal
  contradiction

theorem fixture_nonce_substitution_changes_signing_bytes :
    signingBytesV4 fixtureRequest.content ≠
      signingBytesV4 otherNonceRequest.content := by
  intro h
  have equal := signingBytesV4_injective h
  have := congrArg SignedContent.nonce equal
  contradiction

/-- Stable ids are signed even when a malicious request keeps the same
request-local kernel index. -/
theorem fixture_child_id_substitution_changes_signing_bytes :
    signingBytesV4 fixtureRequest.content ≠
      signingBytesV4 otherChildIdentityRequest.content := by
  intro h
  have equal := signingBytesV4_injective h
  have := congrArg (fun content => content.move.child.stable) equal
  contradiction

theorem fixture_cross_version_refused :
    encodeRequestAt 4 moveKind fixtureRequest ≠
      encodeRequestAt 3 moveKind fixtureRequest := by
  apply cross_version_separated
  decide

theorem fixture_cross_kind_refused :
    encodeRequestAt versionV4 moveKind fixtureRequest ≠
      encodeRequestAt versionV4 responseKind fixtureRequest := by
  apply cross_kind_separated
  decide

theorem fixture_nonce_collision :
    NonceCollision fixtureRequest collidingNonceRequest := by
  simp [NonceCollision, nonceKey, fixtureRequest, collidingNonceRequest,
    fixtureContent, fixtureMove]

theorem fixture_nonce_collision_is_not_replay :
    ¬ NonceReplay fixtureRequest collidingNonceRequest := by
  simp [NonceReplay, nonceKey, fixtureRequest, collidingNonceRequest,
    fixtureContent, fixtureMove]

theorem fixture_nonce_collision_classified :
    compareNonce fixtureRequest collidingNonceRequest = .collision := by
  decide

/-- Different signature bytes over exactly the same signed content remain a
replay, not a nonce collision. -/
theorem alternate_signature_is_replay :
    NonceReplay fixtureRequest alternateSignatureRequest := by
  simp [NonceReplay, nonceKey, fixtureRequest, alternateSignatureRequest]

theorem alternate_signature_is_not_collision :
    ¬ NonceCollision fixtureRequest alternateSignatureRequest := by
  simp [NonceCollision, fixtureRequest, alternateSignatureRequest]

theorem empty_request_bad_magic :
    decodeBounded 1024 [] = .refused .badMagic := by
  decide

theorem old_version_refused :
    decodeBounded (encodeRequestAt 3 moveKind fixtureRequest).length
      (encodeRequestAt 3 moveKind fixtureRequest) =
        .refused .unsupportedVersion := by
  simp [decodeBounded, headerRefusal?, encodeRequestAt, requestCodecAt,
    canonicalCodecOfWire, requestWireAt, prefixedWire, requestPrefixAt,
    protocolMagic, versionV4]

theorem wrong_kind_refused :
    decodeBounded (encodeRequestAt versionV4 responseKind fixtureRequest).length
      (encodeRequestAt versionV4 responseKind fixtureRequest) =
        .refused .wrongKind := by
  simp [decodeBounded, headerRefusal?, encodeRequestAt, requestCodecAt,
    canonicalCodecOfWire, requestWireAt, prefixedWire, requestPrefixAt,
    protocolMagic, versionV4, moveKind, responseKind]

def emptyNonceRequest : SignedRequest :=
  ⟨{ fixtureContent with nonce := [] }, fixtureRequest.signature⟩

theorem empty_nonce_shape_refused :
    validateShape emptyNonceRequest = .error .emptyNonce := by
  simp [validateShape, emptyNonceRequest, fixtureContent]

theorem fixture_replica_has_no_independent_actor :
    (toExecOp fixtureRequest).replica = fixtureContent.issuer := rfl

end Uwueave.RuntimeAuthV4
