/-
# Uwueave.RuntimeAuthV4Kernel — context-bound FORMAT-v4 admission projection

This leaf owns a context-bound signed request kind for runtime admission.
Unlike the legacy kind-1 syntax record, kind 3 signs a nonempty context
commitment so a host can select the exact historical resolver/authority
substrate.  The executable endpoint performs bounded canonical decoding,
semantic shape checks, and exact FORMAT-v3 word-representability checks.  On
success it emits a canonical, self-decoding projection for later host stages.

Canonical kind-3 requests and kind-4 projections encode the move's `lamport`
timestamp as an exact 8-byte little-endian `UInt64` (tag `70` in kind 3, tag
`179` in kind 4), making signed request size, projection size, and stack depth
strictly independent of Lamport clock magnitude.  Legacy unary `lamport`
encodings (tag `66` in kind 3, tag `172` in kind 4) remain decodable under a
disjoint tag grammar so existing signed fixtures and pre-existing journals
verify and recover against their original byte-exact signing and projection
domains.

This module does not interpret the context commitment, authenticate a
signature, resolve a stable id, decide nonce freshness, authorize, execute, or
persist.  Its `accepted` outcome is not `RuntimeAuthV4.ReadyForExecution`.
-/
import Uwueave.RuntimeAuthV4

namespace Uwueave.RuntimeAuthV4Kernel

open Uwueave
open Uwueave.Preo.ArtifactDurable
open Uwueave.RuntimeAuthV4

set_option autoImplicit false

abbrev Bytes := Durable.Bytes
abbrev StableId := RuntimeAuthV4.StableId
abbrev SignatureBytes := RuntimeAuthV4.SignatureBytes

/-- Conventional host default.  The export accepts the caller's exact bound. -/
def defaultMaximumRequestBytes : Nat := 1024 * 1024

/-- Kind 1 remains the legacy syntax-only request; kind 2 remains the existing
layered response.  Context-bound admission therefore uses request kind 3 and
projection-response kind 4. -/
def contextMoveKind : UInt8 := 3
def admissionResponseKind : UInt8 := 4

/-! ## Fixed-width 8-byte little-endian `UInt64` wire codec -/

/-- Canonical fixed-width 8-byte little-endian `UInt64` encoding.  Width and
stack usage are constant across the entire `UInt64` domain. -/
def encodeUInt64Le (value : UInt64) : Bytes :=
  let n0 := value.toNat
  let n1 := n0 / 256
  let n2 := n1 / 256
  let n3 := n2 / 256
  let n4 := n3 / 256
  let n5 := n4 / 256
  let n6 := n5 / 256
  let n7 := n6 / 256
  [ UInt8.ofNat (n0 % 256)
  , UInt8.ofNat (n1 % 256)
  , UInt8.ofNat (n2 % 256)
  , UInt8.ofNat (n3 % 256)
  , UInt8.ofNat (n4 % 256)
  , UInt8.ofNat (n5 % 256)
  , UInt8.ofNat (n6 % 256)
  , UInt8.ofNat (n7 % 256) ]

/-- Reassemble eight little-endian bytes into one `UInt64`. -/
def decodeUInt64Le8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  UInt64.ofNat
    (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 *
      (b3.toNat + 256 * (b4.toNat + 256 * (b5.toNat + 256 *
        (b6.toNat + 256 * b7.toNat)))))))

/-- Prefix parser for fixed-width 8-byte little-endian `UInt64` words. -/
def parseUInt64Le : Bytes → Option (UInt64 × Bytes)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: trailing =>
      some (decodeUInt64Le8 b0 b1 b2 b3 b4 b5 b6 b7, trailing)
  | _ => none

@[simp] theorem encodeUInt64Le_length (value : UInt64) :
    (encodeUInt64Le value).length = 8 := rfl

private theorem uint8_toNat_ofNat_mod (m : Nat) :
    (UInt8.ofNat (m % 256)).toNat = m % 256 := by
  rw [UInt8.toNat_ofNat']
  have hlt : m % 256 < 2 ^ 8 := by omega
  exact Nat.mod_eq_of_lt hlt

private theorem horner_uint64_roundtrip (n : Nat) (hn : n < 2 ^ 64) :
    let n1 := n / 256
    let n2 := n1 / 256
    let n3 := n2 / 256
    let n4 := n3 / 256
    let n5 := n4 / 256
    let n6 := n5 / 256
    let n7 := n6 / 256
    n % 256 + 256 * (n1 % 256 + 256 * (n2 % 256 + 256 *
      (n3 % 256 + 256 * (n4 % 256 + 256 * (n5 % 256 + 256 *
        (n6 % 256 + 256 * (n7 % 256))))))) = n := by
  dsimp only
  omega

theorem parseUInt64Le_encodeUInt64Le_append (value : UInt64) (trailing : Bytes) :
    parseUInt64Le (encodeUInt64Le value ++ trailing) = some (value, trailing) := by
  simp only [encodeUInt64Le, List.cons_append, List.nil_append, parseUInt64Le,
    decodeUInt64Le8, uint8_toNat_ofNat_mod]
  rw [horner_uint64_roundtrip value.toNat value.toBitVec.isLt, UInt64.ofNat_toNat]

def uint64LeWire : WireCodec UInt64 :=
  ⟨encodeUInt64Le, parseUInt64Le, parseUInt64Le_encodeUInt64Le_append⟩

def uint64LeCodec : Durable.CanonicalCodec UInt64 :=
  canonicalCodecOfWire uint64LeWire

theorem uint64LeCodec_roundtrip (value : UInt64) :
    uint64LeCodec.decode (encodeUInt64Le value) = some value :=
  uint64LeCodec.decode_encode value

theorem encodeUInt64Le_injective : Function.Injective encodeUInt64Le := by
  intro left right h
  apply Option.some.inj
  calc
    some left = uint64LeCodec.decode (encodeUInt64Le left) :=
      (uint64LeCodec_roundtrip left).symm
    _ = uint64LeCodec.decode (encodeUInt64Le right) := congrArg _ h
    _ = some right := uint64LeCodec_roundtrip right

/-! ## Lamport wire format and disjoint tag separation -/

/-- Wire encoding of `MovePayload.lamport` in kind-3 requests and kind-4
projections.  `.fixedLe` is the canonical compact 8-byte little-endian form
emitted by `encodeContextRequest` and `contextSigningBytes`; `.legacyUnary`
retains decode compatibility for pre-existing unary frames. -/
inductive LamportWireFormat where
  | fixedLe
  | legacyUnary
  deriving DecidableEq, Repr

def fixedLamportMoveTag : UInt8 := 70
def legacyLamportMoveTag : UInt8 := 66
def fixedLamportProjectionTag : UInt8 := 179
def legacyLamportProjectionTag : UInt8 := 172

def lamportMoveAnyWire : WireCodec (UInt64 × LamportWireFormat) where
  encode
    | (t, .fixedLe) => fixedLamportMoveTag :: encodeUInt64Le t
    | (t, .legacyUnary) => legacyLamportMoveTag :: uint64Wire.encode t
  parse
    | [] => none
    | tag :: rest =>
        if tag = fixedLamportMoveTag then
          match parseUInt64Le rest with
          | none => none
          | some (t, trailing) => some ((t, .fixedLe), trailing)
        else if tag = legacyLamportMoveTag then
          match uint64Wire.parse rest with
          | none => none
          | some (t, trailing) => some ((t, .legacyUnary), trailing)
        else none
  parse_encode_append := by
    intro ⟨t, fmt⟩ trailing
    cases fmt
    · simp [fixedLamportMoveTag, parseUInt64Le_encodeUInt64Le_append]
    · simp [fixedLamportMoveTag, legacyLamportMoveTag,
        uint64Wire.parse_encode_append]

private abbrev ContextMoveRaw :=
  StableId × (UInt64 × (NodeRef × (Option NodeRef × Nat)))

private abbrev ContextMoveAnyRaw :=
  StableId × ((UInt64 × LamportWireFormat) × (NodeRef × (Option NodeRef × Nat)))

/-- Canonical kind-3 move payload wire: tag `70` carries an 8-byte
little-endian `lamport` word. -/
def contextMovePayloadWire : WireCodec MovePayload :=
  ((fieldWire 65 stableIdWire).prod
    ((fieldWire fixedLamportMoveTag uint64LeWire).prod
      ((fieldWire 67 nodeRefWire).prod
        ((fieldWire 68 (WireCodec.option nodeRefWire)).prod
          (fieldWire 69 natWire))))).xmap
    (fun move : MovePayload =>
      (move.operationId, (move.lamport, (move.child, (move.dest, move.cite)))))
    (fun raw : ContextMoveRaw =>
      ⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2⟩)
    (by intro move; cases move; rfl)

/-- Format-preserving kind-3 move payload wire accepting either canonical
fixed-width tag `70` or legacy unary tag `66`. -/
def contextMovePayloadAnyWire : WireCodec (MovePayload × LamportWireFormat) :=
  ((fieldWire 65 stableIdWire).prod
    (lamportMoveAnyWire.prod
      ((fieldWire 67 nodeRefWire).prod
        ((fieldWire 68 (WireCodec.option nodeRefWire)).prod
          (fieldWire 69 natWire))))).xmap
    (fun pair : MovePayload × LamportWireFormat =>
      (pair.1.operationId,
        ((pair.1.lamport, pair.2),
          (pair.1.child, (pair.1.dest, pair.1.cite)))))
    (fun raw : ContextMoveAnyRaw =>
      (⟨raw.1, raw.2.1.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2⟩, raw.2.1.2))
    (by intro ⟨move, fmt⟩; cases move; rfl)

/-! ## Context-bound request and signing domain -/

/-- All legacy signed fields plus the stable commitment selecting the exact
historical deployment context against which resolution and authority must be
checked.  The bytes are opaque here: equality is meaningful, but no digest or
availability claim is manufactured. -/
structure ContextSignedContent where
  document : StableId
  genesis : StableId
  signatureAlgorithm : UInt8
  issuer : UInt64
  keyEpoch : UInt64
  nonce : StableId
  move : MovePayload
  contextCommitment : StableId
  deriving DecidableEq, Repr

private abbrev ContextContentRaw :=
  StableId × StableId × UInt8 × UInt64 × UInt64 × StableId ×
    MovePayload × StableId

private abbrev ContextContentAnyRaw :=
  StableId × StableId × UInt8 × UInt64 × UInt64 × StableId ×
    (MovePayload × LamportWireFormat) × StableId

/-- Tags `81..87` retain the legacy outer tags while tag `87` embeds
`contextMovePayloadWire` (fixed-width `lamport` under tag `70`); tag `88` is
the context commitment. -/
def contextSignedContentWire : WireCodec ContextSignedContent :=
  ((fieldWire 81 stableIdWire).prod
    ((fieldWire 82 stableIdWire).prod
      ((fieldWire 83 byteWire).prod
        ((fieldWire 84 uint64Wire).prod
          ((fieldWire 85 uint64Wire).prod
            ((fieldWire 86 stableIdWire).prod
              ((fieldWire 87 contextMovePayloadWire).prod
                (fieldWire 88 stableIdWire)))))))).xmap
    (fun content : ContextSignedContent =>
      (content.document,
        (content.genesis,
          (content.signatureAlgorithm,
            (content.issuer,
              (content.keyEpoch,
                (content.nonce, (content.move, content.contextCommitment))))))))
    (fun raw : ContextContentRaw =>
      ⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2.1,
        raw.2.2.2.2.2.1, raw.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2⟩)
    (by intro content; cases content; rfl)

def contextSignedContentAnyWire :
    WireCodec (ContextSignedContent × LamportWireFormat) :=
  ((fieldWire 81 stableIdWire).prod
    ((fieldWire 82 stableIdWire).prod
      ((fieldWire 83 byteWire).prod
        ((fieldWire 84 uint64Wire).prod
          ((fieldWire 85 uint64Wire).prod
            ((fieldWire 86 stableIdWire).prod
              ((fieldWire 87 contextMovePayloadAnyWire).prod
                (fieldWire 88 stableIdWire)))))))).xmap
    (fun pair : ContextSignedContent × LamportWireFormat =>
      let content := pair.1
      (content.document,
        (content.genesis,
          (content.signatureAlgorithm,
            (content.issuer,
              (content.keyEpoch,
                (content.nonce,
                  ((content.move, pair.2), content.contextCommitment))))))))
    (fun raw : ContextContentAnyRaw =>
      (⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2.1,
          raw.2.2.2.2.2.1, raw.2.2.2.2.2.2.1.1,
          raw.2.2.2.2.2.2.2⟩,
        raw.2.2.2.2.2.2.1.2))
    (by intro ⟨content, fmt⟩; cases content; rfl)

structure ContextSignedRequest where
  content : ContextSignedContent
  signature : SignatureBytes
  deriving DecidableEq, Repr

def ContextSignedContent.withLamport (content : ContextSignedContent)
    (lamport : UInt64) : ContextSignedContent :=
  { content with move := { content.move with lamport := lamport } }

def ContextSignedRequest.withLamport (request : ContextSignedRequest)
    (lamport : UInt64) : ContextSignedRequest :=
  { request with content := request.content.withLamport lamport }

def contextRequestPayloadWire : WireCodec ContextSignedRequest :=
  ((fieldWire 97 contextSignedContentWire).prod
    (fieldWire 98 stableIdWire)).xmap
    (fun request => (request.content, request.signature))
    (fun raw => ⟨raw.1, raw.2⟩)
    (by intro request; cases request; rfl)

def contextRequestPayloadAnyWire :
    WireCodec (ContextSignedRequest × LamportWireFormat) :=
  ((fieldWire 97 contextSignedContentAnyWire).prod
    (fieldWire 98 stableIdWire)).xmap
    (fun pair => ((pair.1.content, pair.2), pair.1.signature))
    (fun raw => (⟨raw.1.1, raw.2⟩, raw.1.2))
    (by intro ⟨request, fmt⟩; cases request; rfl)

def contextRequestWire : WireCodec ContextSignedRequest :=
  prefixedWire (requestPrefixAt versionV4 contextMoveKind)
    contextRequestPayloadWire

def contextRequestAnyWire :
    WireCodec (ContextSignedRequest × LamportWireFormat) :=
  prefixedWire (requestPrefixAt versionV4 contextMoveKind)
    contextRequestPayloadAnyWire

def contextRequestCodec : Durable.CanonicalCodec ContextSignedRequest :=
  canonicalCodecOfWire contextRequestWire

def contextRequestAnyCodec :
    Durable.CanonicalCodec (ContextSignedRequest × LamportWireFormat) :=
  canonicalCodecOfWire contextRequestAnyWire

def encodeContextRequestAt (fmt : LamportWireFormat)
    (request : ContextSignedRequest) : Bytes :=
  contextRequestAnyCodec.encode (request, fmt)

def encodeContextRequest (request : ContextSignedRequest) : Bytes :=
  contextRequestCodec.encode request

def encodeLegacyContextRequest (request : ContextSignedRequest) : Bytes :=
  encodeContextRequestAt .legacyUnary request

@[simp] theorem encodeContextRequestAt_fixedLe
    (request : ContextSignedRequest) :
    encodeContextRequestAt .fixedLe request = encodeContextRequest request :=
  rfl

/-- The exact kind-3 bytes submitted to a host verifier: prefix and all signed
content, excluding only tag `98` and the signature value. -/
def contextSigningWire : WireCodec ContextSignedContent :=
  prefixedWire (requestPrefixAt versionV4 contextMoveKind)
    (fieldWire 97 contextSignedContentWire)

def contextSigningAnyWire :
    WireCodec (ContextSignedContent × LamportWireFormat) :=
  prefixedWire (requestPrefixAt versionV4 contextMoveKind)
    (fieldWire 97 contextSignedContentAnyWire)

def contextSigningCodec : Durable.CanonicalCodec ContextSignedContent :=
  canonicalCodecOfWire contextSigningWire

def contextSigningAnyCodec :
    Durable.CanonicalCodec (ContextSignedContent × LamportWireFormat) :=
  canonicalCodecOfWire contextSigningAnyWire

def contextSigningBytesAt (fmt : LamportWireFormat)
    (content : ContextSignedContent) : Bytes :=
  contextSigningAnyCodec.encode (content, fmt)

def contextSigningBytes (content : ContextSignedContent) : Bytes :=
  contextSigningCodec.encode content

def legacyContextSigningBytes (content : ContextSignedContent) : Bytes :=
  contextSigningBytesAt .legacyUnary content

@[simp] theorem contextSigningBytesAt_fixedLe
    (content : ContextSignedContent) :
    contextSigningBytesAt .fixedLe content = contextSigningBytes content :=
  rfl

theorem contextRequest_roundtrip (request : ContextSignedRequest) :
    contextRequestCodec.decode (encodeContextRequest request) = some request :=
  contextRequestCodec.decode_encode request

theorem contextRequestAny_roundtrip (fmt : LamportWireFormat)
    (request : ContextSignedRequest) :
    contextRequestAnyCodec.decode (encodeContextRequestAt fmt request) =
      some (request, fmt) :=
  contextRequestAnyCodec.decode_encode (request, fmt)

theorem contextSigning_roundtrip (content : ContextSignedContent) :
    contextSigningCodec.decode (contextSigningBytes content) = some content :=
  contextSigningCodec.decode_encode content

theorem contextSigningAny_roundtrip (fmt : LamportWireFormat)
    (content : ContextSignedContent) :
    contextSigningAnyCodec.decode (contextSigningBytesAt fmt content) =
      some (content, fmt) :=
  contextSigningAnyCodec.decode_encode (content, fmt)

theorem encodeContextRequestAt_injective
    {fmt₁ fmt₂ : LamportWireFormat}
    {left right : ContextSignedRequest}
    (h : encodeContextRequestAt fmt₁ left = encodeContextRequestAt fmt₂ right) :
    left = right ∧ fmt₁ = fmt₂ := by
  have hdec : some (left, fmt₁) = some (right, fmt₂) := by
    calc
      some (left, fmt₁) =
          contextRequestAnyCodec.decode (encodeContextRequestAt fmt₁ left) :=
        (contextRequestAny_roundtrip fmt₁ left).symm
      _ = contextRequestAnyCodec.decode (encodeContextRequestAt fmt₂ right) :=
        congrArg _ h
      _ = some (right, fmt₂) := contextRequestAny_roundtrip fmt₂ right
  exact Prod.mk.inj (Option.some.inj hdec)

theorem contextSigningBytesAt_injective
    {fmt₁ fmt₂ : LamportWireFormat}
    {left right : ContextSignedContent}
    (h : contextSigningBytesAt fmt₁ left = contextSigningBytesAt fmt₂ right) :
    left = right ∧ fmt₁ = fmt₂ := by
  have hdec : some (left, fmt₁) = some (right, fmt₂) := by
    calc
      some (left, fmt₁) =
          contextSigningAnyCodec.decode (contextSigningBytesAt fmt₁ left) :=
        (contextSigningAny_roundtrip fmt₁ left).symm
      _ = contextSigningAnyCodec.decode (contextSigningBytesAt fmt₂ right) :=
        congrArg _ h
      _ = some (right, fmt₂) := contextSigningAny_roundtrip fmt₂ right
  exact Prod.mk.inj (Option.some.inj hdec)

theorem contextSigningBytes_injective :
    Function.Injective contextSigningBytes := by
  intro left right h
  exact (contextSigningBytesAt_injective (fmt₁ := .fixedLe) (fmt₂ := .fixedLe) h).1

/-- Canonical fixed-width kind-3 requests never alias legacy unary kind-3
requests, regardless of field contents. -/
theorem context_request_fixed_ne_legacy
    (left right : ContextSignedRequest) :
    encodeContextRequest left ≠ encodeLegacyContextRequest right := by
  intro h
  have hfmt := (encodeContextRequestAt_injective
    (fmt₁ := .fixedLe) (fmt₂ := .legacyUnary) h).2
  cases hfmt

/-- Canonical fixed-width kind-3 signing bytes never alias legacy unary kind-3
signing bytes, regardless of signed fields. -/
theorem context_signing_fixed_ne_legacy
    (left right : ContextSignedContent) :
    contextSigningBytes left ≠ legacyContextSigningBytes right := by
  intro h
  have hfmt := (contextSigningBytesAt_injective
    (fmt₁ := .fixedLe) (fmt₂ := .legacyUnary) h).2
  cases hfmt

/-- Canonical kind-3 request byte length is strictly independent of the
`lamport` clock value. -/
theorem encodeContextRequest_length_lamport_invariant
    (request : ContextSignedRequest) (t₁ t₂ : UInt64) :
    (encodeContextRequest (request.withLamport t₁)).length =
      (encodeContextRequest (request.withLamport t₂)).length := by
  simp [encodeContextRequest, ContextSignedRequest.withLamport,
    ContextSignedContent.withLamport, contextRequestCodec,
    canonicalCodecOfWire, contextRequestWire, contextRequestPayloadWire,
    contextSignedContentWire, contextMovePayloadWire, prefixedWire,
    RuntimeAuthV4.fieldWire, WireCodec.xmap, WireCodec.prod, uint64LeWire]

/-- Canonical kind-3 signing byte length is strictly independent of the
`lamport` clock value. -/
theorem contextSigningBytes_length_lamport_invariant
    (content : ContextSignedContent) (t₁ t₂ : UInt64) :
    (contextSigningBytes (content.withLamport t₁)).length =
      (contextSigningBytes (content.withLamport t₂)).length := by
  simp [contextSigningBytes, ContextSignedContent.withLamport,
    contextSigningCodec, canonicalCodecOfWire, contextSigningWire,
    contextSignedContentWire, contextMovePayloadWire, prefixedWire,
    RuntimeAuthV4.fieldWire, WireCodec.xmap, WireCodec.prod, uint64LeWire]

theorem context_commitment_is_signed {left right : ContextSignedContent}
    (hne : left.contextCommitment ≠ right.contextCommitment) :
    contextSigningBytes left ≠ contextSigningBytes right := by
  intro h
  exact hne (congrArg ContextSignedContent.contextCommitment
    (contextSigningBytes_injective h))

/-- Reading the object-kind byte is enough to separate context-bound requests
from every other format-v4 object kind, independently of payload bytes. -/
theorem context_request_at_kind_at_index (fmt : LamportWireFormat)
    (request : ContextSignedRequest) :
    (encodeContextRequestAt fmt request)[5]? = some contextMoveKind := by
  simp [encodeContextRequestAt, contextRequestAnyCodec, canonicalCodecOfWire,
    contextRequestAnyWire, prefixedWire, requestPrefixAt, protocolMagic]

theorem context_request_kind_at_index (request : ContextSignedRequest) :
    (encodeContextRequest request)[5]? = some contextMoveKind :=
  context_request_at_kind_at_index .fixedLe request

theorem context_request_separated_from_legacy (request : ContextSignedRequest)
    (legacy : SignedRequest) :
    encodeContextRequest request ≠ encodeRequestV4 legacy := by
  intro h
  have atKind := congrArg (fun bytes : Bytes => bytes[5]?) h
  simp [context_request_kind_at_index, encodeRequestV4, requestCodecV4,
    requestCodecAt, canonicalCodecOfWire, requestWireAt, prefixedWire,
    requestPrefixAt, protocolMagic, contextMoveKind, moveKind] at atKind

theorem context_request_separated_from_layered_response
    (request : ContextSignedRequest) (code : ResponseCode) :
    encodeContextRequest request ≠ encodeResponse code := by
  intro h
  have atKind := congrArg (fun bytes : Bytes => bytes[5]?) h
  simp [context_request_kind_at_index, encodeResponse, protocolMagic,
    contextMoveKind, responseKind] at atKind

/-! ## Decode, shape, and exact host-word checks -/

/-- Header classification is deliberately kind-3-specific.  A canonical
legacy kind-1 request is therefore `wrongKind`, never admission input. -/
def contextHeaderRefusal? (bytes : Bytes) : Option DecodeRefusal :=
  if bytes.take protocolMagic.length ≠ protocolMagic then some .badMagic
  else if bytes[protocolMagic.length]? ≠ some versionV4 then
    some .unsupportedVersion
  else if bytes[protocolMagic.length + 1]? ≠ some contextMoveKind then
    some .wrongKind
  else none

/-- The runtime-facing decoder retains the context-bound request directly;
the legacy model's `DecodeOutcome` intentionally continues to carry only its
kind-1 `SignedRequest`. -/
inductive ContextDecodeOutcome where
  | refused (reason : DecodeRefusal)
  | accepted (request : ContextSignedRequest)
  deriving DecidableEq, Repr

/-- Format-preserving decode outcome retaining whether the accepted canonical
kind-3 frame used `.fixedLe` (tag `70`) or `.legacyUnary` (tag `66`). -/
inductive FormattedContextDecodeOutcome where
  | refused (reason : DecodeRefusal)
  | accepted (format : LamportWireFormat) (request : ContextSignedRequest)
  deriving DecidableEq, Repr

def FormattedContextDecodeOutcome.toOutcome :
    FormattedContextDecodeOutcome → ContextDecodeOutcome
  | .refused reason => .refused reason
  | .accepted _ request => .accepted request

def decodeContextRequestWithFormatBounded (maximumBytes : Nat) (bytes : Bytes) :
    FormattedContextDecodeOutcome :=
  if bytes.length ≤ maximumBytes then
    match contextHeaderRefusal? bytes with
    | some reason => .refused reason
    | none =>
        match contextRequestAnyCodec.decode bytes with
        | none => .refused .malformed
        | some (request, fmt) => .accepted fmt request
  else
    .refused .tooLarge

def decodeContextRequestBounded (maximumBytes : Nat) (bytes : Bytes) :
    ContextDecodeOutcome :=
  (decodeContextRequestWithFormatBounded maximumBytes bytes).toOutcome

theorem context_bounded_at_roundtrip (fmt : LamportWireFormat)
    (maximumBytes : Nat) (request : ContextSignedRequest)
    (hbound : (encodeContextRequestAt fmt request).length ≤ maximumBytes) :
    decodeContextRequestWithFormatBounded maximumBytes
        (encodeContextRequestAt fmt request) =
      .accepted fmt request := by
  unfold decodeContextRequestWithFormatBounded
  rw [if_pos hbound]
  have hheader :
      contextHeaderRefusal? (encodeContextRequestAt fmt request) = none := by
    simp [contextHeaderRefusal?, encodeContextRequestAt, contextRequestAnyCodec,
      canonicalCodecOfWire, contextRequestAnyWire, prefixedWire,
      requestPrefixAt, protocolMagic, versionV4, contextMoveKind]
  rw [hheader, contextRequestAny_roundtrip]

theorem context_bounded_roundtrip (maximumBytes : Nat)
    (request : ContextSignedRequest)
    (hbound : (encodeContextRequest request).length ≤ maximumBytes) :
    decodeContextRequestBounded maximumBytes (encodeContextRequest request) =
      .accepted request := by
  unfold decodeContextRequestBounded
  rw [← encodeContextRequestAt_fixedLe request] at hbound ⊢
  rw [context_bounded_at_roundtrip .fixedLe maximumBytes request hbound]
  rfl

theorem legacy_context_bounded_roundtrip (maximumBytes : Nat)
    (request : ContextSignedRequest)
    (hbound : (encodeLegacyContextRequest request).length ≤ maximumBytes) :
    decodeContextRequestBounded maximumBytes
        (encodeLegacyContextRequest request) =
      .accepted request := by
  unfold decodeContextRequestBounded encodeLegacyContextRequest
  rw [context_bounded_at_roundtrip .legacyUnary maximumBytes request hbound]
  rfl

inductive ContextShapeRefusal where
  | emptyDocument
  | emptyGenesis
  | emptyContextCommitment
  | emptyNonce
  | emptyOperationId
  | emptyChildId
  | emptyDestinationId
  | emptySignature
  deriving DecidableEq, Repr

def validateContextShape (request : ContextSignedRequest) :
    Except ContextShapeRefusal ContextSignedRequest :=
  if request.content.document.isEmpty then .error .emptyDocument
  else if request.content.genesis.isEmpty then .error .emptyGenesis
  else if request.content.contextCommitment.isEmpty then
    .error .emptyContextCommitment
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

/-- Exact unsigned word ceiling used by the FORMAT-v3 child and citation
lanes. -/
def maximumUInt64Nat : Nat := 2 ^ 64 - 1

/-- Exact nonnegative signed-word ceiling used by FORMAT-v3 destinations. -/
def maximumInt64Nat : Nat := 2 ^ 63 - 1

inductive HostWidthRefusal where
  | childIndexTooLarge
  | destinationIndexTooLarge
  | citeTooLarge
  deriving DecidableEq, Repr

def validateHostWidths (request : ContextSignedRequest) :
    Except HostWidthRefusal ContextSignedRequest :=
  if request.content.move.child.kernelIndex ≤ maximumUInt64Nat then
    match request.content.move.dest with
    | some destination =>
        if destination.kernelIndex ≤ maximumInt64Nat then
          if request.content.move.cite ≤ maximumUInt64Nat then .ok request
          else .error .citeTooLarge
        else .error .destinationIndexTooLarge
    | none =>
        if request.content.move.cite ≤ maximumUInt64Nat then .ok request
        else .error .citeTooLarge
  else .error .childIndexTooLarge

/-! ## Exact neutral projection -/

def ContextSignedRequest.toLegacy (request : ContextSignedRequest) :
    SignedRequest :=
  ⟨⟨request.content.document, request.content.genesis,
      request.content.signatureAlgorithm, request.content.issuer,
      request.content.keyEpoch, request.content.nonce, request.content.move⟩,
    request.signature⟩

def execDestination (request : ContextSignedRequest) : Option Nat :=
  request.content.move.dest.map NodeRef.kernelIndex

theorem destinationIndex_toLegacy_exact (request : ContextSignedRequest) :
    destinationIndex request.toLegacy.content.move.dest =
      match execDestination request with
      | none => -1
      | some index => Int.ofNat index := by
  cases h : request.content.move.dest <;>
    simp [ContextSignedRequest.toLegacy, destinationIndex, execDestination, h]

structure AdmissionProjection where
  canonicalRequest : Bytes
  signingBytes : Bytes
  signatureAlgorithm : UInt8
  signature : SignatureBytes
  document : StableId
  genesis : StableId
  contextCommitment : StableId
  issuer : UInt64
  keyEpoch : UInt64
  nonce : StableId
  operationId : StableId
  lamport : UInt64
  child : NodeRef
  destination : Option NodeRef
  execReplica : UInt64
  execChild : Nat
  execDestination : Option Nat
  execCite : Nat
  deriving DecidableEq, Repr

def AdmissionProjection.ofRequestAt (fmt : LamportWireFormat)
    (request : ContextSignedRequest) : AdmissionProjection where
  canonicalRequest := encodeContextRequestAt fmt request
  signingBytes := contextSigningBytesAt fmt request.content
  signatureAlgorithm := request.content.signatureAlgorithm
  signature := request.signature
  document := request.content.document
  genesis := request.content.genesis
  contextCommitment := request.content.contextCommitment
  issuer := request.content.issuer
  keyEpoch := request.content.keyEpoch
  nonce := request.content.nonce
  operationId := request.content.move.operationId
  lamport := (toExecOp request.toLegacy).lamport
  child := request.content.move.child
  destination := request.content.move.dest
  execReplica := (toExecOp request.toLegacy).replica
  execChild := (toExecOp request.toLegacy).child
  execDestination := RuntimeAuthV4Kernel.execDestination request
  execCite := (toExecOp request.toLegacy).cite

def AdmissionProjection.ofRequest (request : ContextSignedRequest) :
    AdmissionProjection :=
  AdmissionProjection.ofRequestAt .fixedLe request

theorem AdmissionProjection.ofRequestAt_exact (fmt : LamportWireFormat)
    (request : ContextSignedRequest) :
    let projection := AdmissionProjection.ofRequestAt fmt request
    projection.canonicalRequest = encodeContextRequestAt fmt request
      ∧ projection.signingBytes = contextSigningBytesAt fmt request.content
      ∧ projection.signatureAlgorithm = request.content.signatureAlgorithm
      ∧ projection.signature = request.signature
      ∧ projection.document = request.content.document
      ∧ projection.genesis = request.content.genesis
      ∧ projection.contextCommitment = request.content.contextCommitment
      ∧ projection.issuer = request.content.issuer
      ∧ projection.keyEpoch = request.content.keyEpoch
      ∧ projection.nonce = request.content.nonce
      ∧ projection.operationId = request.content.move.operationId
      ∧ projection.lamport = (toExecOp request.toLegacy).lamport
      ∧ projection.child = request.content.move.child
      ∧ projection.destination = request.content.move.dest
      ∧ projection.execReplica = (toExecOp request.toLegacy).replica
      ∧ projection.execChild = (toExecOp request.toLegacy).child
      ∧ (match projection.execDestination with
          | none => (-1 : Int)
          | some index => Int.ofNat index) = (toExecOp request.toLegacy).dest
      ∧ projection.execCite = (toExecOp request.toLegacy).cite := by
  simp only [AdmissionProjection.ofRequestAt, true_and]
  exact ⟨by
    simpa only [toExecOp] using (destinationIndex_toLegacy_exact request).symm,
    True.intro⟩

theorem AdmissionProjection.ofRequest_exact (request : ContextSignedRequest) :
    let projection := AdmissionProjection.ofRequest request
    projection.canonicalRequest = encodeContextRequest request
      ∧ projection.signingBytes = contextSigningBytes request.content
      ∧ projection.signatureAlgorithm = request.content.signatureAlgorithm
      ∧ projection.signature = request.signature
      ∧ projection.document = request.content.document
      ∧ projection.genesis = request.content.genesis
      ∧ projection.contextCommitment = request.content.contextCommitment
      ∧ projection.issuer = request.content.issuer
      ∧ projection.keyEpoch = request.content.keyEpoch
      ∧ projection.nonce = request.content.nonce
      ∧ projection.operationId = request.content.move.operationId
      ∧ projection.lamport = (toExecOp request.toLegacy).lamport
      ∧ projection.child = request.content.move.child
      ∧ projection.destination = request.content.move.dest
      ∧ projection.execReplica = (toExecOp request.toLegacy).replica
      ∧ projection.execChild = (toExecOp request.toLegacy).child
      ∧ (match projection.execDestination with
          | none => (-1 : Int)
          | some index => Int.ofNat index) = (toExecOp request.toLegacy).dest
      ∧ projection.execCite = (toExecOp request.toLegacy).cite :=
  AdmissionProjection.ofRequestAt_exact .fixedLe request

/-! ## Canonical, self-decoding response -/

def lamportProjectionAnyWire : WireCodec (UInt64 × LamportWireFormat) where
  encode
    | (t, .fixedLe) => fixedLamportProjectionTag :: encodeUInt64Le t
    | (t, .legacyUnary) => legacyLamportProjectionTag :: uint64Wire.encode t
  parse
    | [] => none
    | tag :: rest =>
        if tag = fixedLamportProjectionTag then
          match parseUInt64Le rest with
          | none => none
          | some (t, trailing) => some ((t, .fixedLe), trailing)
        else if tag = legacyLamportProjectionTag then
          match uint64Wire.parse rest with
          | none => none
          | some (t, trailing) => some ((t, .legacyUnary), trailing)
        else none
  parse_encode_append := by
    intro ⟨t, fmt⟩ trailing
    cases fmt
    · simp [fixedLamportProjectionTag, parseUInt64Le_encodeUInt64Le_append]
    · simp [fixedLamportProjectionTag, legacyLamportProjectionTag,
        uint64Wire.parse_encode_append]

private abbrev ProjectionRaw :=
  Bytes × Bytes × UInt8 × Bytes × Bytes × Bytes × Bytes ×
    UInt64 × UInt64 × Bytes × Bytes × UInt64 × NodeRef ×
      Option NodeRef × UInt64 × Nat × Option Nat × Nat

private abbrev ProjectionAnyRaw :=
  Bytes × Bytes × UInt8 × Bytes × Bytes × Bytes × Bytes ×
    UInt64 × UInt64 × Bytes × Bytes × (UInt64 × LamportWireFormat) × NodeRef ×
      Option NodeRef × UInt64 × Nat × Option Nat × Nat

/-- Accepted tags `161..171`, `179` (`lamport` as fixed-width 8-byte LE), and
`173..178`, in structure-field order.  Byte strings use the canonical
unary-length codec; naturals remain exact naturals. -/
def admissionProjectionWire : WireCodec AdmissionProjection :=
  ((fieldWire 161 stableIdWire).prod
    ((fieldWire 162 stableIdWire).prod
      ((fieldWire 163 byteWire).prod
        ((fieldWire 164 stableIdWire).prod
          ((fieldWire 165 stableIdWire).prod
            ((fieldWire 166 stableIdWire).prod
              ((fieldWire 167 stableIdWire).prod
                ((fieldWire 168 uint64Wire).prod
                  ((fieldWire 169 uint64Wire).prod
                    ((fieldWire 170 stableIdWire).prod
                      ((fieldWire 171 stableIdWire).prod
                        ((fieldWire fixedLamportProjectionTag uint64LeWire).prod
                          ((fieldWire 173 nodeRefWire).prod
                            ((fieldWire 174 (WireCodec.option nodeRefWire)).prod
                              ((fieldWire 175 uint64Wire).prod
                                ((fieldWire 176 natWire).prod
                                  ((fieldWire 177 (WireCodec.option natWire)).prod
                                    (fieldWire 178 natWire)))))))))))))))))).xmap
    (fun p : AdmissionProjection =>
      (p.canonicalRequest, (p.signingBytes, (p.signatureAlgorithm,
        (p.signature, (p.document, (p.genesis, (p.contextCommitment,
          (p.issuer, (p.keyEpoch, (p.nonce, (p.operationId, (p.lamport,
            (p.child, (p.destination, (p.execReplica, (p.execChild,
              (p.execDestination, p.execCite))))))))))))))))))
    (fun raw : ProjectionRaw =>
      ⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2.1,
        raw.2.2.2.2.2.1, raw.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.1, raw.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (by intro projection; cases projection; rfl)

def admissionProjectionAnyWire :
    WireCodec (AdmissionProjection × LamportWireFormat) :=
  ((fieldWire 161 stableIdWire).prod
    ((fieldWire 162 stableIdWire).prod
      ((fieldWire 163 byteWire).prod
        ((fieldWire 164 stableIdWire).prod
          ((fieldWire 165 stableIdWire).prod
            ((fieldWire 166 stableIdWire).prod
              ((fieldWire 167 stableIdWire).prod
                ((fieldWire 168 uint64Wire).prod
                  ((fieldWire 169 uint64Wire).prod
                    ((fieldWire 170 stableIdWire).prod
                      ((fieldWire 171 stableIdWire).prod
                        (lamportProjectionAnyWire.prod
                          ((fieldWire 173 nodeRefWire).prod
                            ((fieldWire 174 (WireCodec.option nodeRefWire)).prod
                              ((fieldWire 175 uint64Wire).prod
                                ((fieldWire 176 natWire).prod
                                  ((fieldWire 177 (WireCodec.option natWire)).prod
                                    (fieldWire 178 natWire)))))))))))))))))).xmap
    (fun pair : AdmissionProjection × LamportWireFormat =>
      let p := pair.1
      (p.canonicalRequest, (p.signingBytes, (p.signatureAlgorithm,
        (p.signature, (p.document, (p.genesis, (p.contextCommitment,
          (p.issuer, (p.keyEpoch, (p.nonce, (p.operationId,
            ((p.lamport, pair.2),
              (p.child, (p.destination, (p.execReplica, (p.execChild,
                (p.execDestination, p.execCite))))))))))))))))))
    (fun raw : ProjectionAnyRaw =>
      (⟨raw.1, raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2.1,
          raw.2.2.2.2.2.1, raw.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.1, raw.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.2.2.1.1,
          raw.2.2.2.2.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
        raw.2.2.2.2.2.2.2.2.2.2.2.1.2))
    (by intro ⟨projection, fmt⟩; cases projection; rfl)

inductive AdmissionRefusal where
  | decode (reason : DecodeRefusal)
  | shape (reason : ContextShapeRefusal)
  | hostWidth (reason : HostWidthRefusal)
  deriving DecidableEq, Repr

inductive AdmissionOutcome where
  | accepted (projection : AdmissionProjection)
  | refused (reason : AdmissionRefusal)
  deriving DecidableEq, Repr

inductive FormattedAdmissionOutcome where
  | accepted (format : LamportWireFormat) (projection : AdmissionProjection)
  | refused (reason : AdmissionRefusal)
  deriving DecidableEq, Repr

def FormattedAdmissionOutcome.toOutcome :
    FormattedAdmissionOutcome → AdmissionOutcome
  | .accepted _ projection => .accepted projection
  | .refused reason => .refused reason

/-- Result tags: accepted `0`; decode `1..5`; shape `6..13`; width `14..16`. -/
def admissionRefusalTag : AdmissionRefusal → UInt8
  | .decode .tooLarge => 1
  | .decode .badMagic => 2
  | .decode .unsupportedVersion => 3
  | .decode .wrongKind => 4
  | .decode .malformed => 5
  | .shape .emptyDocument => 6
  | .shape .emptyGenesis => 7
  | .shape .emptyContextCommitment => 8
  | .shape .emptyNonce => 9
  | .shape .emptyOperationId => 10
  | .shape .emptyChildId => 11
  | .shape .emptyDestinationId => 12
  | .shape .emptySignature => 13
  | .hostWidth .childIndexTooLarge => 14
  | .hostWidth .destinationIndexTooLarge => 15
  | .hostWidth .citeTooLarge => 16

def admissionRefusalOfTag : UInt8 → Option AdmissionRefusal
  | 1 => some (.decode .tooLarge)
  | 2 => some (.decode .badMagic)
  | 3 => some (.decode .unsupportedVersion)
  | 4 => some (.decode .wrongKind)
  | 5 => some (.decode .malformed)
  | 6 => some (.shape .emptyDocument)
  | 7 => some (.shape .emptyGenesis)
  | 8 => some (.shape .emptyContextCommitment)
  | 9 => some (.shape .emptyNonce)
  | 10 => some (.shape .emptyOperationId)
  | 11 => some (.shape .emptyChildId)
  | 12 => some (.shape .emptyDestinationId)
  | 13 => some (.shape .emptySignature)
  | 14 => some (.hostWidth .childIndexTooLarge)
  | 15 => some (.hostWidth .destinationIndexTooLarge)
  | 16 => some (.hostWidth .citeTooLarge)
  | _ => none

theorem admissionRefusalOfTag_roundtrip (reason : AdmissionRefusal) :
    admissionRefusalOfTag (admissionRefusalTag reason) = some reason := by
  cases reason with
  | decode reason => cases reason <;> rfl
  | shape reason => cases reason <;> rfl
  | hostWidth reason => cases reason <;> rfl

theorem admissionRefusalTag_injective :
    Function.Injective admissionRefusalTag := by
  intro left right h
  have mapped := congrArg admissionRefusalOfTag h
  rw [admissionRefusalOfTag_roundtrip,
    admissionRefusalOfTag_roundtrip] at mapped
  exact Option.some.inj mapped

theorem admissionRefusalTag_ne_zero (reason : AdmissionRefusal) :
    admissionRefusalTag reason ≠ 0 := by
  cases reason with
  | decode reason => cases reason <;> decide
  | shape reason => cases reason <;> decide
  | hostWidth reason => cases reason <;> decide

def admissionOutcomeWire : WireCodec AdmissionOutcome where
  encode
    | .accepted projection => 0 :: admissionProjectionWire.encode projection
    | .refused reason => [admissionRefusalTag reason]
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then
          match admissionProjectionWire.parse trailing with
          | none => none
          | some (projection, rest) => some (.accepted projection, rest)
        else
          match admissionRefusalOfTag tag with
          | none => none
          | some reason => some (.refused reason, trailing)
  parse_encode_append := by
    intro outcome trailing
    cases outcome with
    | accepted projection =>
        simp [admissionProjectionWire.parse_encode_append]
    | refused reason =>
        simp [admissionRefusalTag_ne_zero, admissionRefusalOfTag_roundtrip]

def admissionOutcomeAnyWire : WireCodec FormattedAdmissionOutcome where
  encode
    | .accepted fmt projection =>
        0 :: admissionProjectionAnyWire.encode (projection, fmt)
    | .refused reason => [admissionRefusalTag reason]
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then
          match admissionProjectionAnyWire.parse trailing with
          | none => none
          | some ((projection, fmt), rest) =>
              some (.accepted fmt projection, rest)
        else
          match admissionRefusalOfTag tag with
          | none => none
          | some reason => some (.refused reason, trailing)
  parse_encode_append := by
    intro outcome trailing
    cases outcome with
    | accepted fmt projection =>
        simp [admissionProjectionAnyWire.parse_encode_append]
    | refused reason =>
        simp [admissionRefusalTag_ne_zero, admissionRefusalOfTag_roundtrip]

def admissionResponsePrefix : Bytes :=
  protocolMagic ++ [versionV4, admissionResponseKind]

def admissionResponseWire : WireCodec AdmissionOutcome :=
  prefixedWire admissionResponsePrefix admissionOutcomeWire

def admissionResponseAnyWire : WireCodec FormattedAdmissionOutcome :=
  prefixedWire admissionResponsePrefix admissionOutcomeAnyWire

def admissionResponseCodec : Durable.CanonicalCodec AdmissionOutcome :=
  canonicalCodecOfWire admissionResponseWire

def admissionResponseAnyCodec :
    Durable.CanonicalCodec FormattedAdmissionOutcome :=
  canonicalCodecOfWire admissionResponseAnyWire

def encodeAdmissionResponseAt (fmt : LamportWireFormat) :
    AdmissionOutcome → Bytes
  | .accepted projection =>
      admissionResponseAnyCodec.encode (.accepted fmt projection)
  | .refused reason =>
      admissionResponseAnyCodec.encode (.refused reason)

def encodeAdmissionResponse (outcome : AdmissionOutcome) : Bytes :=
  admissionResponseCodec.encode outcome

@[simp] theorem encodeAdmissionResponseAt_fixedLe (outcome : AdmissionOutcome) :
    encodeAdmissionResponseAt .fixedLe outcome =
      encodeAdmissionResponse outcome := by
  cases outcome <;> rfl

def decodeAdmissionResponseWithFormat (bytes : Bytes) :
    Option FormattedAdmissionOutcome :=
  admissionResponseAnyCodec.decode bytes

def decodeAdmissionResponse (bytes : Bytes) : Option AdmissionOutcome :=
  FormattedAdmissionOutcome.toOutcome <$> decodeAdmissionResponseWithFormat bytes

theorem admissionResponseAt_roundtrip (fmt : LamportWireFormat)
    (outcome : AdmissionOutcome) :
    decodeAdmissionResponse (encodeAdmissionResponseAt fmt outcome) =
      some outcome := by
  cases outcome with
  | accepted projection =>
      simp [decodeAdmissionResponse, decodeAdmissionResponseWithFormat,
        encodeAdmissionResponseAt, admissionResponseAnyCodec.decode_encode,
        FormattedAdmissionOutcome.toOutcome]
  | refused reason =>
      simp [decodeAdmissionResponse, decodeAdmissionResponseWithFormat,
        encodeAdmissionResponseAt, admissionResponseAnyCodec.decode_encode,
        FormattedAdmissionOutcome.toOutcome]

theorem admissionResponse_roundtrip (outcome : AdmissionOutcome) :
    decodeAdmissionResponse (encodeAdmissionResponse outcome) = some outcome := by
  rw [← encodeAdmissionResponseAt_fixedLe outcome]
  exact admissionResponseAt_roundtrip .fixedLe outcome

theorem encodeAdmissionResponse_injective :
    Function.Injective encodeAdmissionResponse := by
  intro left right h
  apply Option.some.inj
  calc
    some left = decodeAdmissionResponse (encodeAdmissionResponse left) :=
      (admissionResponse_roundtrip left).symm
    _ = decodeAdmissionResponse (encodeAdmissionResponse right) := congrArg _ h
    _ = some right := admissionResponse_roundtrip right

theorem admissionResponse_binds_kind (outcome : AdmissionOutcome) :
    (encodeAdmissionResponse outcome)[5]? = some admissionResponseKind := by
  simp [encodeAdmissionResponse, admissionResponseCodec, canonicalCodecOfWire,
    admissionResponseWire, prefixedWire, admissionResponsePrefix,
    protocolMagic]

theorem context_request_separated_from_admission_response
    (request : ContextSignedRequest) (outcome : AdmissionOutcome) :
    encodeContextRequest request ≠ encodeAdmissionResponse outcome := by
  intro h
  have atKind := congrArg (fun bytes : Bytes => bytes[5]?) h
  have : some contextMoveKind = some admissionResponseKind := by
    simpa only [context_request_kind_at_index,
      admissionResponse_binds_kind] using atKind
  contradiction

/-! ## Executed fixture pinning the positive crossing -/

def fixtureContextContent : ContextSignedContent :=
  ⟨fixtureContent.document, fixtureContent.genesis,
    fixtureContent.signatureAlgorithm, fixtureContent.issuer,
    fixtureContent.keyEpoch, fixtureContent.nonce, fixtureContent.move,
    [201, 202, 203]⟩

def fixtureContextRequest : ContextSignedRequest :=
  ⟨fixtureContextContent, fixtureRequest.signature⟩

theorem fixture_context_request_roundtrip :
    contextRequestCodec.decode (encodeContextRequest fixtureContextRequest) =
      some fixtureContextRequest :=
  contextRequest_roundtrip _

theorem fixture_legacy_request_wrong_kind :
    decodeContextRequestBounded (encodeRequestV4 fixtureRequest).length
      (encodeRequestV4 fixtureRequest) = .refused .wrongKind := by
  decide

/-! ## Pipeline and native export -/

def projectAdmissionWithFormat (maximumBytes : Nat) (bytes : Bytes) :
    FormattedAdmissionOutcome :=
  match decodeContextRequestWithFormatBounded maximumBytes bytes with
  | .refused reason => .refused (.decode reason)
  | .accepted fmt request =>
      match validateContextShape request with
      | .error reason => .refused (.shape reason)
      | .ok shaped =>
          match validateHostWidths shaped with
          | .error reason => .refused (.hostWidth reason)
          | .ok checked =>
              .accepted fmt (AdmissionProjection.ofRequestAt fmt checked)

def projectAdmission (maximumBytes : Nat) (bytes : Bytes) : AdmissionOutcome :=
  (projectAdmissionWithFormat maximumBytes bytes).toOutcome

def projectAdmissionBytes (maximumBytes : Nat) (bytes : Bytes) : Bytes :=
  admissionResponseAnyCodec.encode (projectAdmissionWithFormat maximumBytes bytes)

theorem decode_projectAdmissionBytes (maximumBytes : Nat) (bytes : Bytes) :
    decodeAdmissionResponse (projectAdmissionBytes maximumBytes bytes) =
      some (projectAdmission maximumBytes bytes) := by
  simp [decodeAdmissionResponse, decodeAdmissionResponseWithFormat,
    projectAdmissionBytes, projectAdmission,
    admissionResponseAnyCodec.decode_encode]

theorem projectAdmissionBytes_accepted_at_exact (fmt : LamportWireFormat)
    (maximumBytes : Nat) (bytes : Bytes) (request : ContextSignedRequest)
    (hdecode : decodeContextRequestWithFormatBounded maximumBytes bytes =
      .accepted fmt request)
    (hshape : validateContextShape request = .ok request)
    (hwidth : validateHostWidths request = .ok request) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponseAt fmt
        (.accepted (AdmissionProjection.ofRequestAt fmt request)) := by
  simp [projectAdmissionBytes, projectAdmissionWithFormat,
    encodeAdmissionResponseAt, hdecode, hshape, hwidth]

theorem projectAdmissionBytes_accepted_exact (maximumBytes : Nat)
    (bytes : Bytes) (request : ContextSignedRequest)
    (hdecode : decodeContextRequestWithFormatBounded maximumBytes bytes =
      .accepted .fixedLe request)
    (hshape : validateContextShape request = .ok request)
    (hwidth : validateHostWidths request = .ok request) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse
        (.accepted (AdmissionProjection.ofRequest request)) := by
  simpa [AdmissionProjection.ofRequest] using
    projectAdmissionBytes_accepted_at_exact .fixedLe maximumBytes bytes request
      hdecode hshape hwidth

theorem projectAdmissionBytes_decode_refused (maximumBytes : Nat)
    (bytes : Bytes) (reason : DecodeRefusal)
    (hdecode : decodeContextRequestBounded maximumBytes bytes =
      .refused reason) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse (.refused (.decode reason)) := by
  unfold decodeContextRequestBounded at hdecode
  cases hraw : decodeContextRequestWithFormatBounded maximumBytes bytes with
  | refused rawReason =>
      rw [hraw] at hdecode
      cases hdecode
      simp [projectAdmissionBytes, projectAdmissionWithFormat, hraw]
      rfl
  | accepted _ _ =>
      rw [hraw] at hdecode
      cases hdecode

theorem projectAdmissionBytes_shape_refused (maximumBytes : Nat)
    (bytes : Bytes) (request : ContextSignedRequest)
    (reason : ContextShapeRefusal)
    (hdecode : decodeContextRequestBounded maximumBytes bytes =
      .accepted request)
    (hshape : validateContextShape request = .error reason) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse (.refused (.shape reason)) := by
  unfold decodeContextRequestBounded at hdecode
  cases hraw : decodeContextRequestWithFormatBounded maximumBytes bytes with
  | refused _ =>
      rw [hraw] at hdecode
      cases hdecode
  | accepted fmt rawReq =>
      rw [hraw] at hdecode
      cases hdecode
      simp [projectAdmissionBytes, projectAdmissionWithFormat, hraw, hshape]
      rfl

theorem projectAdmissionBytes_width_refused (maximumBytes : Nat)
    (bytes : Bytes) (request : ContextSignedRequest)
    (reason : HostWidthRefusal)
    (hdecode : decodeContextRequestBounded maximumBytes bytes =
      .accepted request)
    (hshape : validateContextShape request = .ok request)
    (hwidth : validateHostWidths request = .error reason) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse (.refused (.hostWidth reason)) := by
  unfold decodeContextRequestBounded at hdecode
  cases hraw : decodeContextRequestWithFormatBounded maximumBytes bytes with
  | refused _ =>
      rw [hraw] at hdecode
      cases hdecode
  | accepted fmt rawReq =>
      rw [hraw] at hdecode
      cases hdecode
      simp [projectAdmissionBytes, projectAdmissionWithFormat, hraw, hshape,
        hwidth]
      rfl

theorem distinct_refusals_have_distinct_responses {left right : AdmissionRefusal}
    (hne : left ≠ right) :
    encodeAdmissionResponse (.refused left) ≠
      encodeAdmissionResponse (.refused right) := by
  intro h
  exact hne (AdmissionOutcome.refused.inj
    (encodeAdmissionResponse_injective h))

theorem fixture_context_projection_accepted :
    projectAdmission (encodeContextRequest fixtureContextRequest).length
      (encodeContextRequest fixtureContextRequest) =
        .accepted (AdmissionProjection.ofRequest fixtureContextRequest) := by
  decide

theorem fixture_legacy_context_projection_accepted :
    projectAdmission (encodeLegacyContextRequest fixtureContextRequest).length
      (encodeLegacyContextRequest fixtureContextRequest) =
        .accepted
          (AdmissionProjection.ofRequestAt .legacyUnary fixtureContextRequest) := by
  decide

@[export uwueave_runtime_auth_v4_project_admission]
def projectAdmissionKernel (maximumBytes : Nat) (input : ByteArray) : ByteArray :=
  (projectAdmissionBytes maximumBytes input.data.toList).toByteArray

end Uwueave.RuntimeAuthV4Kernel
