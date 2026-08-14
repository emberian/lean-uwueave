/-
# Uwueave.RuntimeAuthV4Kernel — context-bound FORMAT-v4 admission projection

This leaf owns a new signed request kind for runtime admission.  Unlike the
legacy kind-1 syntax record, kind 3 signs a nonempty context commitment so a
host can select the exact historical resolver/authority substrate.  The
executable endpoint performs bounded canonical decoding, semantic shape
checks, and exact FORMAT-v3 word-representability checks.  On success it emits
a canonical, self-decoding projection for later host stages.

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

/-- Tags `81..87` retain the legacy meanings; tag `88` is the context
commitment. -/
def contextSignedContentWire : WireCodec ContextSignedContent :=
  ((fieldWire 81 stableIdWire).prod
    ((fieldWire 82 stableIdWire).prod
      ((fieldWire 83 byteWire).prod
        ((fieldWire 84 uint64Wire).prod
          ((fieldWire 85 uint64Wire).prod
            ((fieldWire 86 stableIdWire).prod
              ((fieldWire 87 movePayloadWire).prod
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

structure ContextSignedRequest where
  content : ContextSignedContent
  signature : SignatureBytes
  deriving DecidableEq, Repr

def contextRequestPayloadWire : WireCodec ContextSignedRequest :=
  ((fieldWire 97 contextSignedContentWire).prod
    (fieldWire 98 stableIdWire)).xmap
    (fun request => (request.content, request.signature))
    (fun raw => ⟨raw.1, raw.2⟩)
    (by intro request; cases request; rfl)

def contextRequestWire : WireCodec ContextSignedRequest :=
  prefixedWire (requestPrefixAt versionV4 contextMoveKind)
    contextRequestPayloadWire

def contextRequestCodec : Durable.CanonicalCodec ContextSignedRequest :=
  canonicalCodecOfWire contextRequestWire

def encodeContextRequest (request : ContextSignedRequest) : Bytes :=
  contextRequestCodec.encode request

/-- The exact kind-3 bytes submitted to a host verifier: prefix and all signed
content, excluding only tag `98` and the signature value. -/
def contextSigningWire : WireCodec ContextSignedContent :=
  prefixedWire (requestPrefixAt versionV4 contextMoveKind)
    (fieldWire 97 contextSignedContentWire)

def contextSigningCodec : Durable.CanonicalCodec ContextSignedContent :=
  canonicalCodecOfWire contextSigningWire

def contextSigningBytes (content : ContextSignedContent) : Bytes :=
  contextSigningCodec.encode content

theorem contextRequest_roundtrip (request : ContextSignedRequest) :
    contextRequestCodec.decode (encodeContextRequest request) = some request :=
  contextRequestCodec.decode_encode request

theorem contextSigning_roundtrip (content : ContextSignedContent) :
    contextSigningCodec.decode (contextSigningBytes content) = some content :=
  contextSigningCodec.decode_encode content

theorem contextSigningBytes_injective :
    Function.Injective contextSigningBytes := by
  intro left right h
  apply Option.some.inj
  calc
    some left = contextSigningCodec.decode (contextSigningBytes left) :=
      (contextSigning_roundtrip left).symm
    _ = contextSigningCodec.decode (contextSigningBytes right) := congrArg _ h
    _ = some right := contextSigning_roundtrip right

theorem context_commitment_is_signed {left right : ContextSignedContent}
    (hne : left.contextCommitment ≠ right.contextCommitment) :
    contextSigningBytes left ≠ contextSigningBytes right := by
  intro h
  exact hne (congrArg ContextSignedContent.contextCommitment
    (contextSigningBytes_injective h))

/-- Reading the object-kind byte is enough to separate context-bound requests
from every other format-v4 object kind, independently of payload bytes. -/
theorem context_request_kind_at_index (request : ContextSignedRequest) :
    (encodeContextRequest request)[5]? = some contextMoveKind := by
  simp [encodeContextRequest, contextRequestCodec, canonicalCodecOfWire,
    contextRequestWire, prefixedWire, requestPrefixAt, protocolMagic]

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

def decodeContextRequestBounded (maximumBytes : Nat) (bytes : Bytes) :
    ContextDecodeOutcome :=
  if bytes.length ≤ maximumBytes then
    match contextHeaderRefusal? bytes with
    | some reason => .refused reason
    | none =>
        match contextRequestCodec.decode bytes with
        | none => .refused .malformed
        | some request => .accepted request
  else
    .refused .tooLarge

theorem context_bounded_roundtrip (maximumBytes : Nat)
    (request : ContextSignedRequest)
    (hbound : (encodeContextRequest request).length ≤ maximumBytes) :
    decodeContextRequestBounded maximumBytes (encodeContextRequest request) =
      .accepted request := by
  unfold decodeContextRequestBounded
  rw [if_pos hbound]
  have hheader :
      contextHeaderRefusal? (encodeContextRequest request) = none := by
    simp [contextHeaderRefusal?, encodeContextRequest, contextRequestCodec,
      canonicalCodecOfWire, contextRequestWire, prefixedWire,
      requestPrefixAt, protocolMagic, versionV4, contextMoveKind]
  rw [hheader, contextRequest_roundtrip]

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

def AdmissionProjection.ofRequest (request : ContextSignedRequest) :
    AdmissionProjection where
  canonicalRequest := encodeContextRequest request
  signingBytes := contextSigningBytes request.content
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
      ∧ projection.execCite = (toExecOp request.toLegacy).cite := by
  simp only [AdmissionProjection.ofRequest, true_and]
  exact ⟨by
    simpa only [toExecOp] using (destinationIndex_toLegacy_exact request).symm,
    True.intro⟩

/-! ## Canonical, self-decoding response -/

private abbrev ProjectionRaw :=
  Bytes × Bytes × UInt8 × Bytes × Bytes × Bytes × Bytes ×
    UInt64 × UInt64 × Bytes × Bytes × UInt64 × NodeRef ×
      Option NodeRef × UInt64 × Nat × Option Nat × Nat

/-- Accepted tags `161..178`, in structure-field order.  Byte strings use the
canonical unary-length codec; naturals remain exact naturals. -/
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
                        ((fieldWire 172 uint64Wire).prod
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

inductive AdmissionRefusal where
  | decode (reason : DecodeRefusal)
  | shape (reason : ContextShapeRefusal)
  | hostWidth (reason : HostWidthRefusal)
  deriving DecidableEq, Repr

inductive AdmissionOutcome where
  | accepted (projection : AdmissionProjection)
  | refused (reason : AdmissionRefusal)
  deriving DecidableEq, Repr

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

def admissionResponsePrefix : Bytes :=
  protocolMagic ++ [versionV4, admissionResponseKind]

def admissionResponseWire : WireCodec AdmissionOutcome :=
  prefixedWire admissionResponsePrefix admissionOutcomeWire

def admissionResponseCodec : Durable.CanonicalCodec AdmissionOutcome :=
  canonicalCodecOfWire admissionResponseWire

def encodeAdmissionResponse (outcome : AdmissionOutcome) : Bytes :=
  admissionResponseCodec.encode outcome

def decodeAdmissionResponse (bytes : Bytes) : Option AdmissionOutcome :=
  admissionResponseCodec.decode bytes

theorem admissionResponse_roundtrip (outcome : AdmissionOutcome) :
    decodeAdmissionResponse (encodeAdmissionResponse outcome) = some outcome :=
  admissionResponseCodec.decode_encode outcome

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

def projectAdmission (maximumBytes : Nat) (bytes : Bytes) : AdmissionOutcome :=
  match decodeContextRequestBounded maximumBytes bytes with
  | .refused reason => .refused (.decode reason)
  | .accepted request =>
      match validateContextShape request with
      | .error reason => .refused (.shape reason)
      | .ok shaped =>
          match validateHostWidths shaped with
          | .error reason => .refused (.hostWidth reason)
          | .ok checked => .accepted (AdmissionProjection.ofRequest checked)

def projectAdmissionBytes (maximumBytes : Nat) (bytes : Bytes) : Bytes :=
  encodeAdmissionResponse (projectAdmission maximumBytes bytes)

theorem decode_projectAdmissionBytes (maximumBytes : Nat) (bytes : Bytes) :
    decodeAdmissionResponse (projectAdmissionBytes maximumBytes bytes) =
      some (projectAdmission maximumBytes bytes) :=
  admissionResponse_roundtrip _

theorem projectAdmissionBytes_accepted_exact (maximumBytes : Nat)
    (bytes : Bytes) (request : ContextSignedRequest)
    (hdecode : decodeContextRequestBounded maximumBytes bytes =
      .accepted request)
    (hshape : validateContextShape request = .ok request)
    (hwidth : validateHostWidths request = .ok request) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse
        (.accepted (AdmissionProjection.ofRequest request)) := by
  simp [projectAdmissionBytes, projectAdmission, hdecode, hshape, hwidth]

theorem projectAdmissionBytes_decode_refused (maximumBytes : Nat)
    (bytes : Bytes) (reason : DecodeRefusal)
    (hdecode : decodeContextRequestBounded maximumBytes bytes =
      .refused reason) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse (.refused (.decode reason)) := by
  simp [projectAdmissionBytes, projectAdmission, hdecode]

theorem projectAdmissionBytes_shape_refused (maximumBytes : Nat)
    (bytes : Bytes) (request : ContextSignedRequest)
    (reason : ContextShapeRefusal)
    (hdecode : decodeContextRequestBounded maximumBytes bytes =
      .accepted request)
    (hshape : validateContextShape request = .error reason) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse (.refused (.shape reason)) := by
  simp [projectAdmissionBytes, projectAdmission, hdecode, hshape]

theorem projectAdmissionBytes_width_refused (maximumBytes : Nat)
    (bytes : Bytes) (request : ContextSignedRequest)
    (reason : HostWidthRefusal)
    (hdecode : decodeContextRequestBounded maximumBytes bytes =
      .accepted request)
    (hshape : validateContextShape request = .ok request)
    (hwidth : validateHostWidths request = .error reason) :
    projectAdmissionBytes maximumBytes bytes =
      encodeAdmissionResponse (.refused (.hostWidth reason)) := by
  simp [projectAdmissionBytes, projectAdmission, hdecode, hshape, hwidth]

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

@[export uwueave_runtime_auth_v4_project_admission]
def projectAdmissionKernel (maximumBytes : Nat) (input : ByteArray) : ByteArray :=
  (projectAdmissionBytes maximumBytes input.data.toList).toByteArray

end Uwueave.RuntimeAuthV4Kernel
