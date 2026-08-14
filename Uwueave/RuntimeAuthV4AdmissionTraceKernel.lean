/-
# Uwueave.RuntimeAuthV4AdmissionTraceKernel

Lean-owned validation of the canonical Rust authenticated-admission v2
certificate.  The native bridge makes this module's one-byte verdict
mandatory for fresh admission and recovered-record revalidation.
-/
import Uwueave.RuntimeAuthV4Kernel
import Uwueave.ExecRefine

namespace Uwueave.RuntimeAuthV4AdmissionTraceKernel

open Uwueave
open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel

set_option autoImplicit false

/-- Fixed admission-certificate resource ceiling: 16 MiB. -/
def maximumCertificateBytes : Nat := 16 * 1024 * 1024

/-- Fixed projection request ceiling: 1 MiB. -/
def maximumProjectionBytes : Nat := 1024 * 1024

/-- The frozen Rust admission-certificate envelope version. -/
def admissionCertificateVersion : UInt8 := 2

abbrev Bytes := List UInt8
abbrev Parser (α : Type) := StateT Bytes Option α

structure StoredMove where
  lamport : UInt64
  replica : UInt64
  child : Bytes
  destination : Option Bytes
  cite : UInt64
  deriving DecidableEq, Repr

inductive KernelAdmission where
  | applied
  | skippedCycle
  deriving DecidableEq, Repr

/-- Every field of `rust/src/persistence/authenticated.rs::encode_admission`,
in its frozen v2 order.  Hash-shaped fields stay as bytes so this checker does
not manufacture cryptographic meaning for them. -/
structure AdmissionTraceCertificate where
  canonicalRequest : Bytes
  nonceDocument : Bytes
  nonceGenesis : Bytes
  nonceIssuer : UInt64
  nonceKeyEpoch : UInt64
  nonce : Bytes
  operationDocument : Bytes
  operationGenesis : Bytes
  operationId : Bytes
  contextCommitment : Bytes
  executionBinding : Bytes
  resolverPolicy : UInt64
  authorityPolicy : UInt64
  membershipPolicy : UInt64
  previousAdmissionCommitment : Option Bytes
  signatureAlgorithm : UInt8
  signingBytes : Bytes
  signature : Bytes
  childStable : Bytes
  childIndex : UInt64
  destinationStable : Option Bytes
  destinationIndex : Option UInt64
  lamport : UInt64
  replica : UInt64
  cite : UInt64
  resolvedMove : StoredMove
  executionNodes : List Bytes
  admission : KernelAdmission
  projectionBound : UInt64
  projectionResponse : Bytes
  formatV3Request : Bytes
  formatV3Response : Bytes
  selectedRequestSlot : UInt64
  operationWasNew : Bool
  deriving DecidableEq, Repr

private def takeExact (n : Nat) : Parser Bytes := fun rest =>
  if n ≤ rest.length then some (rest.take n, rest.drop n) else none

private def readByte : Parser UInt8 := do
  let bytes ← takeExact 1
  match bytes with
  | [byte] => pure byte
  | _ => failure

private def readUInt64 : Parser UInt64 := do
  let bytes ← takeExact 8
  pure (Uwueave.Exec.getWord bytes.toByteArray 0)

private def readBytes : Parser Bytes := do
  let length ← readUInt64
  takeExact length.toNat

private def readHash : Parser Bytes := takeExact 32

private def readBool : Parser Bool := do
  match ← readByte with
  | 0 => pure false
  | 1 => pure true
  | _ => failure

private def readAcceptedReceipt : Parser Unit := do
  if (← readByte) = 1 then pure () else failure

private def readOptional {α : Type} (readValue : Parser α) : Parser (Option α) := do
  match ← readByte with
  | 0 => pure none
  | 1 => return some (← readValue)
  | _ => failure

private def readStoredMove : Parser StoredMove := do
  return {
    lamport := ← readUInt64
    replica := ← readUInt64
    child := ← readHash
    destination := ← readOptional readHash
    cite := ← readUInt64
  }

private def splitHashesAcc : Nat → Bytes → List Bytes → List Bytes
  | 0, _, accumulator => accumulator.reverse
  | count + 1, bytes, accumulator =>
      splitHashesAcc count (bytes.drop 32) (bytes.take 32 :: accumulator)

/-- Tail-recursive: even a cap-filling hostile node count does not consume one
native stack frame per purported node. -/
private def splitHashes (count : Nat) (bytes : Bytes) : List Bytes :=
  splitHashesAcc count bytes []

private def readHashes : Parser (List Bytes) := do
  let count ← readUInt64
  let bytes ← takeExact (count.toNat * 32)
  pure (splitHashes count.toNat bytes)

private def readKernelAdmission : Parser KernelAdmission := do
  match ← readByte with
  | 0 => pure .applied
  | 1 => pure .skippedCycle
  | _ => failure

/-- Strict v2 parser.  Option tags, booleans, the admission byte, and all five
receipts are normalized while parsing; trailing bytes are rejected by
`decodeAdmissionTrace`. -/
private def parseAdmissionTrace : Parser AdmissionTraceCertificate := do
  if (← readByte) ≠ admissionCertificateVersion then failure
  let canonicalRequest ← readBytes
  let nonceDocument ← readBytes
  let nonceGenesis ← readBytes
  let nonceIssuer ← readUInt64
  let nonceKeyEpoch ← readUInt64
  let nonce ← readBytes
  let operationDocument ← readBytes
  let operationGenesis ← readBytes
  let operationId ← readBytes
  let contextCommitment ← readBytes
  let executionBinding ← readHash
  let resolverPolicy ← readUInt64
  let authorityPolicy ← readUInt64
  let membershipPolicy ← readUInt64
  let previousAdmissionCommitment ← readOptional readHash
  let signatureAlgorithm ← readByte
  let signingBytes ← readBytes
  let signature ← readBytes
  let childStable ← readBytes
  let childIndex ← readUInt64
  let destinationStable ← readOptional readBytes
  let destinationIndex ← readOptional readUInt64
  let lamport ← readUInt64
  let replica ← readUInt64
  let cite ← readUInt64
  let resolvedMove ← readStoredMove
  let executionNodes ← readHashes
  let admission ← readKernelAdmission
  let projectionBound ← readUInt64
  let projectionResponse ← readBytes
  let formatV3Request ← readBytes
  let formatV3Response ← readBytes
  let selectedRequestSlot ← readUInt64
  let operationWasNew ← readBool
  readAcceptedReceipt
  readAcceptedReceipt
  readAcceptedReceipt
  readAcceptedReceipt
  readAcceptedReceipt
  pure {
    canonicalRequest, nonceDocument, nonceGenesis, nonceIssuer, nonceKeyEpoch,
    nonce, operationDocument, operationGenesis, operationId,
    contextCommitment, executionBinding, resolverPolicy, authorityPolicy,
    membershipPolicy, previousAdmissionCommitment, signatureAlgorithm,
    signingBytes, signature, childStable, childIndex, destinationStable,
    destinationIndex, lamport, replica, cite, resolvedMove, executionNodes,
    admission,
    projectionBound, projectionResponse, formatV3Request, formatV3Response,
    selectedRequestSlot, operationWasNew
  }

def decodeAdmissionTrace (bytes : Bytes) : Option AdmissionTraceCertificate :=
  match parseAdmissionTrace.run bytes with
  | some (certificate, []) => some certificate
  | _ => none

private def encodeUInt64 (value : UInt64) : Bytes :=
  (Uwueave.Exec.pushWord ByteArray.empty value).data.toList

private def encodeBytes (bytes : Bytes) : Bytes :=
  encodeUInt64 (UInt64.ofNat bytes.length) ++ bytes

private def encodeBool (value : Bool) : Bytes :=
  [if value then 1 else 0]

private def encodeOptional {α : Type} (encodeValue : α → Bytes) : Option α → Bytes
  | none => [0]
  | some value => 1 :: encodeValue value

private def encodeStoredMove (move : StoredMove) : Bytes :=
  encodeUInt64 move.lamport ++ encodeUInt64 move.replica ++ move.child ++
    encodeOptional id move.destination ++ encodeUInt64 move.cite

private def encodeHashes (hashes : List Bytes) : Bytes :=
  encodeUInt64 (UInt64.ofNat hashes.length) ++ hashes.flatten

private def encodeKernelAdmission : KernelAdmission → Bytes
  | .applied => [0]
  | .skippedCycle => [1]

/-- Exact mirror of Rust's v2 encoder, including the five normalized receipt
bytes.  Comparing this with the input makes the accepted envelope canonical,
independently of parser strictness. -/
def encodeAdmissionTrace (c : AdmissionTraceCertificate) : Bytes :=
  [admissionCertificateVersion] ++
  encodeBytes c.canonicalRequest ++
  encodeBytes c.nonceDocument ++ encodeBytes c.nonceGenesis ++
  encodeUInt64 c.nonceIssuer ++ encodeUInt64 c.nonceKeyEpoch ++
  encodeBytes c.nonce ++ encodeBytes c.operationDocument ++
  encodeBytes c.operationGenesis ++ encodeBytes c.operationId ++
  encodeBytes c.contextCommitment ++ c.executionBinding ++
  encodeUInt64 c.resolverPolicy ++ encodeUInt64 c.authorityPolicy ++
  encodeUInt64 c.membershipPolicy ++
  encodeOptional id c.previousAdmissionCommitment ++
  [c.signatureAlgorithm] ++ encodeBytes c.signingBytes ++
  encodeBytes c.signature ++ encodeBytes c.childStable ++
  encodeUInt64 c.childIndex ++ encodeOptional encodeBytes c.destinationStable ++
  encodeOptional encodeUInt64 c.destinationIndex ++
  encodeUInt64 c.lamport ++ encodeUInt64 c.replica ++ encodeUInt64 c.cite ++
  encodeStoredMove c.resolvedMove ++ encodeHashes c.executionNodes ++
  encodeKernelAdmission c.admission ++
  encodeUInt64 c.projectionBound ++ encodeBytes c.projectionResponse ++
  encodeBytes c.formatV3Request ++ encodeBytes c.formatV3Response ++
  encodeUInt64 c.selectedRequestSlot ++ encodeBool c.operationWasNew ++
  [1, 1, 1, 1, 1]

/-- The four count words describe exactly the supplied FORMAT-v3 request.
This check runs before any count-sized decoder allocation. -/
def formatV3Shape (bytes : Bytes) : Bool :=
  let input := bytes.toByteArray
  if bytes.length % 8 ≠ 0 ∨ bytes.length < 5 * 8 then false
  else
    let n := (Uwueave.Exec.getWord input 1).toNat
    let m := (Uwueave.Exec.getWord input 2).toNat
    let ng := (Uwueave.Exec.getWord input 3).toNat
    let nr := (Uwueave.Exec.getWord input 4).toNat
    bytes.length / 8 = 5 + n + m * 5 + ng * 3 + nr

def formatV3Canonical (bytes : Bytes) : Bool :=
  let input := bytes.toByteArray
  formatV3Shape bytes &&
    Uwueave.Exec.getWord input 0 == Uwueave.Exec.magicV3 &&
    (Uwueave.Exec.encodeRequest (Uwueave.Exec.decodeBase input)
      (Uwueave.Exec.decodeOps input) (Uwueave.Exec.decodeGrants input)
      (Uwueave.Exec.decodeRevs input)).data.toList == bytes

private def destinationLanesMatch (projection : AdmissionProjection)
    (stable : Option Bytes) (index : Option UInt64) : Bool :=
  match projection.destination, projection.execDestination, stable, index with
  | none, none, none, none => true
  | some node, some execIndex, some stableId, some storedIndex =>
      decide (node.stable = stableId ∧
        node.kernelIndex = storedIndex.toNat ∧ execIndex = storedIndex.toNat)
  | _, _, _, _ => false

/-- All projection-origin lanes are tied back to the one decoded kind-3
request and to the persisted Rust observation. -/
def projectionLanesMatch (c : AdmissionTraceCertificate)
    (request : ContextSignedRequest) (projection : AdmissionProjection) : Bool :=
  decide (projection = AdmissionProjection.ofRequest request ∧
  projection.canonicalRequest = c.canonicalRequest ∧
  projection.signingBytes = c.signingBytes ∧
  projection.signatureAlgorithm = c.signatureAlgorithm ∧
  projection.signature = c.signature ∧
  projection.document = c.nonceDocument ∧
  projection.document = c.operationDocument ∧
  projection.genesis = c.nonceGenesis ∧
  projection.genesis = c.operationGenesis ∧
  projection.contextCommitment = c.contextCommitment ∧
  projection.issuer = c.nonceIssuer ∧
  projection.keyEpoch = c.nonceKeyEpoch ∧
  projection.nonce = c.nonce ∧
  projection.operationId = c.operationId ∧
  projection.lamport = c.lamport ∧
  projection.child.stable = c.childStable ∧
  projection.child.kernelIndex = c.childIndex.toNat ∧
  destinationLanesMatch projection c.destinationStable c.destinationIndex = true ∧
  projection.execReplica = c.replica ∧
  projection.execChild = c.childIndex.toNat ∧
  projection.execDestination = c.destinationIndex.map UInt64.toNat ∧
  projection.execCite = c.cite.toNat ∧
  c.resolvedMove.lamport = c.lamport ∧
  c.resolvedMove.replica = c.replica ∧
  c.resolvedMove.cite = c.cite)

def resolvedNodesMatch (c : AdmissionTraceCertificate) : Bool :=
  (c.executionNodes[c.childIndex.toNat]? == some c.resolvedMove.child) &&
    match c.destinationIndex, c.resolvedMove.destination with
    | none, none => true
    | some index, some node => c.executionNodes[index.toNat]? == some node
    | _, _ => false

def expectedStatus : KernelAdmission → UInt64
  | .applied => 0
  | .skippedCycle => 1

def execOpsEqual (left right : Uwueave.Exec.Op) : Bool :=
  left.lamport == right.lamport && left.replica == right.replica &&
    left.child == right.child && left.dest == right.dest &&
    left.cite == right.cite

/-- Exact FORMAT-v3 replay, selected operation, and selected status checks. -/
def executionTraceMatches (c : AdmissionTraceCertificate)
    (request : ContextSignedRequest) : Bool :=
  let input := c.formatV3Request.toByteArray
  let response := c.formatV3Response.toByteArray
  let slot := c.selectedRequestSlot.toNat
  formatV3Canonical c.formatV3Request && resolvedNodesMatch c &&
    decide (c.executionNodes.length = (Uwueave.Exec.decodeBase input).size) &&
    c.formatV3Response == (Uwueave.Exec.replay input).data.toList &&
    decide (slot < (Uwueave.Exec.decodeOps input).size) &&
    (match (Uwueave.Exec.decodeOps input)[slot]? with
      | none => false
      | some operation =>
          execOpsEqual operation (RuntimeAuthV4.toExecOp request.toLegacy)) &&
    Uwueave.Exec.getWord response
      ((Uwueave.Exec.decodeBase input).size + slot) == expectedStatus c.admission

/-- Evidence retained by the checker after both canonical decoders and every
semantic comparison succeed. -/
structure AdmissionTraceEvidence (c : AdmissionTraceCertificate) where
  request : ContextSignedRequest
  projection : AdmissionProjection
  requestDecoded : decodeContextRequestBounded c.projectionBound.toNat
    c.canonicalRequest = .accepted request
  projectionDecoded : decodeAdmissionResponse c.projectionResponse =
    some (.accepted projection)
  exactProjection : c.projectionResponse =
    projectAdmissionBytes c.projectionBound.toNat c.canonicalRequest
  exactProjectionBound : c.projectionBound.toNat = c.canonicalRequest.length
  projectionBounded : c.projectionBound.toNat ≤ maximumProjectionBytes
  nonzeroCitation : c.cite ≠ 0
  projectionLanes : projectionLanesMatch c request projection = true
  executionTrace : executionTraceMatches c request = true

/-- The exact kind-4 response evidence exposes the decision-layer result,
not merely a successful response decoder. -/
theorem AdmissionTraceEvidence.projectAdmission_eq
    {c : AdmissionTraceCertificate} (evidence : AdmissionTraceEvidence c) :
    projectAdmission c.projectionBound.toNat c.canonicalRequest =
      .accepted evidence.projection := by
  have h := decode_projectAdmissionBytes c.projectionBound.toNat
    c.canonicalRequest
  rw [← evidence.exactProjection, evidence.projectionDecoded] at h
  exact (Option.some.inj h).symm

theorem execOpsEqual_eq_true_iff (left right : Uwueave.Exec.Op) :
    execOpsEqual left right = true ↔ left = right := by
  constructor
  · intro h
    simp only [execOpsEqual, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩
    cases left
    cases right
    simp_all
  · intro h
    subst right
    simp [execOpsEqual]

/-- A checker witness selects an in-range FORMAT-v3 request slot containing
exactly the signed request's `toExecOp`, and the response word in that slot is
exactly the certificate's `0` (applied) or `1` (cycle-skipped) admission. -/
theorem AdmissionTraceEvidence.execution_exact
    {c : AdmissionTraceCertificate} (evidence : AdmissionTraceEvidence c) :
    let input := c.formatV3Request.toByteArray
    let slot := c.selectedRequestSlot.toNat
    formatV3Canonical c.formatV3Request = true ∧
    resolvedNodesMatch c = true ∧
    c.executionNodes.length = (Uwueave.Exec.decodeBase input).size ∧
    c.formatV3Response = (Uwueave.Exec.replay input).data.toList ∧
    slot < (Uwueave.Exec.decodeOps input).size ∧
    (Uwueave.Exec.decodeOps input)[slot]? =
      some (RuntimeAuthV4.toExecOp evidence.request.toLegacy) ∧
    Uwueave.Exec.getWord c.formatV3Response.toByteArray
      ((Uwueave.Exec.decodeBase input).size + slot) =
        expectedStatus c.admission := by
  have hexecution := evidence.executionTrace
  simp only [executionTraceMatches, Bool.and_eq_true, beq_iff_eq] at hexecution
  rcases hexecution with
    ⟨⟨⟨⟨⟨⟨hcanonical, hnodes⟩, hnodeLength⟩, hresponse⟩, hslot⟩,
      hop⟩, hstatus⟩
  have hnodeLength' := of_decide_eq_true hnodeLength
  have hslot' := of_decide_eq_true hslot
  refine ⟨hcanonical, hnodes, hnodeLength', hresponse, hslot', ?_, hstatus⟩
  cases hget : (Uwueave.Exec.decodeOps c.formatV3Request.toByteArray)[
      c.selectedRequestSlot.toNat]? with
  | none => simp [hget] at hop
  | some operation =>
      have heq : operation =
          RuntimeAuthV4.toExecOp evidence.request.toLegacy :=
        (execOpsEqual_eq_true_iff _ _).mp (by simpa [hget] using hop)
      simp [heq]

theorem expectedStatus_eq_zero_or_one (admission : KernelAdmission) :
    expectedStatus admission = 0 ∨ expectedStatus admission = 1 := by
  cases admission <;> simp [expectedStatus]

def admissionTraceEvidence? (c : AdmissionTraceCertificate) :
    Option (AdmissionTraceEvidence c) :=
  match hrequest : decodeContextRequestBounded c.projectionBound.toNat
      c.canonicalRequest with
  | .refused _ => none
  | .accepted request =>
      match hprojection : decodeAdmissionResponse c.projectionResponse with
      | some (.accepted projection) =>
          if hexact : c.projectionResponse =
              projectAdmissionBytes c.projectionBound.toNat c.canonicalRequest then
            if hboundExact : c.projectionBound.toNat = c.canonicalRequest.length then
              if hbound : c.projectionBound.toNat ≤ maximumProjectionBytes then
                if hcite : c.cite ≠ 0 then
                  if hlanes : projectionLanesMatch c request projection = true then
                    if hexecution : executionTraceMatches c request = true then
                      some ⟨request, projection, hrequest, hprojection, hexact,
                        hboundExact, hbound, hcite, hlanes, hexecution⟩
                    else none
                  else none
                else none
              else none
            else none
          else none
      | _ => none

structure CheckedAdmissionTrace where
  certificate : AdmissionTraceCertificate
  evidence : AdmissionTraceEvidence certificate

def checkAdmissionTrace? (input : Bytes) : Option CheckedAdmissionTrace :=
  if input.length ≤ maximumCertificateBytes then
    match decodeAdmissionTrace input with
    | none => none
    | some certificate =>
        if encodeAdmissionTrace certificate = input then
          match admissionTraceEvidence? certificate with
          | none => none
          | some evidence => some ⟨certificate, evidence⟩
        else none
  else none

def checkAdmissionTrace (input : ByteArray) : Bool :=
  (checkAdmissionTrace? input.data.toList).isSome

/-- The exported one-byte success result cannot occur without a canonical v2
certificate and concrete evidence for the exact kind-3 → kind-4 → FORMAT-v3
trace checked above. -/
theorem checkAdmissionTrace_sound {input : Bytes}
    (h : (checkAdmissionTrace? input).isSome = true) :
    ∃ checked, checkAdmissionTrace? input = some checked := by
  cases hcheck : checkAdmissionTrace? input with
  | none => simp [hcheck] at h
  | some checked => exact ⟨checked, rfl⟩

@[export uwueave_runtime_auth_v4_check_admission_trace]
def checkAdmissionTraceKernel (input : ByteArray) : ByteArray :=
  ByteArray.empty.push (if checkAdmissionTrace input then 1 else 0)

end Uwueave.RuntimeAuthV4AdmissionTraceKernel
