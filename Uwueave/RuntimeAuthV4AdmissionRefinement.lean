/-
# Uwueave.RuntimeAuthV4AdmissionRefinement — proof-only FORMAT-v4 refinement

This leaf connects the canonical FORMAT-v4 admission projection to the
abstract authenticated grant gate.  It is intentionally absent from the
runtime export closure: importing it must not make the native admission
kernel depend on `Authenticity`, `AuthenticatedAdmission`, or `Gated`.

The concrete signature scheme and key lifecycle are not reconstructed here.
`CryptoAdapter` is the explicit U-0001 premise which transports a successful
host verification of the exact context-bound request (in either canonical
fixed-width binary Lamport form or legacy unary Lamport form) into the
abstract `Authenticity` model.  The remaining proofs are structural: canonical
origin, field projection, and the safety-only reading of FORMAT-v3 status 0/1.

This is a conditional model bridge, not a shipping-trace refinement theorem.
In particular, nothing here proves that Rust `AuthenticatedRuntime.admit` or
`recover`, an authority/context provider, the FFI response parser, or compiled
native execution supplies the premises of the final constructor.  Establishing
that concrete trace relation remains the U-0052 shipping obligation.
-/
import Uwueave.RuntimeAuthV4Kernel
import Uwueave.AuthenticatedAdmission

namespace Uwueave.RuntimeAuthV4AdmissionRefinement

open Uwueave
open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel
open Uwueave.AuthenticatedAdmission

set_option autoImplicit false

/-! ## Exact semantic projection -/

/-- The four signed move fields, with only the representation changes already
used by the FORMAT-v3 execution carrier. -/
def claimOf (request : ContextSignedRequest) : Authenticity.MoveClaim where
  t := request.content.move.lamport.toNat
  node := request.content.move.child.kernelIndex
  dest := request.content.move.dest.map NodeRef.kernelIndex
  cite := request.content.move.cite

/-- The abstract move claim is exactly the gate operation denoted by the
projected FORMAT-v3 operation. -/
theorem claimOf_toGOp_exact (request : ContextSignedRequest) :
    moveClaimToGOp (claimOf request) =
      Gated.gopOf (toExecOp request.toLegacy) := by
  cases hdest : request.content.move.dest with
  | none =>
      simp [claimOf, moveClaimToGOp, Gated.gopOf, toExecOp,
        ContextSignedRequest.toLegacy, destinationIndex, hdest]
  | some destination =>
      simp [claimOf, moveClaimToGOp, Gated.gopOf, toExecOp,
        ContextSignedRequest.toLegacy, destinationIndex, hdest]

/-! ## Canonical accepted origin -/

/-- A format-preserving bounded decode can accept only the canonical encoding
of the `(request, fmt)` pair it returns. -/
theorem accepted_decode_with_format_has_canonical_origin (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (fmt : LamportWireFormat)
    (request : ContextSignedRequest)
    (haccepted : decodeContextRequestWithFormatBounded maximumBytes bytes =
      .accepted fmt request) :
    bytes = encodeContextRequestAt fmt request := by
  unfold decodeContextRequestWithFormatBounded at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  next hheader =>
    split at haccepted <;> try contradiction
    next hdecode =>
      injection haccepted with hfmt hrequest
      subst hfmt
      subst hrequest
      exact (contextRequestAnyCodec.encode_decode hdecode).symm

/-- Every accepted bounded decode originates from a unique `(request, fmt)`
encoding. -/
theorem accepted_decode_has_canonical_origin (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (request : ContextSignedRequest)
    (haccepted : decodeContextRequestBounded maximumBytes bytes =
      .accepted request) :
    ∃ fmt : LamportWireFormat, bytes = encodeContextRequestAt fmt request := by
  unfold decodeContextRequestBounded at haccepted
  cases hraw : decodeContextRequestWithFormatBounded maximumBytes bytes with
  | refused _ =>
      rw [hraw] at haccepted
      cases haccepted
  | accepted fmt rawRequest =>
      rw [hraw] at haccepted
      injection haccepted with hreq
      subst hreq
      exact ⟨fmt, accepted_decode_with_format_has_canonical_origin
        maximumBytes bytes fmt rawRequest hraw⟩

theorem encodeContextRequest_injective :
    Function.Injective encodeContextRequest := by
  intro left right hencode
  exact (encodeContextRequestAt_injective
    (fmt₁ := .fixedLe) (fmt₂ := .fixedLe) hencode).1

private theorem validateContextShape_ok_eq
    {request shaped : ContextSignedRequest}
    (h : validateContextShape request = .ok shaped) : shaped = request := by
  by_cases hdocument : request.content.document.isEmpty
  · simp [validateContextShape, hdocument] at h
  by_cases hgenesis : request.content.genesis.isEmpty
  · simp [validateContextShape, hdocument, hgenesis] at h
  by_cases hcontext : request.content.contextCommitment.isEmpty
  · simp [validateContextShape, hdocument, hgenesis, hcontext] at h
  by_cases hnonce : request.content.nonce.isEmpty
  · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce] at h
  by_cases hop : request.content.move.operationId.isEmpty
  · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce,
      hop] at h
  by_cases hchild : request.content.move.child.stable.isEmpty
  · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce,
      hop, hchild] at h
  cases hdestination : request.content.move.dest with
  | none =>
      by_cases hsignature : request.signature.isEmpty
      · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce,
          hop, hchild, hdestination, hsignature] at h
      · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce,
          hop, hchild, hdestination, hsignature] at h
        exact h.symm
  | some destination =>
      by_cases hstable : destination.stable.isEmpty
      · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce,
          hop, hchild, hdestination, hstable] at h
      by_cases hsignature : request.signature.isEmpty
      · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce,
          hop, hchild, hdestination, hstable, hsignature] at h
      · simp [validateContextShape, hdocument, hgenesis, hcontext, hnonce,
          hop, hchild, hdestination, hstable, hsignature] at h
        exact h.symm

private theorem validateHostWidths_ok_eq
    {request checked : ContextSignedRequest}
    (h : validateHostWidths request = .ok checked) : checked = request := by
  by_cases hchild : request.content.move.child.kernelIndex ≤ maximumUInt64Nat
  · cases hdestination : request.content.move.dest with
    | none =>
        by_cases hcite : request.content.move.cite ≤ maximumUInt64Nat
        · simp [validateHostWidths, hchild, hdestination, hcite] at h
          exact h.symm
        · simp [validateHostWidths, hchild, hdestination, hcite] at h
    | some destination =>
        by_cases hdestWidth : destination.kernelIndex ≤ maximumInt64Nat
        · by_cases hcite : request.content.move.cite ≤ maximumUInt64Nat
          · simp [validateHostWidths, hchild, hdestination, hdestWidth,
              hcite] at h
            exact h.symm
          · simp [validateHostWidths, hchild, hdestination, hdestWidth,
              hcite] at h
        · simp [validateHostWidths, hchild, hdestination, hdestWidth] at h
  · simp [validateHostWidths, hchild] at h

/-- Every accepted projection has one and only one canonical kind-3 request and
wire format as its origin.  Both the submitted bytes and every projection field
remain bound to that exact `(request, fmt)` pair. -/
theorem accepted_projection_unique_canonical_origin (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (projection : AdmissionProjection)
    (haccepted : projectAdmission maximumBytes bytes = .accepted projection) :
    ∃ (fmt : LamportWireFormat) (request : ContextSignedRequest),
      (bytes = encodeContextRequestAt fmt request ∧
        projection = AdmissionProjection.ofRequestAt fmt request) ∧
      ∀ (otherFmt : LamportWireFormat) (other : ContextSignedRequest),
        bytes = encodeContextRequestAt otherFmt other ∧
          projection = AdmissionProjection.ofRequestAt otherFmt other →
        otherFmt = fmt ∧ other = request := by
  unfold projectAdmission projectAdmissionWithFormat at haccepted
  split at haccepted <;> try contradiction
  next fmt request hdecode =>
    split at haccepted <;> try contradiction
    next shaped hshape =>
      split at haccepted <;> try contradiction
      next checked hwidth =>
        simp only [FormattedAdmissionOutcome.toOutcome] at haccepted
        injection haccepted with hprojection
        have hshapeEq : shaped = request := validateContextShape_ok_eq hshape
        have hwidthEq : checked = shaped := validateHostWidths_ok_eq hwidth
        subst shaped
        subst checked
        subst projection
        have horigin := accepted_decode_with_format_has_canonical_origin
          maximumBytes bytes fmt request hdecode
        refine ⟨fmt, request, ⟨⟨horigin, rfl⟩, ?_⟩⟩
        intro otherFmt other hother
        have hencode : encodeContextRequestAt fmt request =
            encodeContextRequestAt otherFmt other :=
          horigin.symm.trans hother.1
        obtain ⟨hreq, hfmt⟩ := encodeContextRequestAt_injective hencode
        exact ⟨hfmt.symm, hreq.symm⟩

/-- Once a caller names the canonical request bytes and wire format, acceptance
fixes the projection; it cannot be paired with a different request's fields or
wire format. -/
theorem accepted_projection_exact_of_canonical_origin_at
    (fmt : LamportWireFormat) (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (request : ContextSignedRequest)
    (projection : AdmissionProjection)
    (haccepted : projectAdmission maximumBytes bytes = .accepted projection)
    (horigin : bytes = encodeContextRequestAt fmt request) :
    projection = AdmissionProjection.ofRequestAt fmt request := by
  obtain ⟨originFmt, origin, ⟨hbytes, hprojection⟩, -⟩ :=
    accepted_projection_unique_canonical_origin maximumBytes bytes projection
      haccepted
  obtain ⟨hreq, hfmt⟩ :=
    encodeContextRequestAt_injective (hbytes.symm.trans horigin)
  subst hreq
  subst hfmt
  exact hprojection

theorem accepted_projection_exact_of_canonical_origin (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (request : ContextSignedRequest)
    (projection : AdmissionProjection)
    (haccepted : projectAdmission maximumBytes bytes = .accepted projection)
    (horigin : bytes = encodeContextRequest request) :
    projection = AdmissionProjection.ofRequest request :=
  accepted_projection_exact_of_canonical_origin_at .fixedLe maximumBytes bytes
    request projection haccepted horigin

/-! ## FORMAT-v3 status safety -/

/-- Status 0 (applied) or 1 (cycle-skipped) implies that the operation passed
the executable grant gate.  This is deliberately only the soundness
direction: it needs neither well-formed grants nor unique grant ids. -/
theorem status_zero_or_one_is_gated (grants : Array Exec.Grant)
    (revocations : Array Nat) (firstParent : Array Int)
    (operations : Array Exec.Op) (index : Nat) (hindex : index < operations.size)
    (hstatus :
      (Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 0 ∨
        (Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 1) :
    Gated.gatedOps (Gated.stateOf grants revocations operations)
      (Gated.gopOf operations[index]) := by
  have hnotRefused :
      (Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 ≠ 3 := by
    intro hrefused
    rcases hstatus with hzero | hone
    · omega
    · omega
  have hnotFalse :
      Exec.permittedOp grants revocations operations[index] ≠ false := by
    intro hfalse
    exact hnotRefused
      ((Exec.gated_status_eq_three_iff grants revocations firstParent operations
        hindex).2 hfalse)
  have hpermitted :
      Exec.permittedOp grants revocations operations[index] = true := by
    cases h : Exec.permittedOp grants revocations operations[index] <;>
      simp_all
  refine ⟨?_, Gated.kernel_permitted_sound operations hpermitted⟩
  show operations.any
      (fun operation => Gated.gopOf operation == Gated.gopOf operations[index]) =
    true
  rw [Array.any_eq_true']
  exact ⟨operations[index], by simp, by simp⟩

/-! ## Explicit U-0001 premise and the composed refinement -/

/-- The deployed verification predicate, stated over the three exact lanes the
host passes to its verifier.  Its cryptographic soundness belongs to U-0001. -/
structure HostVerificationBoundary where
  Accepts : UInt8 → RuntimeAuthV4Kernel.Bytes →
    RuntimeAuthV4Kernel.SignatureBytes → Prop

/-- Verification of one request is mechanically tied to its signed algorithm,
canonical kind-3 signing bytes under `fmt`, and literal signature bytes. -/
def HostVerifiedAt (boundary : HostVerificationBoundary)
    (fmt : LamportWireFormat) (request : ContextSignedRequest) : Prop :=
  boundary.Accepts request.content.signatureAlgorithm
    (contextSigningBytesAt fmt request.content) request.signature

def HostVerified (boundary : HostVerificationBoundary)
    (request : ContextSignedRequest) : Prop :=
  HostVerifiedAt boundary .fixedLe request

/-- U-0001's explicit adapter from deployed verification to the abstract
signature model.  In particular, this module never equates FORMAT-v4's byte
encoding with `Authenticity.signingMessage`; a deployment supplies the
translation and its soundness. -/
structure CryptoAdapter
    (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop)
    (boundary : HostVerificationBoundary) where
  recordOf : ContextSignedRequest → Authenticity.SignedRecord scheme
  issuer_exact : ∀ request,
    (recordOf request).issuer = request.content.issuer.toNat
  keyEpoch_exact : ∀ request,
    (recordOf request).keyEpoch = request.content.keyEpoch.toNat
  payload_exact : ∀ request,
    (recordOf request).payload = .move (claimOf request)
  received_of_hostVerified : ∀ fmt request,
    HostVerifiedAt boundary fmt request → received (recordOf request)
  accepted_of_hostVerified : ∀ fmt request,
    HostVerifiedAt boundary fmt request →
      Authenticity.Accepted scheme keys keyRevocations (recordOf request)
  authenticIssuer : Authenticity.AuthenticIssuer scheme keys keyRevocations
    issued received

/-- The deployment context whose identity must survive the projection into
the smaller authentication/gate vocabulary. -/
structure AdmissionScope where
  document : RuntimeAuthV4Kernel.StableId
  genesis : RuntimeAuthV4Kernel.StableId
  contextCommitment : RuntimeAuthV4Kernel.StableId
  deriving DecidableEq, Repr

def scopeOf (request : ContextSignedRequest) : AdmissionScope where
  document := request.content.document
  genesis := request.content.genesis
  contextCommitment := request.content.contextCommitment

/-- The final result retains the complete FORMAT-v4 request, wire format, and
projection, not merely the four fields remembered by `AuthenticatedGatedOp`. -/
structure RefinedHostAdmission
    (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop)
    (holder : GrantHolder)
    (grants : Array Exec.Grant) (revocations : Array Nat)
    (operations : Array Exec.Op) where
  wireFormat : LamportWireFormat
  maximumBytes : Nat
  submittedBytes : RuntimeAuthV4Kernel.Bytes
  request : ContextSignedRequest
  projection : AdmissionProjection
  scope : AdmissionScope
  projected : projectAdmission maximumBytes submittedBytes = .accepted projection
  canonical_origin : submittedBytes = encodeContextRequestAt wireFormat request
  projection_exact : projection = AdmissionProjection.ofRequestAt wireFormat request
  scope_exact : scope = scopeOf request
  projection_document_exact : projection.document = scope.document
  projection_genesis_exact : projection.genesis = scope.genesis
  projection_context_exact :
    projection.contextCommitment = scope.contextCommitment
  authenticated : AuthenticatedGatedOp scheme keys keyRevocations issued received
    holder (Gated.stateOf grants revocations operations)
  authenticated_record_issuer :
    authenticated.record.issuer = request.content.issuer.toNat
  authenticated_record_keyEpoch :
    authenticated.record.keyEpoch = request.content.keyEpoch.toNat
  authenticated_claim_exact : authenticated.claim = claimOf request

/-- **Conditional model bridge.** Given an accepted canonical FORMAT-v4
projection (under either `.fixedLe` or `.legacyUnary`), U-0001 authentication
receipt, holder proof, exact execution-op identity, and a model status 0/1,
construct an authenticated gated operation while retaining the entire signed
FORMAT-v4 scope. -/
def hostAdmission_refines_authenticatedGatedOpAt
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {holder : GrantHolder}
    {boundary : HostVerificationBoundary}
    (crypto : CryptoAdapter scheme keys keyRevocations issued received
      boundary)
    (fmt : LamportWireFormat)
    (maximumBytes : Nat) (submittedBytes : RuntimeAuthV4Kernel.Bytes)
    (request : ContextSignedRequest)
    (projection : AdmissionProjection)
    (hprojected : projectAdmission maximumBytes submittedBytes =
      .accepted projection)
    (horigin : submittedBytes = encodeContextRequestAt fmt request)
    (hverification : HostVerifiedAt boundary fmt request)
    (hholder : holder request.content.issuer.toNat
      request.content.move.cite)
    (grants : Array Exec.Grant) (revocations : Array Nat)
    (firstParent : Array Int) (operations : Array Exec.Op)
    (index : Nat) (hindex : index < operations.size)
    (hexecution : operations[index] = toExecOp request.toLegacy)
    (hstatus :
      (Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 0 ∨
        (Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 1) :
    RefinedHostAdmission scheme keys keyRevocations issued received holder
      grants revocations operations := by
  have hprojection := accepted_projection_exact_of_canonical_origin_at fmt
    maximumBytes submittedBytes request projection hprojected horigin
  let record := crypto.recordOf request
  have hgatedAtIndex := status_zero_or_one_is_gated grants revocations
    firstParent operations index hindex hstatus
  have hgated : Gated.gatedOps (Gated.stateOf grants revocations operations)
      (moveClaimToGOp (claimOf request)) := by
    rw [claimOf_toGOp_exact, ← hexecution]
    exact hgatedAtIndex
  let hauthenticated :
      AuthenticatedGatedOp scheme keys keyRevocations issued received holder
        (Gated.stateOf grants revocations operations) :=
    AuthenticatedGatedOp.ofAuthenticIssuer crypto.authenticIssuer record
      (claimOf request) (crypto.payload_exact request)
      (crypto.received_of_hostVerified fmt request hverification)
      (crypto.accepted_of_hostVerified fmt request hverification)
      (by simpa [record, crypto.issuer_exact request] using
        hholder)
      hgated
  exact
    { wireFormat := fmt
      maximumBytes := maximumBytes
      submittedBytes := submittedBytes
      request := request
      projection := projection
      scope := scopeOf request
      projected := hprojected
      canonical_origin := horigin
      projection_exact := hprojection
      scope_exact := rfl
      projection_document_exact := by simp [hprojection, scopeOf,
        AdmissionProjection.ofRequestAt]
      projection_genesis_exact := by simp [hprojection, scopeOf,
        AdmissionProjection.ofRequestAt]
      projection_context_exact := by simp [hprojection, scopeOf,
        AdmissionProjection.ofRequestAt]
      authenticated := hauthenticated
      authenticated_record_issuer := by
        simpa [hauthenticated, record,
          AuthenticatedGatedOp.ofAuthenticIssuer] using
            crypto.issuer_exact request
      authenticated_record_keyEpoch := by
        simpa [hauthenticated, record,
          AuthenticatedGatedOp.ofAuthenticIssuer] using
            crypto.keyEpoch_exact request
      authenticated_claim_exact := by
        simp [hauthenticated, record, AuthenticatedGatedOp.ofAuthenticIssuer] }

def hostAdmission_refines_authenticatedGatedOp
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {holder : GrantHolder}
    {boundary : HostVerificationBoundary}
    (crypto : CryptoAdapter scheme keys keyRevocations issued received
      boundary)
    (maximumBytes : Nat) (submittedBytes : RuntimeAuthV4Kernel.Bytes)
    (request : ContextSignedRequest)
    (projection : AdmissionProjection)
    (hprojected : projectAdmission maximumBytes submittedBytes =
      .accepted projection)
    (horigin : submittedBytes = encodeContextRequest request)
    (hverification : HostVerified boundary request)
    (hholder : holder request.content.issuer.toNat
      request.content.move.cite)
    (grants : Array Exec.Grant) (revocations : Array Nat)
    (firstParent : Array Int) (operations : Array Exec.Op)
    (index : Nat) (hindex : index < operations.size)
    (hexecution : operations[index] = toExecOp request.toLegacy)
    (hstatus :
      (Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 0 ∨
        (Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 1) :
    RefinedHostAdmission scheme keys keyRevocations issued received holder
      grants revocations operations :=
  hostAdmission_refines_authenticatedGatedOpAt crypto .fixedLe maximumBytes
    submittedBytes request projection hprojected horigin hverification hholder
    grants revocations firstParent operations index hindex hexecution hstatus

end Uwueave.RuntimeAuthV4AdmissionRefinement
