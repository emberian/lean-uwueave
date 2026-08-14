/-
# Uwueave.RuntimeAuthV4AdmissionRefinement — proof-only FORMAT-v4 refinement

This leaf connects the canonical FORMAT-v4 admission projection to the
abstract authenticated grant gate.  It is intentionally absent from the
runtime export closure: importing it must not make the native admission
kernel depend on `Authenticity`, `AuthenticatedAdmission`, or `Gated`.

The concrete signature scheme and key lifecycle are not reconstructed here.
`CryptoAdapter` is the explicit U-0001 premise which transports a successful
host verification of the exact context-bound request into the abstract
`Authenticity` model.  The remaining proofs are structural: canonical origin,
field projection, and the safety-only reading of FORMAT-v3 status 0/1.

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

/-- A bounded decode can accept only the canonical encoding of the request it
returns. -/
theorem accepted_decode_has_canonical_origin (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (request : ContextSignedRequest)
    (haccepted : decodeContextRequestBounded maximumBytes bytes =
      .accepted request) :
    bytes = encodeContextRequest request := by
  unfold decodeContextRequestBounded at haccepted
  split at haccepted <;> try contradiction
  split at haccepted <;> try contradiction
  next hheader =>
    split at haccepted <;> try contradiction
    next hdecode =>
      injection haccepted with hrequest
      subst hrequest
      exact (contextRequestCodec.encode_decode hdecode).symm

theorem encodeContextRequest_injective :
    Function.Injective encodeContextRequest := by
  intro left right hencode
  apply Option.some.inj
  calc
    some left = contextRequestCodec.decode (encodeContextRequest left) :=
      (contextRequest_roundtrip _).symm
    _ = contextRequestCodec.decode (encodeContextRequest right) :=
      congrArg contextRequestCodec.decode hencode
    _ = some right := contextRequest_roundtrip _

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

/-- Every accepted projection has one and only one canonical kind-3 request
as its origin.  Both the submitted bytes and every projection field remain
bound to that request. -/
theorem accepted_projection_unique_canonical_origin (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (projection : AdmissionProjection)
    (haccepted : projectAdmission maximumBytes bytes = .accepted projection) :
    ∃ request : ContextSignedRequest,
      (bytes = encodeContextRequest request ∧
        projection = AdmissionProjection.ofRequest request) ∧
      ∀ other : ContextSignedRequest,
        bytes = encodeContextRequest other ∧
          projection = AdmissionProjection.ofRequest other →
        other = request := by
  unfold projectAdmission at haccepted
  split at haccepted <;> try contradiction
  next request hdecode =>
    split at haccepted <;> try contradiction
    next shaped hshape =>
      split at haccepted <;> try contradiction
      next checked hwidth =>
        injection haccepted with hprojection
        have hshapeEq : shaped = request := validateContextShape_ok_eq hshape
        have hwidthEq : checked = shaped := validateHostWidths_ok_eq hwidth
        subst shaped
        subst checked
        subst projection
        refine ⟨request, ⟨⟨accepted_decode_has_canonical_origin
          maximumBytes bytes request hdecode, rfl⟩, ?_⟩⟩
        intro other hother
        have hencode : encodeContextRequest request =
            encodeContextRequest other :=
          (accepted_decode_has_canonical_origin maximumBytes bytes request
            hdecode).symm.trans hother.1
        exact (encodeContextRequest_injective hencode).symm

/-- Once a caller names the canonical request bytes, acceptance fixes the
projection; it cannot be paired with a different request's fields. -/
theorem accepted_projection_exact_of_canonical_origin (maximumBytes : Nat)
    (bytes : RuntimeAuthV4Kernel.Bytes) (request : ContextSignedRequest)
    (projection : AdmissionProjection)
    (haccepted : projectAdmission maximumBytes bytes = .accepted projection)
    (horigin : bytes = encodeContextRequest request) :
    projection = AdmissionProjection.ofRequest request := by
  obtain ⟨origin, ⟨hbytes, hprojection⟩, -⟩ :=
    accepted_projection_unique_canonical_origin maximumBytes bytes projection
      haccepted
  have : origin = request :=
    encodeContextRequest_injective (hbytes.symm.trans horigin)
  simpa [this] using hprojection

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
canonical kind-3 signing bytes, and literal signature bytes. -/
def HostVerified (boundary : HostVerificationBoundary)
    (request : ContextSignedRequest) : Prop :=
  boundary.Accepts request.content.signatureAlgorithm
    (contextSigningBytes request.content) request.signature

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
  received_of_hostVerified : ∀ request, HostVerified boundary request →
    received (recordOf request)
  accepted_of_hostVerified : ∀ request, HostVerified boundary request →
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

/-- The final result retains the complete FORMAT-v4 request and projection,
not merely the four fields remembered by `AuthenticatedGatedOp`.  Thus
document, genesis, context commitment, nonce, operation id, stable node ids,
algorithm, signature, and key epoch remain available through `request` and
are tied to `projection` by `projection_exact`. -/
structure RefinedHostAdmission
    (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop)
    (holder : GrantHolder)
    (grants : Array Exec.Grant) (revocations : Array Nat)
    (operations : Array Exec.Op) where
  maximumBytes : Nat
  submittedBytes : RuntimeAuthV4Kernel.Bytes
  request : ContextSignedRequest
  projection : AdmissionProjection
  scope : AdmissionScope
  projected : projectAdmission maximumBytes submittedBytes = .accepted projection
  canonical_origin : submittedBytes = encodeContextRequest request
  projection_exact : projection = AdmissionProjection.ofRequest request
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

/-- **Conditional model bridge only.** Given an accepted canonical FORMAT-v4
projection, U-0001 authentication receipt, holder proof, exact execution-op
identity, and a model status 0/1, construct an authenticated gated operation
while retaining the entire signed FORMAT-v4 scope.  This declaration does not
derive any premise from Rust `admit`/`recover` or from a shipping trace. -/
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
      grants revocations operations := by
  have hprojection := accepted_projection_exact_of_canonical_origin
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
      (crypto.received_of_hostVerified request hverification)
      (crypto.accepted_of_hostVerified request hverification)
      (by simpa [record, crypto.issuer_exact request] using
        hholder)
      hgated
  exact
    { maximumBytes := maximumBytes
      submittedBytes := submittedBytes
      request := request
      projection := projection
      scope := scopeOf request
      projected := hprojected
      canonical_origin := horigin
      projection_exact := hprojection
      scope_exact := rfl
      projection_document_exact := by simp [hprojection, scopeOf,
        AdmissionProjection.ofRequest]
      projection_genesis_exact := by simp [hprojection, scopeOf,
        AdmissionProjection.ofRequest]
      projection_context_exact := by simp [hprojection, scopeOf,
        AdmissionProjection.ofRequest]
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

end Uwueave.RuntimeAuthV4AdmissionRefinement
