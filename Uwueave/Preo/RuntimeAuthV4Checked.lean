/-
# Uwueave.Preo.RuntimeAuthV4Checked — proof-indexed sidecar construction

This proof-rich leaf is the only bridge from the existing runtime-auth model
to neutral sidecar rows.  It consumes `RuntimeAuthV4.ReadyForExecution` for
the exact signed request plus an exact active-grant receipt.  The former's
`authorized` and `isMember` fields remain independent caller premises; the
grant receipt proves only active citation and scope coverage, not issuer
possession or holder authorization. Decoded rows have no constructor back
into either proof object.

Context digests and origin/version identities remain caller-authored opaque
bindings, never verified values. `ContextReceipt` proves only the finite
membership statements it stores; it does not claim that the list exhausts a
deployment's membership.
-/
import Uwueave.Preo.RuntimeAuthV4Data
import Uwueave.RuntimeAuthV4
import Uwueave.Gated
import Uwueave.AuthenticatedFrontier

namespace Uwueave.Preo.RuntimeAuthV4

open Uwueave

set_option autoImplicit false

def NodeRow.ofRequest (node : Uwueave.RuntimeAuthV4.NodeRef) : NodeRow :=
  ⟨node.stable, node.kernelIndex⟩

/-- Exact first-order projection of every signed-request field.  UInt8/UInt64
values are widened with `toNat`; no narrowing or truncation occurs. -/
def SignedMoveRow.ofRequest (request : Uwueave.RuntimeAuthV4.SignedRequest) :
    SignedMoveRow where
  document := request.content.document
  genesis := request.content.genesis
  signatureAlgorithm := request.content.signatureAlgorithm.toNat
  issuer := request.content.issuer.toNat
  keyEpoch := request.content.keyEpoch.toNat
  nonce := request.content.nonce
  operationId := request.content.move.operationId
  lamport := request.content.move.lamport.toNat
  child := NodeRow.ofRequest request.content.move.child
  destination := request.content.move.dest.map NodeRow.ofRequest
  cite := request.content.move.cite
  signature := request.signature

@[simp] theorem SignedMoveRow.ofRequest_signatureAlgorithm
    (request : Uwueave.RuntimeAuthV4.SignedRequest) :
    (SignedMoveRow.ofRequest request).signatureAlgorithm =
      request.content.signatureAlgorithm.toNat := rfl

@[simp] theorem SignedMoveRow.ofRequest_issuer
    (request : Uwueave.RuntimeAuthV4.SignedRequest) :
    (SignedMoveRow.ofRequest request).issuer = request.content.issuer.toNat := rfl

@[simp] theorem SignedMoveRow.ofRequest_keyEpoch
    (request : Uwueave.RuntimeAuthV4.SignedRequest) :
    (SignedMoveRow.ofRequest request).keyEpoch = request.content.keyEpoch.toNat := rfl

@[simp] theorem SignedMoveRow.ofRequest_lamport
    (request : Uwueave.RuntimeAuthV4.SignedRequest) :
    (SignedMoveRow.ofRequest request).lamport = request.content.move.lamport.toNat := rfl

/-- The exact active grant and scope exercised by the signed request. -/
structure GrantReceipt (request : Uwueave.RuntimeAuthV4.SignedRequest) where
  state : Gated.GatedState
  grant : Authority.Grant
  active : Authority.Active (Gated.grants state) (Gated.revoked state) grant
  parent_lt_id : grant.2.1 < grant.1
  cite_exact : request.content.move.cite = grant.1
  child_covered : Gated.covers grant.2.2
    ⟨request.content.move.lamport.toNat,
      request.content.move.child.kernelIndex,
      match request.content.move.dest with
      | none => none
      | some node => some node.kernelIndex,
      request.content.move.cite⟩

def GrantReceipt.toRow {request : Uwueave.RuntimeAuthV4.SignedRequest}
    (receipt : GrantReceipt request) : GrantScopeRow :=
  ⟨receipt.grant.1, receipt.grant.2.1, receipt.grant.2.2⟩

@[simp] theorem GrantReceipt.toRow_id
    {request : Uwueave.RuntimeAuthV4.SignedRequest}
    (receipt : GrantReceipt request) :
    receipt.toRow.id = request.content.move.cite := receipt.cite_exact.symm

/-- Finite context attached to one exact request.  Opaque identities are
retained verbatim. -/
structure ContextReceipt (request : Uwueave.RuntimeAuthV4.SignedRequest) where
  substrateDigest : Digest
  historyHeadDigest : Digest
  originId : StableId
  versionId : StableId
  roster : List Nat
  participants : List Nat
  substrate_nonempty : ¬ substrateDigest.isEmpty
  history_head_nonempty : ¬ historyHeadDigest.isEmpty
  origin_nonempty : ¬ originId.isEmpty
  version_nonempty : ¬ versionId.isEmpty
  roster_canonical : roster.Pairwise (· < ·)
  participants_canonical : participants.Pairwise (· < ·)
  issuer_mem : request.content.issuer.toNat ∈ roster
  participants_mem : ∀ participant ∈ participants, participant ∈ roster

/-- Bind a move's finite roster to an independently authenticated progress
issuer.  The explicit equality is load-bearing: the two signed protocols use
different record carriers and are never silently identified. -/
def ContextReceipt.ofAuthenticatedProgress
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {roster : List Evidence.Source}
    (request : Uwueave.RuntimeAuthV4.SignedRequest)
    (progress : AuthenticatedFrontier.AuthenticatedProgress scheme keys
      keyRevocations issued received roster)
    (issuer_exact : request.content.issuer.toNat = progress.source)
    (participants : List Nat)
    (roster_canonical : roster.Pairwise (· < ·))
    (participants_canonical : participants.Pairwise (· < ·))
    (participants_mem : ∀ participant ∈ participants, participant ∈ roster)
    (substrateDigest historyHeadDigest originId versionId : StableId) :
    (¬ substrateDigest.isEmpty) → (¬ historyHeadDigest.isEmpty) →
    (¬ originId.isEmpty) → (¬ versionId.isEmpty) →
    ContextReceipt request :=
  fun substrate_nonempty history_head_nonempty origin_nonempty version_nonempty =>
  { substrateDigest
    historyHeadDigest
    originId
    versionId
    roster
    participants
    substrate_nonempty
    history_head_nonempty
    origin_nonempty
    version_nonempty
    roster_canonical
    participants_canonical
    issuer_mem := issuer_exact ▸ progress.issuer_mem_roster
    participants_mem }

/-- A proof-indexed sidecar producer.  The private constructor prevents a
neutral decoded manifest from masquerading as checked input. -/
structure CheckedManifest
    {boundary : Uwueave.RuntimeAuthV4.VerificationBoundary}
    {resolver : Uwueave.RuntimeAuthV4.ResolverBoundary}
    {authority membership : Uwueave.RuntimeAuthV4.SignedRequest → Prop}
    {seen : List Uwueave.RuntimeAuthV4.SignedRequest}
    (request : Uwueave.RuntimeAuthV4.SignedRequest) where private mk ::
  ready : Uwueave.RuntimeAuthV4.ReadyForExecution boundary resolver authority
    membership seen request
  shape : Uwueave.RuntimeAuthV4.validateShape request = .ok request
  grant : GrantReceipt request
  context : ContextReceipt request

def CheckedManifest.ofReady
    {boundary : Uwueave.RuntimeAuthV4.VerificationBoundary}
    {resolver : Uwueave.RuntimeAuthV4.ResolverBoundary}
    {authority membership : Uwueave.RuntimeAuthV4.SignedRequest → Prop}
    {seen : List Uwueave.RuntimeAuthV4.SignedRequest}
    (request : Uwueave.RuntimeAuthV4.SignedRequest)
    (ready : Uwueave.RuntimeAuthV4.ReadyForExecution boundary resolver authority
      membership seen request)
    (shape : Uwueave.RuntimeAuthV4.validateShape request = .ok request)
    (grant : GrantReceipt request) (context : ContextReceipt request) :
    CheckedManifest (boundary := boundary) (resolver := resolver)
      (authority := authority) (membership := membership) (seen := seen) request :=
  ⟨ready, shape, grant, context⟩

def CheckedManifest.toManifest
    {boundary : Uwueave.RuntimeAuthV4.VerificationBoundary}
    {resolver : Uwueave.RuntimeAuthV4.ResolverBoundary}
    {authority membership : Uwueave.RuntimeAuthV4.SignedRequest → Prop}
    {seen : List Uwueave.RuntimeAuthV4.SignedRequest}
    {request : Uwueave.RuntimeAuthV4.SignedRequest}
    (checked : CheckedManifest (boundary := boundary) (resolver := resolver)
      (authority := authority) (membership := membership) (seen := seen) request) :
    Manifest :=
  Manifest.ofRows (SignedMoveRow.ofRequest request)
    { citedGrant := checked.grant.toRow
      substrateDigest := checked.context.substrateDigest
      historyHeadDigest := checked.context.historyHeadDigest
      originId := checked.context.originId
      versionId := checked.context.versionId
      roster := checked.context.roster
      participants := checked.context.participants }

@[simp] theorem CheckedManifest.toManifest_move
    {boundary : Uwueave.RuntimeAuthV4.VerificationBoundary}
    {resolver : Uwueave.RuntimeAuthV4.ResolverBoundary}
    {authority membership : Uwueave.RuntimeAuthV4.SignedRequest → Prop}
    {seen : List Uwueave.RuntimeAuthV4.SignedRequest}
    {request : Uwueave.RuntimeAuthV4.SignedRequest}
    (checked : CheckedManifest (boundary := boundary) (resolver := resolver)
      (authority := authority) (membership := membership) (seen := seen) request) :
    checked.toManifest.move = SignedMoveRow.ofRequest request := rfl

/-- The checked producer retains the exact canonical bytes which its
`ReadyForExecution.verified` premise authenticated.  These bytes are not the
manifest sidecar bytes. -/
def CheckedManifest.sourceSigningBytes
    {boundary : Uwueave.RuntimeAuthV4.VerificationBoundary}
    {resolver : Uwueave.RuntimeAuthV4.ResolverBoundary}
    {authority membership : Uwueave.RuntimeAuthV4.SignedRequest → Prop}
    {seen : List Uwueave.RuntimeAuthV4.SignedRequest}
    {request : Uwueave.RuntimeAuthV4.SignedRequest}
    (_checked : CheckedManifest (boundary := boundary) (resolver := resolver)
      (authority := authority) (membership := membership) (seen := seen) request) :
    Durable.Bytes :=
  Uwueave.RuntimeAuthV4.signingBytesV4 request.content

@[simp] theorem CheckedManifest.sourceSigningBytes_exact
    {boundary : Uwueave.RuntimeAuthV4.VerificationBoundary}
    {resolver : Uwueave.RuntimeAuthV4.ResolverBoundary}
    {authority membership : Uwueave.RuntimeAuthV4.SignedRequest → Prop}
    {seen : List Uwueave.RuntimeAuthV4.SignedRequest}
    {request : Uwueave.RuntimeAuthV4.SignedRequest}
    (checked : CheckedManifest (boundary := boundary) (resolver := resolver)
      (authority := authority) (membership := membership) (seen := seen) request) :
    checked.sourceSigningBytes =
      Uwueave.RuntimeAuthV4.signingBytesV4 request.content := rfl

end Uwueave.Preo.RuntimeAuthV4
