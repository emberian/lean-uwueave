/-
# Uwueave.RuntimeAuthV4AdmissionTraceRefinement

Proof-only composition of the Lean admission-trace checker with the existing
conditional FORMAT-v4 authenticated-gate bridge.  The result retains the
complete checker-accepted v2 certificate, including `operationWasNew` as exact
provenance (either Boolean value is valid), and the checker evidence from which
the canonical projection and FORMAT-v3 execution premises are derived.

The five normalized stage-receipt bytes in a certificate are not proofs of
signature verification or holder policy.  `OperationalReceipts` supplies those
two exact relations, and `CryptoAdapter` remains the explicit U-0001 bridge
from deployed verification to the abstract authenticity model.

This module does not prove provider availability or honesty, `Authority.WF`,
`Authority.UniqueGrant`, completeness/equivalence of grant lookup, compiled
Rust/FFI/native trace fidelity, journal append durability, or recovery.  Those
remain separate shipping assumptions/obligations; no such claim is inferred
from checker acceptance.
-/
import Uwueave.RuntimeAuthV4AdmissionTraceKernel
import Uwueave.RuntimeAuthV4AdmissionRefinement

namespace Uwueave.RuntimeAuthV4AdmissionTraceRefinement

open Uwueave
open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel
open Uwueave.RuntimeAuthV4AdmissionTraceKernel
open Uwueave.RuntimeAuthV4AdmissionRefinement
open Uwueave.AuthenticatedAdmission

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The operational premises which byte checking deliberately cannot create.
Both predicates are stated over the exact request retained by the dependent
checker evidence, rather than over separately reconstructed host fields. -/
structure OperationalReceipts
    (boundary : HostVerificationBoundary)
    (holder : GrantHolder)
    (checked : CheckedAdmissionTrace) : Prop where
  hostVerified : HostVerified boundary checked.evidence.request
  holderAccepted : holder checked.evidence.request.content.issuer.toNat
    checked.evidence.request.content.move.cite

/-! ## FORMAT-v3 response word back to the decision layer -/

/-- The selected raw response word exposed by `execution_exact` is precisely
the selected status in `gatedReplayFull`.  This is the remaining output-codec
step needed by the pre-existing status-to-gate soundness theorem. -/
private theorem modelStatus_zero_or_one
    {c : AdmissionTraceCertificate} (evidence : AdmissionTraceEvidence c) :
    let input := c.formatV3Request.toByteArray
    let firstParent := Uwueave.Exec.decodeBase input
    let operations := Uwueave.Exec.decodeOps input
    let grants := Uwueave.Exec.decodeGrants input
    let revocations := Uwueave.Exec.decodeRevs input
    let index := c.selectedRequestSlot.toNat
    (Uwueave.Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 0 ∨
      (Uwueave.Exec.gatedReplayFull grants revocations firstParent operations).statuses.getD
          index 0 = 1 := by
  let input := c.formatV3Request.toByteArray
  let firstParent := Uwueave.Exec.decodeBase input
  let operations := Uwueave.Exec.decodeOps input
  let grants := Uwueave.Exec.decodeGrants input
  let revocations := Uwueave.Exec.decodeRevs input
  let index := c.selectedRequestSlot.toNat
  let replayed := Uwueave.Exec.gatedReplayFull grants revocations firstParent operations
  obtain ⟨hcanonical, -, -, hresponse, hindex, -, hword⟩ :=
    evidence.execution_exact
  have hmagic : Uwueave.Exec.getWord input 0 = Uwueave.Exec.magicV3 := by
    have h := hcanonical
    simp only [formatV3Canonical, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.2
  have hreplay : Uwueave.Exec.replay input =
      Uwueave.Exec.encodeView (replayed.overrides ++ replayed.statuses) := by
    simp [Uwueave.Exec.replay, hmagic, replayed, firstParent, operations,
      grants, revocations]
  have hresponseBytes : c.formatV3Response.toByteArray =
      Uwueave.Exec.encodeView (replayed.overrides ++ replayed.statuses) := by
    apply ByteArray.ext
    rw [List.data_toByteArray]
    rw [← hreplay]
    simpa using congrArg List.toArray hresponse
  have hoverrides : replayed.overrides.size = firstParent.size := by
    simpa [replayed, Uwueave.Exec.gatedReplay] using
      Uwueave.Exec.size_gatedReplay grants revocations firstParent operations
  have hstatuses : replayed.statuses.size = operations.size := by
    simpa [replayed] using
      Uwueave.Exec.size_statuses_gatedReplayFull grants revocations firstParent operations
  have hencodedIndex : firstParent.size + index <
      (replayed.overrides ++ replayed.statuses).size := by
    simp [hoverrides, hstatuses]
    exact hindex
  have hencoded := Uwueave.Exec.getWord_encodeView
    (replayed.overrides ++ replayed.statuses) hencodedIndex
  have hstatusIndex : index < replayed.statuses.size := by
    simpa [hstatuses] using hindex
  have hgetD : replayed.statuses.getD index 0 = replayed.statuses[index] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hstatusIndex]
    rfl
  have happend :
      (replayed.overrides ++ replayed.statuses)[firstParent.size + index] =
        replayed.statuses[index] := by
    rw [Array.getElem_append_right]
    · simp [hoverrides]
    · simp [hoverrides]
  have hselected :
      Uwueave.Exec.ofI (replayed.statuses.getD index 0) =
        expectedStatus c.admission := by
    calc
      Uwueave.Exec.ofI (replayed.statuses.getD index 0) =
          Uwueave.Exec.ofI replayed.statuses[index] := congrArg _ hgetD
      _ = Uwueave.Exec.ofI
          (replayed.overrides ++ replayed.statuses)[firstParent.size + index] :=
            congrArg _ happend.symm
      _ = Uwueave.Exec.getWord
          (Uwueave.Exec.encodeView (replayed.overrides ++ replayed.statuses))
            (firstParent.size + index) := hencoded.symm
      _ = Uwueave.Exec.getWord c.formatV3Response.toByteArray
          (firstParent.size + index) := by rw [hresponseBytes]
      _ = expectedStatus c.admission := hword
  rcases Uwueave.Exec.gated_status_mem_range grants revocations firstParent
      operations index with hzero | hone | htwo | hthree
  · exact Or.inl hzero
  · exact Or.inr hone
  · exfalso
    change replayed.statuses.getD index 0 = 2 at htwo
    rw [htwo] at hselected
    rcases expectedStatus_eq_zero_or_one c.admission with hstatus | hstatus
    · rw [hstatus] at hselected
      simp [Uwueave.Exec.ofI] at hselected
    · rw [hstatus] at hselected
      simp [Uwueave.Exec.ofI] at hselected
  · exfalso
    change replayed.statuses.getD index 0 = 3 at hthree
    rw [hthree] at hselected
    rcases expectedStatus_eq_zero_or_one c.admission with hstatus | hstatus
    · rw [hstatus] at hselected
      simp [Uwueave.Exec.ofI] at hselected
    · rw [hstatus] at hselected
      simp [Uwueave.Exec.ofI] at hselected

/-! ## Full retained trace and exact operational lanes -/

/-- The complete semantic result.  `checked` retains every certificate field
and dependent checker witness.  `refined` is the existing model-level result;
the two exact fields below make explicit how the operational predicates are
bound to the persisted signature and holder lanes. -/
structure RefinedAdmissionTrace
    (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop)
    (holder : GrantHolder)
    (boundary : HostVerificationBoundary)
    (checked : CheckedAdmissionTrace) where
  submittedCertificate : RuntimeAuthV4AdmissionTraceKernel.Bytes
  checkerAccepted : checkAdmissionTrace? submittedCertificate = some checked
  operational : OperationalReceipts boundary holder checked
  refined : RefinedHostAdmission scheme keys keyRevocations issued received
    holder
    (Uwueave.Exec.decodeGrants checked.certificate.formatV3Request.toByteArray)
    (Uwueave.Exec.decodeRevs checked.certificate.formatV3Request.toByteArray)
    (Uwueave.Exec.decodeOps checked.certificate.formatV3Request.toByteArray)
  certificateCitationNonzero : checked.certificate.cite ≠ 0
  hostVerificationExact : boundary.Accepts checked.certificate.signatureAlgorithm
    checked.certificate.signingBytes checked.certificate.signature
  holderReceiptExact : holder checked.certificate.nonceIssuer.toNat
    checked.certificate.cite.toNat

/-- Checker acceptance supplies every structural premise of
`hostAdmission_refines_authenticatedGatedOp`; only the exact operational
verification/holder receipts and U-0001 adapter remain explicit.  The entire
certificate/evidence pair is retained in the conclusion. -/
def checkedTrace_refines_authenticatedGatedOp
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {holder : GrantHolder}
    {boundary : HostVerificationBoundary}
    (crypto : CryptoAdapter scheme keys keyRevocations issued received boundary)
    (submittedCertificate : RuntimeAuthV4AdmissionTraceKernel.Bytes)
    (checked : CheckedAdmissionTrace)
    (hchecked : checkAdmissionTrace? submittedCertificate = some checked)
    (operational : OperationalReceipts boundary holder checked) :
    RefinedAdmissionTrace scheme keys keyRevocations issued received holder
      boundary checked := by
  let c := checked.certificate
  let evidence := checked.evidence
  let input := c.formatV3Request.toByteArray
  let firstParent := Uwueave.Exec.decodeBase input
  let operations := Uwueave.Exec.decodeOps input
  let grants := Uwueave.Exec.decodeGrants input
  let revocations := Uwueave.Exec.decodeRevs input
  let index := c.selectedRequestSlot.toNat
  obtain ⟨-, -, -, -, hindex, hexecution, -⟩ := evidence.execution_exact
  have hexecution' : operations[index] =
      RuntimeAuthV4.toExecOp evidence.request.toLegacy := by
    apply Option.some.inj
    calc
      some operations[index] = operations[index]? :=
        (Array.getElem?_eq_getElem hindex).symm
      _ = some (RuntimeAuthV4.toExecOp evidence.request.toLegacy) := hexecution
  have horigin : c.canonicalRequest = encodeContextRequest evidence.request :=
    accepted_decode_has_canonical_origin c.projectionBound.toNat
      c.canonicalRequest evidence.request evidence.requestDecoded
  have hstatus := modelStatus_zero_or_one evidence
  let refined := hostAdmission_refines_authenticatedGatedOp crypto
    c.projectionBound.toNat c.canonicalRequest evidence.request
    evidence.projection evidence.projectAdmission_eq horigin
    operational.hostVerified operational.holderAccepted grants revocations
    firstParent operations index hindex hexecution'
    hstatus
  have hlanes := evidence.projectionLanes
  simp only [projectionLanesMatch, decide_eq_true_eq] at hlanes
  rcases hlanes with
    ⟨hprojection, -, hsigning, halgorithm, hsignature, -, -, -, -, -,
      hissuer, -, -, -, -, -, -, -, -, -, -, hcite, -, -, -⟩
  have hostExact : boundary.Accepts c.signatureAlgorithm c.signingBytes
      c.signature := by
    rw [← halgorithm, ← hsigning, ← hsignature, hprojection]
    simpa [AdmissionProjection.ofRequest, HostVerified] using
      operational.hostVerified
  have holderExact : holder c.nonceIssuer.toNat c.cite.toNat := by
    rw [← congrArg UInt64.toNat hissuer, ← hcite, hprojection]
    simpa [AdmissionProjection.ofRequest] using operational.holderAccepted
  exact {
    submittedCertificate := submittedCertificate
    checkerAccepted := hchecked
    operational := operational
    refined := by simpa [c, input, grants, revocations, operations] using refined
    certificateCitationNonzero := evidence.nonzeroCitation
    hostVerificationExact := hostExact
    holderReceiptExact := holderExact
  }

/-- Executable-checker form of the composition.  The Boolean success yields
the dependent checked trace; the caller supplies operational receipts for the
exact witness selected by that success.  The dependent-pair conclusion retains
that entire witness and its `RefinedAdmissionTrace`. -/
def checkerAcceptance_refines_authenticatedGatedOp
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {holder : GrantHolder}
    {boundary : HostVerificationBoundary}
    (crypto : CryptoAdapter scheme keys keyRevocations issued received boundary)
    (submittedCertificate : RuntimeAuthV4AdmissionTraceKernel.Bytes)
    (haccepted : (checkAdmissionTrace? submittedCertificate).isSome = true)
    (operational : ∀ checked,
      checkAdmissionTrace? submittedCertificate = some checked →
        OperationalReceipts boundary holder checked) :
    Σ checked : CheckedAdmissionTrace,
      RefinedAdmissionTrace scheme keys keyRevocations issued received holder
        boundary checked := by
  cases hchecked : checkAdmissionTrace? submittedCertificate with
  | none => simp [hchecked] at haccepted
  | some checked =>
      exact ⟨checked, checkedTrace_refines_authenticatedGatedOp crypto
        submittedCertificate checked hchecked
          (operational checked hchecked)⟩

end Uwueave.RuntimeAuthV4AdmissionTraceRefinement
