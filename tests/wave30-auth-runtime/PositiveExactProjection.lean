import Wave30AuthRuntimeCommon
import Uwueave.TrustFloor

namespace Canary.Wave30.PositiveExactProjection

open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel
open Canary.Wave30.AuthRuntimeCommon

example : project request = .accepted projection := by decide

example : decodeAdmissionResponse (projectAdmissionBytes exactBound canonicalBytes) =
    some (.accepted projection) := by
  calc
    _ = some (projectAdmission exactBound canonicalBytes) :=
      decode_projectAdmissionBytes _ _
    _ = some (.accepted projection) := by decide

example : (encodeContextRequest request)[5]? = some contextMoveKind :=
  context_request_kind_at_index request

example : (encodeAdmissionResponse (.accepted projection))[5]? =
    some admissionResponseKind := admissionResponse_binds_kind _

example : encodeContextRequest request ≠ encodeRequestV4 fixtureRequest :=
  context_request_separated_from_legacy request fixtureRequest

example : encodeContextRequest request ≠
    encodeAdmissionResponse (.accepted projection) :=
  context_request_separated_from_admission_response request _

example : contextSigningBytes content ≠
    contextSigningBytes changedContext.content := by
  apply context_commitment_is_signed
  decide

example : (AdmissionProjection.ofRequest changedDocument).document = [31] := rfl
example : (AdmissionProjection.ofRequest changedGenesis).genesis = [32] := rfl
example : (AdmissionProjection.ofRequest changedContext).contextCommitment = [42] := rfl
example : (AdmissionProjection.ofRequest changedAlgorithm).signatureAlgorithm = 3 := rfl
example : (AdmissionProjection.ofRequest changedIssuer).issuer = 23 := rfl
example : (AdmissionProjection.ofRequest changedEpoch).keyEpoch = 5 := rfl
example : (AdmissionProjection.ofRequest changedNonce).nonce = [33] := rfl
example : (AdmissionProjection.ofRequest changedOperationId).operationId = [34] := rfl
example : (AdmissionProjection.ofRequest changedLamport).lamport = 19 := rfl
example : (AdmissionProjection.ofRequest changedChildStable).child.stable = [35] := rfl
example : (AdmissionProjection.ofRequest changedChildIndex).execChild = 13 := rfl
example : (AdmissionProjection.ofRequest changedDestinationStable).destination.map
    NodeRef.stable = some [36] := rfl
example : (AdmissionProjection.ofRequest changedDestinationIndex).execDestination =
    some 14 := rfl
example : (AdmissionProjection.ofRequest changedDestinationPresence).execDestination =
    none := rfl
example : (AdmissionProjection.ofRequest changedCite).execCite = 15 := rfl
example : (AdmissionProjection.ofRequest changedSignature).signature = [37] := rfl

#audit_floor_prefix Uwueave.RuntimeAuthV4Kernel
#audit_floor_prefix Canary.Wave30.AuthRuntimeCommon

end Canary.Wave30.PositiveExactProjection
