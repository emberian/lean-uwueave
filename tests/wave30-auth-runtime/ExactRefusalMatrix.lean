import Wave30AuthRuntimeCommon

namespace Canary.Wave30.ExactRefusalMatrix

open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel
open Canary.Wave30.AuthRuntimeCommon

example : projectAdmission (exactBound - 1) canonicalBytes =
    .refused (.decode .tooLarge) := by decide
example : projectAdmission 1024 [] = .refused (.decode .badMagic) := by decide
example : projectAdmission oldVersionBytes.length oldVersionBytes =
    .refused (.decode .unsupportedVersion) := by decide
example : projectAdmission (encodeRequestV4 fixtureRequest).length
    (encodeRequestV4 fixtureRequest) = .refused (.decode .wrongKind) := by decide
example : projectAdmission malformedBytes.length malformedBytes =
    .refused (.decode .malformed) := by decide

example : project emptyDocument = .refused (.shape .emptyDocument) := by decide
example : project emptyGenesis = .refused (.shape .emptyGenesis) := by decide
example : project emptyContext = .refused (.shape .emptyContextCommitment) := by decide
example : project emptyNonce = .refused (.shape .emptyNonce) := by decide
example : project emptyOperationId = .refused (.shape .emptyOperationId) := by decide
example : project emptyChildId = .refused (.shape .emptyChildId) := by decide
example : project emptyDestinationId = .refused (.shape .emptyDestinationId) := by decide
example : project emptySignature = .refused (.shape .emptySignature) := by decide

set_option maxRecDepth 100000 in
example : validateHostWidths childTooLarge = .error .childIndexTooLarge := by rfl
set_option maxRecDepth 100000 in
example : validateHostWidths destinationTooLarge =
    .error .destinationIndexTooLarge := by rfl
set_option maxRecDepth 100000 in
example : validateHostWidths citeTooLarge = .error .citeTooLarge := by rfl

example : admissionRefusalTag (.decode .tooLarge) = 1 := rfl
example : admissionRefusalTag (.decode .badMagic) = 2 := rfl
example : admissionRefusalTag (.decode .unsupportedVersion) = 3 := rfl
example : admissionRefusalTag (.decode .wrongKind) = 4 := rfl
example : admissionRefusalTag (.decode .malformed) = 5 := rfl
example : admissionRefusalTag (.shape .emptyDocument) = 6 := rfl
example : admissionRefusalTag (.shape .emptyGenesis) = 7 := rfl
example : admissionRefusalTag (.shape .emptyContextCommitment) = 8 := rfl
example : admissionRefusalTag (.shape .emptyNonce) = 9 := rfl
example : admissionRefusalTag (.shape .emptyOperationId) = 10 := rfl
example : admissionRefusalTag (.shape .emptyChildId) = 11 := rfl
example : admissionRefusalTag (.shape .emptyDestinationId) = 12 := rfl
example : admissionRefusalTag (.shape .emptySignature) = 13 := rfl
example : admissionRefusalTag (.hostWidth .childIndexTooLarge) = 14 := rfl
example : admissionRefusalTag (.hostWidth .destinationIndexTooLarge) = 15 := rfl
example : admissionRefusalTag (.hostWidth .citeTooLarge) = 16 := rfl

end Canary.Wave30.ExactRefusalMatrix
