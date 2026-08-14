import Wave30AuthRuntimeCommon
open Uwueave.RuntimeAuthV4 Uwueave.RuntimeAuthV4Kernel Canary.Wave30.AuthRuntimeCommon
example : projectAdmission (encodeRequestV4 fixtureRequest).length
    (encodeRequestV4 fixtureRequest) = .accepted projection := by decide
