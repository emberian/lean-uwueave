import Wave30AuthRuntimeCommon
open Uwueave.RuntimeAuthV4Kernel Canary.Wave30.AuthRuntimeCommon
example : (validateContextShape emptyDestinationId).isOk = true := by decide
