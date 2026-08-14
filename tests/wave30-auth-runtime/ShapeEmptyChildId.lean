import Wave30AuthRuntimeCommon
open Uwueave.RuntimeAuthV4Kernel Canary.Wave30.AuthRuntimeCommon
example : (validateContextShape emptyChildId).isOk = true := by decide
