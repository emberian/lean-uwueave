import Wave30AuthRuntimeCommon
open Uwueave.RuntimeAuthV4Kernel Canary.Wave30.AuthRuntimeCommon
set_option maxRecDepth 100000 in
example : (validateHostWidths citeTooLarge).isOk = true := by decide
