import RuntimeAuthV4Common

namespace Canary.Wave27.V4ResourceRefusal

open Uwueave.Preo.RuntimeAuthV4Projection
open Canary.Wave27.RuntimeAuthV4Common

def tinyConfig : ValidationConfig :=
  { config with bounds := { config.bounds with maxRoster := 0 } }

example : (validate tinyConfig projection).isOk = true := by
  decide

end Canary.Wave27.V4ResourceRefusal
