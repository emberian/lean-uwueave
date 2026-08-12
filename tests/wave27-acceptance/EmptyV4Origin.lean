import RuntimeAuthV4Common

namespace Canary.Wave27.EmptyV4Origin

open Uwueave.Preo.RuntimeAuthV4
open Uwueave.Preo.RuntimeAuthV4Projection
open Canary.Wave27.RuntimeAuthV4Common

def badManifest : Manifest :=
  { manifest with context := { manifest.context with originId := [] } }

example : (validate config (Projection.ofManifest badManifest)).isOk = true := by
  decide

end Canary.Wave27.EmptyV4Origin
