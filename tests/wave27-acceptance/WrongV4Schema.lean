import RuntimeAuthV4Common

namespace Canary.Wave27.WrongV4Schema

open Uwueave.Preo.RuntimeAuthV4Projection
open Canary.Wave27.RuntimeAuthV4Common

def wrongProjection : Projection :=
  { projection with schema := "uwueave/preo-runtime-auth/not-v4" }

example : (validate config wrongProjection).isOk = true := by
  decide

end Canary.Wave27.WrongV4Schema
