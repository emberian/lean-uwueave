import Uwueave.Preo.RuntimeAuthV4Examples

namespace PreoBench.Wave27.V4Checked1

open Uwueave.Preo.RuntimeAuthV4
open Uwueave.Preo.RuntimeAuthV4Examples

def mk (_ : Unit) := CheckedManifest.ofReady Uwueave.RuntimeAuthV4.fixtureRequest
  ready rfl grant context
def V00 := mk ()

end PreoBench.Wave27.V4Checked1
