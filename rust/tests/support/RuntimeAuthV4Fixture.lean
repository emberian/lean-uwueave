/- Test-only stdout emitter for the frozen, checked runtime-auth V4 sidecar. -/
import Uwueave.Preo.RuntimeAuthV4Fixtures

namespace Uwueave.Tests.RuntimeAuthV4Fixture

def emit : IO Unit := do
  let stdout <- IO.getStdout
  stdout.write Uwueave.Preo.RuntimeAuthV4Examples.fixtureBytes.toByteArray
  stdout.flush

end Uwueave.Tests.RuntimeAuthV4Fixture

def main : IO Unit := Uwueave.Tests.RuntimeAuthV4Fixture.emit
