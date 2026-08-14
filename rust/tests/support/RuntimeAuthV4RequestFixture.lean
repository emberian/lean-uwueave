/- Test-only stdout emitter for the canonical UWV4 signed-request fixture. -/
import Uwueave.RuntimeAuthV4

def main : IO Unit := do
  let stdout ← IO.getStdout
  stdout.write
    (Uwueave.RuntimeAuthV4.encodeRequestV4
      Uwueave.RuntimeAuthV4.fixtureRequest).toByteArray
  stdout.flush
