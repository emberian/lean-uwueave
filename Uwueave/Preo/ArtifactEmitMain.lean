/- Explicit CLI for `Uwueave.Preo.ArtifactEmit`; importing never writes. -/
import Uwueave.Preo.ArtifactEmit
import Uwueave.TrustFloor

open Uwueave.Preo.ArtifactEmit

private def usage : String :=
  "usage:\n" ++
  "  tools/uwueave-preo-artifact --list\n" ++
  "  tools/uwueave-preo-artifact NAME --stdout\n" ++
  "  tools/uwueave-preo-artifact NAME --output PATH"

private def selectedBytes (spelling : String) : IO ByteArray :=
  match parseName spelling with
  | some name => pure (byteArray name)
  | none => throw <| IO.userError s!"unknown artifact {spelling.quote}\n{usage}"

private def emitStdout (artifact : ByteArray) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.write artifact
  stdout.flush

private def run : List String → IO Unit
  | ["--list"] =>
      for name in names do
        IO.println name.canonical
  | [name, "--stdout"] => do
      emitStdout (← selectedBytes name)
  | [name, "--output", path] => do
      if path.isEmpty then
        throw <| IO.userError s!"output path must not be empty\n{usage}"
      IO.FS.writeBinFile path (← selectedBytes name)
  | _ => throw <| IO.userError usage

def main (args : List String) : IO Unit := run args

#assert_current_owns main

#audit_floor_current
