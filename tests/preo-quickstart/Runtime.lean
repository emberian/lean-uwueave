/- Real-byte, reopen, journal, and Lean-inspection gate for the Quickstart. -/
import Uwueave.Preo.Quickstart

namespace Canary.PreoQuickstart.Runtime

open Lean
open Uwueave.Preo
open Uwueave.Preo.Quickstart

private def refuse (message : String) : IO α :=
  throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do refuse message

def run (directory : String) : IO Unit := do
  let framePath := directory ++ "/quickstart-v3.frame"
  let journalPath := directory ++ "/quickstart-v3.journal"
  let frame := v3BytesExecutable.toByteArray
  IO.FS.writeBinFile framePath frame
  let reopened ← IO.FS.readBinFile framePath
  require (reopened == frame) "reopened frame differs from emitted canonical bytes"
  let journal := (v3BytesExecutable ++ v3BytesExecutable).toByteArray
  IO.FS.writeBinFile journalPath journal
  let reopenedJournal ← IO.FS.readBinFile journalPath
  require (reopenedJournal == journal)
    "reopened journal differs from emitted canonical frames"
  let frameJson ← match ArtifactInspectionV1.inspectFrame {} reopened.data.toList with
    | .ok json => pure json
    | .error _ => refuse "Lean inspection refused the reopened frame"
  let journalJson ← match ArtifactInspectionV1.inspectJournal {}
      reopenedJournal.data.toList with
    | .ok json => pure json
    | .error _ => refuse "Lean inspection refused the reopened journal"
  IO.println s!"frameBytes={frame.size}"
  IO.println s!"journalBytes={journal.size}"
  IO.println s!"frame={frameJson.compress}"
  IO.println s!"journal={journalJson.compress}"

end Canary.PreoQuickstart.Runtime

def main (args : List String) : IO Unit :=
  match args with
  | [directory] => Canary.PreoQuickstart.Runtime.run directory
  | _ => throw <| IO.userError "usage: preo-quickstart-runtime DIRECTORY"
