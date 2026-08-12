/- Explicit binary-input CLI for bounded Lean-owned artifact inspection. -/
import Uwueave.Preo.ArtifactInspectionV1

open Lean
open Uwueave.Preo.ArtifactInspectionV1

private def usage : String :=
  "usage:\n" ++
  "  tools/uwueave-preo-inspect --frame PATH|- [--max-bytes N] [--max-records N] [--max-refs N]\n" ++
  "  tools/uwueave-preo-inspect --journal PATH|- [--max-bytes N] [--max-records N] [--max-refs N]"

private def parseNat (flag value : String) : IO Nat :=
  match value.toNat? with
  | some number => pure number
  | none => throw <| IO.userError s!"{flag} requires a natural number"

private def parseBounds : List String → IO Bounds
  | [] => pure {}
  | "--max-bytes" :: value :: rest => do
      let bounds ← parseBounds rest
      let limit ← parseNat "--max-bytes" value
      pure { bounds with maxInputBytes := limit }
  | "--max-records" :: value :: rest => do
      let bounds ← parseBounds rest
      let limit ← parseNat "--max-records" value
      pure { bounds with maxRecords := limit }
  | "--max-refs" :: value :: rest => do
      let bounds ← parseBounds rest
      let limit ← parseNat "--max-refs" value
      pure { bounds with maxRows := limit, maxRefsPerRow := limit }
  | _ => throw <| IO.userError usage

private def readInput (path : String) : IO ByteArray :=
  if path = "-" then do
    (← IO.getStdin).readBinToEnd
  else
    IO.FS.readBinFile path

private def describeError : Error → String
  | .inputLimit actual limit =>
      s!"input byte limit exceeded: found {actual}, limit {limit}"
  | .tornFrame start observed =>
      s!"torn artifact frame at byte {start} (observed through byte {observed})"
  | .refusedFrame start =>
      s!"canonical artifact validation refused frame at byte {start}"
  | .recordLimit limit =>
      s!"record limit exceeded: limit {limit}"
  | .expectedOneFrame actual =>
      s!"frame mode requires exactly one record, found {actual}"
  | .invalidV2 index =>
      s!"record {index} failed bounded ProjectionV2 structural validation"
  | .invalidV3 index =>
      s!"record {index} failed bounded ProjectionV3 structural validation"

private def run (args : List String) : IO Unit := do
  let (frameMode, path, boundArgs) ← match args with
    | "--frame" :: path :: rest => pure (true, path, rest)
    | "--journal" :: path :: rest => pure (false, path, rest)
    | _ => throw <| IO.userError usage
  let bounds ← parseBounds boundArgs
  let bytes ← readInput path
  let result := if frameMode then
      inspectFrame bounds bytes.data.toList
    else
      inspectJournal bounds bytes.data.toList
  match result with
  | .ok json => IO.println json.compress
  | .error error => throw <| IO.userError (describeError error)

def main (args : List String) : IO Unit := run args
