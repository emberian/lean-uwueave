/-
Test-only batch emitter for the checkpoint-preflight scaling and recovery tests.

Rust chooses each move as one `lamport child dest cite` row (`dest` is `-` for a
move to root). Lean alone encodes the canonical kind-3 requests, each with a
nonce and operation id derived from its row number, and writes them to stdout
as `u64le length ‖ request` frames. Rust never encodes or edits a UWV4 request.
-/
import Uwueave.RuntimeAuthV4Kernel

namespace Uwueave.Tests.IncrementalPreflightCorpus

open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel

def littleEndian (value : Nat) : List UInt8 :=
  (List.range 8).map fun k => UInt8.ofNat (value >>> (8 * k))

def nodeRef (index : Nat) : NodeRef := ⟨[100, UInt8.ofNat index], index⟩

def parseDestination : String → Option (Option NodeRef)
  | "-" => some none
  | text => (fun index => some (nodeRef index)) <$> text.toNat?

def requestOfRow (row : Nat) (line : String) : Option ContextSignedRequest := do
  let [lamportText, childText, destinationText, citeText] := line.splitOn " "
    | none
  let lamport ← lamportText.toNat?
  let child ← childText.toNat?
  let destination ← parseDestination destinationText
  let cite ← citeText.toNat?
  let identity := littleEndian (row + 1)
  let move : MovePayload :=
    ⟨identity, UInt64.ofNat lamport, nodeRef child, destination, cite⟩
  pure ⟨⟨[1, 2], [3, 4], 1, 17, 2, identity, move, [30, 31]⟩, [0xAA]⟩

def main (args : List String) : IO Unit := do
  let [specPath] := args
    | throw <| IO.userError "usage: SPEC_FILE"
  let lines ← IO.FS.lines specPath
  let mut output := ByteArray.empty
  for h : row in [:lines.size] do
    let line := lines[row]'h.upper
    let some request := requestOfRow row line
      | throw <| IO.userError s!"malformed corpus row {row}: {line}"
    let bytes := encodeContextRequest request
    output := (littleEndian bytes.length).foldl ByteArray.push output
    output := bytes.foldl ByteArray.push output
  let stdout ← IO.getStdout
  stdout.write output
  stdout.flush

end Uwueave.Tests.IncrementalPreflightCorpus

def main (args : List String) : IO Unit :=
  Uwueave.Tests.IncrementalPreflightCorpus.main args
