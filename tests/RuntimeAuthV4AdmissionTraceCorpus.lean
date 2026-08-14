/-
Executable corpus for the shipping authenticated-admission trace boundary.

Rust asks this program for canonical kind-3 request/signing bytes and, once a
fresh runtime certificate exists, for Lean-owned semantic mutations of that
certificate.  The test never carries a second Rust encoder for either wire.
-/
import Uwueave.RuntimeAuthV4Kernel

namespace Uwueave.Tests.RuntimeAuthV4AdmissionTraceCorpus

open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel

def baseContent : ContextSignedContent :=
  ⟨[1, 2], [3, 4], 1, 17, 2, [5, 6], fixtureMove, [30, 31]⟩

def contentFor : String → Option ContextSignedContent
  | "base" => some baseContent
  | "cite0" => some {
      baseContent with move := { fixtureMove with cite := 0 } }
  | "duplicate_move" => some {
      baseContent with
      nonce := [5, 7]
      move := { fixtureMove with operationId := [22] } }
  | _ => none

def requireContent (name : String) : IO ContextSignedContent := do
  match contentFor name with
  | some content => pure content
  | none => throw <| IO.userError s!"unknown trace corpus case: {name}"

def emit (bytes : List UInt8) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.write bytes.toByteArray
  stdout.flush

def main (args : List String) : IO Unit := do
  match args with
  | ["signing", name] =>
      emit (contextSigningBytes (← requireContent name))
  | ["request", name, signaturePath] =>
      let content ← requireContent name
      let signature ← IO.FS.readBinFile signaturePath
      emit (encodeContextRequest ⟨content, signature.data.toList⟩)
  | _ =>
      throw <| IO.userError
        "usage: signing CASE | request CASE SIGNATURE_FILE"

end Uwueave.Tests.RuntimeAuthV4AdmissionTraceCorpus

def main (args : List String) : IO Unit :=
  Uwueave.Tests.RuntimeAuthV4AdmissionTraceCorpus.main args
