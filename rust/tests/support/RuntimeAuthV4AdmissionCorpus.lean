/-
Test-only canonical request corpus for the context-bound UWV4 admission path.

The program deliberately supports a two-pass test flow:

* `signing CASE` emits Lean's exact kind-3 signing bytes;
* `request CASE SIGNATURE_FILE` embeds those raw signature bytes and emits
  Lean's exact kind-3 request bytes;
* `legacy` emits the old kind-1 syntax fixture, which admission must refuse.

Rust may choose a case and supply verifier-produced signature bytes, but it
never encodes or edits a UWV4 request.
-/
import Uwueave.RuntimeAuthV4Kernel

namespace Uwueave.Tests.RuntimeAuthV4AdmissionCorpus

open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel

def baseContent : ContextSignedContent :=
  ⟨[1, 2], [3, 4], 1, 17, 2, [5, 6], fixtureMove, [30, 31]⟩

def contentFor : String → Option ContextSignedContent
  | "base" => some baseContent
  | "other_algorithm" => some { baseContent with signatureAlgorithm := 2 }
  | "other_document" => some { baseContent with document := [8, 8] }
  | "other_genesis" => some { baseContent with genesis := [9, 9] }
  | "other_issuer" => some { baseContent with issuer := 18 }
  | "other_epoch" => some { baseContent with keyEpoch := 3 }
  | "other_context" => some { baseContent with contextCommitment := [32, 33] }
  | "other_nonce" => some { baseContent with nonce := [5, 7] }
  | "nonce_collision" =>
      some { baseContent with move := { fixtureMove with cite := 8 } }
  | "operation_id_collision" =>
      some { baseContent with nonce := [5, 7] }
  | "other_operation_id" =>
      some { baseContent with
        nonce := [5, 7]
        move := { fixtureMove with operationId := [22] } }
  | "child_index_mismatch" =>
      some { baseContent with
        move := { fixtureMove with child := ⟨fixtureNodeA.stable, 4⟩ } }
  | "destination_index_mismatch" =>
      some { baseContent with
        move := { fixtureMove with dest := some ⟨fixtureNodeB.stable, 5⟩ } }
  | "child_identity_substitution" =>
      some { baseContent with
        move := { fixtureMove with child := ⟨[10, 12], fixtureNodeA.kernelIndex⟩ } }
  | "no_destination" =>
      some { baseContent with move := { fixtureMove with dest := none } }
  | "empty_document" => some { baseContent with document := [] }
  | "empty_genesis" => some { baseContent with genesis := [] }
  | "empty_context" => some { baseContent with contextCommitment := [] }
  | "empty_nonce" => some { baseContent with nonce := [] }
  | "empty_operation_id" =>
      some { baseContent with
        move := { fixtureMove with operationId := [] } }
  | "empty_child_id" =>
      some { baseContent with
        move := { fixtureMove with child := ⟨[], fixtureNodeA.kernelIndex⟩ } }
  | "empty_destination_id" =>
      some { baseContent with
        move := { fixtureMove with dest := some ⟨[], fixtureNodeB.kernelIndex⟩ } }
  | _ => none

def requireContent (name : String) : IO ContextSignedContent := do
  match contentFor name with
  | some content => pure content
  | none => throw <| IO.userError s!"unknown admission corpus case: {name}"

def emit (bytes : List UInt8) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.write bytes.toByteArray
  stdout.flush

def main (args : List String) : IO Unit := do
  match args with
  | ["signing", name] =>
      let content ← requireContent name
      emit (contextSigningBytes content)
  | ["request", name, signaturePath] =>
      let content ← requireContent name
      let signature ← IO.FS.readBinFile signaturePath
      emit (encodeContextRequest ⟨content, signature.data.toList⟩)
  | ["empty_signature", name] =>
      let content ← requireContent name
      emit (encodeContextRequest ⟨content, []⟩)
  | ["legacy"] => emit (encodeRequestV4 fixtureRequest)
  | _ =>
      throw <| IO.userError
        "usage: signing CASE | request CASE SIGNATURE_FILE | empty_signature CASE | legacy"

end Uwueave.Tests.RuntimeAuthV4AdmissionCorpus

def main (args : List String) : IO Unit :=
  Uwueave.Tests.RuntimeAuthV4AdmissionCorpus.main args
