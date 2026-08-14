/- Lean-owned canonical corpus for the host outer-journal refinement test.

The executable emits only the exact concatenation of three small canonical
artifact frames.  Rust deliberately learns the frame boundaries through its
production parser and existing Lean validator; this fixture does not model a
filesystem, interrupted write, synchronization, or power loss. -/
import Uwueave.Preo.ArtifactJournalKernel

namespace Uwueave.Tests.ArtifactJournalRefinementCorpus

open Uwueave
open Uwueave.Preo.Artifact
open Uwueave.Preo.ArtifactDurable
open Uwueave.Preo.ArtifactJournalKernel

set_option autoImplicit false

def values : List ArtifactEncoding :=
  [Fixtures.first, Fixtures.second, Fixtures.third]

def bytes : Durable.Bytes := encodeJournal values

theorem bytes_recover_exactly :
    Durable.recover artifactFormat bytes =
      values.map artifactCodec.encode := by
  rw [bytes, encodeJournal_eq_durable, Durable.recover_encodeJournal]

def emit : IO Unit := do
  let stdout ← IO.getStdout
  stdout.write bytes.toByteArray
  stdout.flush

end Uwueave.Tests.ArtifactJournalRefinementCorpus

def main : IO Unit := Uwueave.Tests.ArtifactJournalRefinementCorpus.emit
