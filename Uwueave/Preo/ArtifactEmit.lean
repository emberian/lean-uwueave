/-
# Uwueave.Preo.ArtifactEmit -- explicit named durable-byte emission

This module is a deliberately opt-in boundary from checked Preoscript exports
to host bytes. Importing or elaborating it performs no I/O. `bytes` selects a
named, already-defined artifact value and returns the exact output of Lean's
`ArtifactDurable.projectionBytes`; the companion `ArtifactEmitMain.lean`
writes those bytes only when a user explicitly invokes the command.

This is not a filesystem theorem. The command inherits Lean's ordinary
`stdout`/`writeBinFile` behavior and makes no atomicity, fsync, permission, or
path-hardening claim.
-/
import Uwueave.Preo.Demo
import Uwueave.Preo.ProjectionV2Examples
import Uwueave.Preo.ArtifactJournalKernel

namespace Uwueave.Preo.ArtifactEmit

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

/-- Stable command-level names for currently available durable artifacts. -/
inductive Name where
  | semanticExport
  | fullExport
  deriving BEq, DecidableEq, Repr

/-- Canonical spelling printed by `--list` and accepted by `parseName`. -/
def Name.canonical : Name → String
  | .semanticExport => "SemanticExport.ArtifactDurableBytes"
  | .fullExport => "ProjectionV2.Examples.fullExport"

/-- Short aliases are conveniences; canonical names identify Lean values. -/
def parseName : String → Option Name
  | "SemanticExport.ArtifactDurableBytes" => some .semanticExport
  | "semantic-export" => some .semanticExport
  | "ProjectionV2.Examples.fullExport" => some .fullExport
  | "full-export" => some .fullExport
  | _ => none

/-- The complete finite registry, in stable display order. -/
def names : List Name := [.semanticExport, .fullExport]

/-- Executable reification of the demand shared by both generated sessions.
The equality theorem below prevents this first-order reification from becoming
an unchecked semantic copy. -/
private def semanticDemand : DemandArtifact where
  currency := .peerBarrier
  participants := [0, 1]
  scope := 7
  epoch := 3
  evidence := .named 11
  round := 0
  barrier := 5

private def semanticObligations : List ObligationArtifact :=
  [{ origin := .crossing 0, demand := semanticDemand },
   { origin := .crossing 1, demand := semanticDemand }]

private def semanticProfile : List (Currency × Nat) :=
  [(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
   (.userPrompt, 0), (.rollback, 0)]

/-- A computable first-order reification of the generated export. The next
theorem is deliberately whole-value and definitional: drift anywhere in a row,
reference, demand, plan, or budget makes this module fail to elaborate. -/
def semanticEncoding : ArtifactEncoding where
  declaration := ⟨700, 701, 1⟩
  fields := [⟨702, 700, 10, 701, none⟩]
  invariants := [⟨703, 700, 701, .free⟩]
  futures := [⟨704, 700, 705, 706⟩]
  sessions :=
    [⟨707, 700, 2, semanticObligations⟩,
     ⟨709, 700, 2, semanticObligations⟩]
  plans :=
    [⟨708, 707, [semanticDemand, semanticDemand], semanticProfile⟩,
     ⟨710, 709, [semanticDemand, semanticDemand], semanticProfile⟩]
  budgets := [⟨711, 707, 708, semanticProfile, semanticProfile⟩]

theorem semanticEncoding_eq_generated :
    semanticEncoding = Demo.SemanticExport.Encoding := by
  rfl

/-- The exact first-order encoding selected by each stable command name.
Keeping this selector public lets the emitted byte theorem state which value
the host buffer represents without asking Rust to reconstruct artifact data. -/
noncomputable def encoding : Name → ArtifactEncoding
  | .semanticExport => Demo.SemanticExport.Encoding
  | .fullExport => ProjectionV2.Examples.fullExport.encoding

/-- The compiler implementation. It remains Lean's canonical codec applied to
whole-value checked encodings, through ArtifactDurable's proved-equal
stack-safe framing path; Rust neither constructs nor interprets payload fields. -/
def bytesImpl : Name → ArtifactDurable.Bytes
  | .semanticExport =>
      ArtifactDurable.stackSafeEncodeValue ArtifactDurable.artifactCodec
        ArtifactDurable.artifactFormat semanticEncoding
  | .fullExport =>
      ArtifactDurable.stackSafeEncodeValue ArtifactDurable.artifactCodec
        ArtifactDurable.artifactFormat ProjectionV2.Examples.fullExport.encoding

/-- Select exact Lean-owned durable bytes. The logical semantic-export branch
names the actual generated `ArtifactDurableBytes`; `implemented_by` supplies
the definitionally equal computable reification above to native execution. -/
@[implemented_by bytesImpl]
noncomputable def bytes (name : Name) : ArtifactDurable.Bytes :=
  ArtifactDurable.projectionBytes (encoding name)

theorem bytesImpl_eq_bytes (name : Name) : bytesImpl name = bytes name := by
  cases name with
  | semanticExport =>
      simp only [bytesImpl, bytes, encoding,
        ArtifactDurable.stackSafeEncodeValue_eq,
        ArtifactDurable.projectionBytes]
      rw [semanticEncoding_eq_generated]
  | fullExport =>
      exact ArtifactDurable.stackSafeEncodeValue_eq _ _ _

theorem bytes_semanticExport :
    bytes .semanticExport = Demo.SemanticExport.ArtifactDurableBytes := by
  rfl

theorem bytes_fullExport :
    bytes .fullExport =
      ArtifactDurable.projectionBytes ProjectionV2.Examples.fullExport.encoding := rfl

/-- Every named output is the canonical durable projection of the exact
first-order encoding selected by that name. -/
theorem bytes_eq_projectionBytes (name : Name) :
    bytes name = ArtifactDurable.projectionBytes (encoding name) := rfl

/-- The same Lean validator used by Rust accepts every named emitted frame and
recovers its exact first-order encoding.  This is a byte-codec theorem only;
it says nothing about filesystem writes, synchronization, or power loss. -/
theorem validateOne_bytes (name : Name) :
    ArtifactJournalKernel.validateOne (bytes name) = some (encoding name) := by
  rw [bytes_eq_projectionBytes]
  exact ArtifactJournalKernel.validateOne_projectionBytes (encoding name)

/-- A fresh runtime byte array containing exactly `bytes name`. -/
def byteArray (name : Name) : ByteArray := (bytes name).toByteArray

theorem byteArray_data_toList (name : Name) :
    (byteArray name).data.toList = bytes name := by
  simp [byteArray]

end Uwueave.Preo.ArtifactEmit
