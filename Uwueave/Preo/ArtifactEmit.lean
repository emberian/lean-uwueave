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

/-- Tail-recursive implementation of `Durable.encodeData`. The logical format
is unchanged; this avoids the Lean interpreter retaining one frame per payload
byte when this explicit command is run without compiling a separate binary. -/
private def encodeDataFast (payload : Durable.Bytes) : Durable.Bytes :=
  (payload.foldl
    (fun encoded byte => byte :: Durable.dataTag :: encoded) []).reverse

private theorem encodeDataFast_go (payload accumulator : Durable.Bytes) :
    (payload.foldl
      (fun encoded byte => byte :: Durable.dataTag :: encoded)
      accumulator).reverse =
    accumulator.reverse ++ Durable.encodeData payload := by
  induction payload generalizing accumulator with
  | nil => simp [Durable.encodeData]
  | cons byte payload ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Durable.encodeData, List.append_assoc]

private theorem encodeDataFast_eq (payload : Durable.Bytes) :
    encodeDataFast payload = Durable.encodeData payload := by
  simpa [encodeDataFast] using encodeDataFast_go payload []

/-- Stack-safe execution path, proved byte-for-byte equal to Lean's canonical
artifact framing rather than introducing a second format implementation. -/
private def projectionBytesFast (value : ArtifactEncoding) :
    ArtifactDurable.Bytes :=
  let tag := ArtifactDurable.artifactFormat
  [Durable.magic₀, Durable.magic₁, tag.version, tag.domain] ++
    encodeDataFast (ArtifactDurable.artifactCodec.encode value) ++
    [Durable.endTag]

private theorem projectionBytesFast_eq (value : ArtifactEncoding) :
    projectionBytesFast value = ArtifactDurable.projectionBytes value := by
  simp [projectionBytesFast, ArtifactDurable.projectionBytes,
    Durable.encodeValue, Durable.encodeFrame, Durable.encodeEnvelope,
    Durable.encodePayload, encodeDataFast_eq]

/-- The compiler implementation. It remains Lean's canonical codec applied to
whole-value checked encodings, through the equal stack-safe framing path above;
Rust neither constructs nor interprets payload fields. -/
def bytesImpl : Name → ArtifactDurable.Bytes
  | .semanticExport => projectionBytesFast semanticEncoding
  | .fullExport =>
      projectionBytesFast ProjectionV2.Examples.fullExport.encoding

/-- Select exact Lean-owned durable bytes. The logical semantic-export branch
names the actual generated `ArtifactDurableBytes`; `implemented_by` supplies
the definitionally equal computable reification above to native execution. -/
@[implemented_by bytesImpl]
noncomputable def bytes : Name → ArtifactDurable.Bytes
  | .semanticExport => Demo.SemanticExport.ArtifactDurableBytes
  | .fullExport =>
      ArtifactDurable.projectionBytes ProjectionV2.Examples.fullExport.encoding

theorem bytesImpl_eq_bytes (name : Name) : bytesImpl name = bytes name := by
  cases name with
  | semanticExport =>
      simp only [bytesImpl, bytes, Demo.SemanticExport.ArtifactDurableBytes,
        projectionBytesFast_eq]
      rw [semanticEncoding_eq_generated]
  | fullExport => exact projectionBytesFast_eq _

theorem bytes_semanticExport :
    bytes .semanticExport = Demo.SemanticExport.ArtifactDurableBytes := rfl

theorem bytes_fullExport :
    bytes .fullExport =
      ArtifactDurable.projectionBytes ProjectionV2.Examples.fullExport.encoding := rfl

/-- A fresh runtime byte array containing exactly `bytes name`. -/
def byteArray (name : Name) : ByteArray := (bytes name).toByteArray

theorem byteArray_data_toList (name : Name) :
    (byteArray name).data.toList = bytes name := by
  simp [byteArray]

end Uwueave.Preo.ArtifactEmit
