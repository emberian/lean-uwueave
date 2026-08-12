/- Nonempty, structurally valid V3 bytes for the inspection boundary test. -/
import Uwueave.Preo.ArtifactInspectionV1
import Uwueave.Preo.ProjectionV2Examples

namespace Uwueave.Tests.ArtifactInspectionV3Fixture

open Uwueave
open Uwueave.Preo.Artifact
open Uwueave.Preo.ArtifactV3

set_option autoImplicit false

def value : ArtifactV3Encoding where
  base := Uwueave.Preo.ProjectionV2.Examples.fullEncoding
  schema := ⟨1000⟩
  worlds := [⟨1001⟩]
  queries :=
    [{ id := ⟨1002⟩
       schema := ⟨1000⟩
       result := ⟨1003⟩
       program := ⟨1004⟩
       reads := [⟨402⟩]
       holes := [{ path := [0], field := ⟨402⟩, kind := .field }]
       analyses := [.mergeSafe] }]
  results :=
    [{ id := ⟨1003⟩
       query := ⟨1002⟩
       future := ⟨404⟩
       resolution := .preserveFork
       surface := ⟨1005⟩
       status := .exact
       effect := [.exact]
       visibility := .inspectable
       disclosure := some .shown }]
  certificates := [{ id := ⟨1006⟩, future := ⟨404⟩, world := ⟨1001⟩ }]

def config : Uwueave.Preo.ProjectionV3.ValidationConfig where
  bounds := {
    base := {
      maxFields := 8
      maxInvariants := 8
      maxFutures := 8
      maxSessions := 8
      maxPlans := 8
      maxBudgets := 8
      maxObligationsPerSession := 8
      maxActionsPerPlan := 8
      maxProfileEntriesPerPlan := 5
      maxProfileEntriesPerBudget := 5
      maxParticipantsPerDemand := 8
      maxWitnessWords := 8 }
    maxWorlds := 8
    maxQueries := 8
    maxResults := 8
    maxCertificates := 8
    maxReadsPerQuery := 8
    maxHolesPerQuery := 8
    maxAnalysesPerQuery := 2
    maxEffectShapesPerResult := 6 }

theorem value_validates :
    (Uwueave.Preo.ProjectionV3.validate config
      (Uwueave.Preo.ProjectionV3.Projection.ofEncoding value)).isOk = true := by
  decide

private def encodeDataFast (payload : List UInt8) : List UInt8 :=
  (payload.foldl
    (fun encoded byte => byte :: Durable.dataTag :: encoded) []).reverse

/-- Stack-safe executable framing for the test fixture.  The production V3
codec still owns the payload; no host language constructs these bytes. -/
def bytes : List UInt8 :=
  let tag := Uwueave.Preo.ArtifactV3Durable.artifactV3Format
  [Durable.magic₀, Durable.magic₁, tag.version, tag.domain] ++
    encodeDataFast
      (Uwueave.Preo.ArtifactV3Durable.artifactV3Codec.encode value) ++
    [Durable.endTag]

def emit : IO Unit := do
  let stdout ← IO.getStdout
  stdout.write bytes.toByteArray
  stdout.flush

end Uwueave.Tests.ArtifactInspectionV3Fixture

def main : IO Unit := Uwueave.Tests.ArtifactInspectionV3Fixture.emit
