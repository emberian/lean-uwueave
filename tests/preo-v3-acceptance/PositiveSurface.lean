import PreoV3AcceptanceSupport
import PreoV3AcceptanceCommon
import Uwueave.Preo.ArtifactV3Surface

namespace Canary.PreoV3Acceptance.PositiveSurface

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common
open PreoV3AcceptanceSupport

preo_export_v3 Export from Journey := {
  base := baseArtifact,
  futureDecl := QueryFuture,
  binding := worldBinding,
  index := startIndex,
  observed := observedStartReport,
  certificate := QueryCertificate,
  plan := artifactPlan,
  budget := artifactBudget,
  query := checkedQuery,
  future := artifactFuture,
  world := checkedWorld,
  resolutionId := fun _ => ⟨0⟩,
  surfaceId := StableId.surface,
  reasonId := fun _ => ⟨0⟩,
  certificateId := StableId.certificate,
  branch := exactStartBranch,
  maxWork := 64,
  config := validationConfig
}

#assert_decl Export.StateProgram
#assert_decl Export.Binding
#assert_decl Export.ObservedReport
#assert_decl Export.Plan
#assert_decl Export.Budget
#assert_decl Export.Query
#assert_decl Export.World
#assert_decl Export.Result
#assert_decl Export.Certificate
#assert_decl Export.Encoding
#assert_decl Export.Validated
#assert_decl Export.Bytes

example : Export.StateProgram = Journey := rfl
example : Export.ObservedReport = observedStartReport := rfl
example : Export.Encoding = v3Artifact := rfl
example : Export.Bytes = v3Bytes := rfl
example : Export.Validation.isOk = true := Export.validation_ok

#audit_floor_prefix Canary.PreoV3Acceptance.PositiveSurface.Export

end Canary.PreoV3Acceptance.PositiveSurface
