import PreoV3AcceptanceSupport
import PreoV3AcceptanceCommon
import Uwueave.Preo.ArtifactV3Surface

namespace Canary.PreoV3Acceptance.RollbackReuse

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common
open PreoV3AcceptanceSupport

/--
error: preo_export_v3: the automatic V3 route exceeded `maxWork`
-/
#guard_msgs (error, substring := true) in
preo_export_v3 Reused from Journey := {
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
  maxWork := 0,
  config := validationConfig
}

#assert_no_decl Reused.StateProgram
#assert_no_decl Reused.ObservedReport
#assert_no_decl Reused.Encoding
#assert_no_decl Reused.Validated
#assert_no_decl Reused.Bytes

preo_export_v3 Reused from Journey := {
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

#assert_decl Reused.StateProgram
#assert_decl Reused.ObservedReport
#assert_decl Reused.Encoding
#assert_decl Reused.Validated
#assert_decl Reused.Bytes

end Canary.PreoV3Acceptance.RollbackReuse
