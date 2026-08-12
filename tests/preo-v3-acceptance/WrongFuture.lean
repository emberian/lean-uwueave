import PreoV3AcceptanceCommon
import Uwueave.Preo.ArtifactV3Surface

namespace Canary.PreoV3Acceptance.WrongFuture

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common

def OtherFuture : Future.FutureDecl appWorldModel where
  name := "quickstart/other-future"
  scope := .extension
  future := fun _ _ => True

preo_export_v3 Rejected from Journey := {
  base := baseArtifact,
  futureDecl := OtherFuture,
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

end Canary.PreoV3Acceptance.WrongFuture
