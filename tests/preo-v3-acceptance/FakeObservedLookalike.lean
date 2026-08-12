import PreoV3AcceptanceCommon
import Uwueave.Preo.ArtifactV3Surface

namespace Canary.PreoV3Acceptance.FakeObservedLookalike

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart

/-- This has every field the surface projects, but no retained authenticity or
running-reach proof. Structural resemblance must not cross the boundary. -/
structure Lookalike where
  binding : BoundResult.WorldBinding QueryFuture Journey.Result
  index : Future.WorldIndex appWorldModel
  report : worldBinding.CertifiedReport queryKey QueryAccepted startIndex
  certificate : Future.CheckedCertificate QueryFuture
    worldBinding.declaration.answer queryKey QueryAccepted startIndex

def fake : Lookalike where
  binding := worldBinding
  index := startIndex
  report := certifiedStartReport
  certificate := QueryCertificate

preo_export_v3 Rejected from Journey := {
  base := baseArtifact,
  futureDecl := QueryFuture,
  binding := worldBinding,
  index := startIndex,
  observed := fake,
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

end Canary.PreoV3Acceptance.FakeObservedLookalike
