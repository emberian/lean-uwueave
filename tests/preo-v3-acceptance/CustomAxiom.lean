import PreoV3AcceptanceCommon
import Uwueave.Preo.ArtifactV3Surface

namespace Canary.PreoV3Acceptance.CustomAxiom

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common

axiom unsound : False

def poisonedReason (_ : String) : ArtifactV3.ReasonId :=
  False.elim unsound

preo_export_v3 Rejected from Journey := {
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
  reasonId := poisonedReason,
  certificateId := StableId.certificate,
  branch := exactStartBranch,
  maxWork := 64,
  config := validationConfig
}

end Canary.PreoV3Acceptance.CustomAxiom
