import PreoV3AcceptanceCommon
import Uwueave.Preo.ArtifactV3Surface

namespace Canary.PreoV3Acceptance.WrongProjection

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common

def wrongProject (state : AppState) : Expr.Env AppSchema :=
  .cons (state.count + 1) (.cons state.enabled .nil)

def wrongJourney : StateProgram AppState AppSchema :=
  { Journey with project := wrongProject }

def wrongQuery : ArtifactV3.CheckedQuery baseArtifact wrongJourney :=
  ArtifactV3.CheckedQuery.ofStateProgram baseArtifact wrongJourney StableId.query
    StableId.schema StableId.resultId StableId.program queryFieldId (by
      intro position read
      change position ∈ [0] at read
      simp at read
      subst position
      rfl)

preo_export_v3 Rejected from Journey := {
  base := baseArtifact,
  futureDecl := QueryFuture,
  binding := worldBinding,
  index := startIndex,
  observed := observedStartReport,
  certificate := QueryCertificate,
  plan := artifactPlan,
  budget := artifactBudget,
  query := wrongQuery,
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

end Canary.PreoV3Acceptance.WrongProjection
