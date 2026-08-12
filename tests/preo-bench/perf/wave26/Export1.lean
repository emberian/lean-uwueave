import Uwueave.Preo.ArtifactV3Surface
import Uwueave.Preo.Quickstart

namespace PreoBench.Wave26.Export1

open Uwueave Uwueave.Preo Uwueave.Preo.Quickstart

def boundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state
def runningReach : List AppWorld := [startWorld]
def observed : ObservedBoundResult.ObservedCertifiedReport boundary worldBinding
    runningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld boundary worldBinding runningReach
    startIndex rfl (by change startWorld ∈ [startWorld]; simp)
    (by change startWorld ∈ [startWorld]; simp) QueryCertificate

preo_export_v3 E00 from Journey := {
  base := baseArtifact, futureDecl := QueryFuture, binding := worldBinding,
  index := startIndex, observed := observed, certificate := QueryCertificate,
  plan := artifactPlan, budget := artifactBudget, query := checkedQuery,
  future := artifactFuture, world := checkedWorld,
  resolutionId := fun _ => ⟨0⟩, surfaceId := StableId.surface,
  reasonId := fun _ => ⟨0⟩, certificateId := StableId.certificate,
  branch := exactStartBranch, maxWork := 64, config := validationConfig }

end PreoBench.Wave26.Export1
