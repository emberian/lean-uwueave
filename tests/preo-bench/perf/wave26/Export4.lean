import Uwueave.Preo.ArtifactV3Surface
import Uwueave.Preo.Quickstart

namespace PreoBench.Wave26.Export4

open Uwueave Uwueave.Preo Uwueave.Preo.Quickstart

def boundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state
def runningReach : List AppWorld := [startWorld]
def observed : ObservedBoundResult.ObservedCertifiedReport boundary worldBinding
    runningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld boundary worldBinding runningReach
    startIndex rfl (by change startWorld ∈ [startWorld]; simp)
    (by change startWorld ∈ [startWorld]; simp) QueryCertificate

macro "bench_export " name:ident : command => do
  let journey := Lean.mkIdent `Uwueave.Preo.Quickstart.Journey
  `(preo_export_v3 $name from $journey := {
    base := baseArtifact, futureDecl := QueryFuture, binding := worldBinding,
    index := startIndex, observed := observed, certificate := QueryCertificate,
    plan := artifactPlan, budget := artifactBudget, query := checkedQuery,
    future := artifactFuture, world := checkedWorld,
    resolutionId := fun _ => ⟨0⟩, surfaceId := StableId.surface,
    reasonId := fun _ => ⟨0⟩, certificateId := StableId.certificate,
    branch := exactStartBranch, maxWork := 64, config := validationConfig })

bench_export E00
bench_export E01
bench_export E02
bench_export E03

end PreoBench.Wave26.Export4
