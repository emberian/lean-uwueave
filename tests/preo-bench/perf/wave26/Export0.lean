import Uwueave.Preo.ArtifactV3Surface
import Uwueave.Preo.Quickstart

namespace PreoBench.Wave26.Export0

open Uwueave Uwueave.Preo Uwueave.Preo.Quickstart

def boundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state
def runningReach : List AppWorld := [startWorld]
def observed : ObservedBoundResult.ObservedCertifiedReport boundary worldBinding
    runningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld boundary worldBinding runningReach
    startIndex rfl (by change startWorld ∈ [startWorld]; simp)
    (by change startWorld ∈ [startWorld]; simp) QueryCertificate

end PreoBench.Wave26.Export0
