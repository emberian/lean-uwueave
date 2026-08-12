import Uwueave.Preo.ObservedBoundResult
import Uwueave.Preo.Quickstart

namespace PreoBench.Wave26.ObservedExact1

open Uwueave Uwueave.Preo Uwueave.Preo.Quickstart

def boundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state
def runningReach : List AppWorld := [startWorld]

def O00 : ObservedBoundResult.ObservedCertifiedReport boundary worldBinding
    runningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld boundary worldBinding runningReach
    startIndex rfl (by change startWorld ∈ [startWorld]; simp)
    (by change startWorld ∈ [startWorld]; simp) QueryCertificate

end PreoBench.Wave26.ObservedExact1
