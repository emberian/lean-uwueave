import Uwueave.Preo.ObservedBoundResult
import Uwueave.Preo.Quickstart

namespace PreoBench.Wave26.ObservedExact0

open Uwueave Uwueave.Preo Uwueave.Preo.Quickstart

def boundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state

def runningReach : List AppWorld := [startWorld]

end PreoBench.Wave26.ObservedExact0
