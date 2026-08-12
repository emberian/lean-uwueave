import Uwueave.Preo.ObservedBoundResult
import Uwueave.Preo.Quickstart

namespace PreoBench.Wave26.ObservedExact4

open Uwueave Uwueave.Preo Uwueave.Preo.Quickstart

def boundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state
def runningReach : List AppWorld := [startWorld]

macro "bench_observed " name:ident : command =>
  `(def $name : ObservedBoundResult.ObservedCertifiedReport boundary worldBinding
      runningReach queryKey QueryAccepted startIndex :=
    ObservedBoundResult.attachAtWorld boundary worldBinding runningReach
      startIndex rfl (by change startWorld ∈ [startWorld]; simp)
      (by change startWorld ∈ [startWorld]; simp) QueryCertificate)

bench_observed O00
bench_observed O01
bench_observed O02
bench_observed O03

end PreoBench.Wave26.ObservedExact4
