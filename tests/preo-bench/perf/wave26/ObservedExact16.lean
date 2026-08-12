import Uwueave.Preo.ObservedBoundResult
import Uwueave.Preo.Quickstart

namespace PreoBench.Wave26.ObservedExact16

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
bench_observed O04
bench_observed O05
bench_observed O06
bench_observed O07
bench_observed O08
bench_observed O09
bench_observed O10
bench_observed O11
bench_observed O12
bench_observed O13
bench_observed O14
bench_observed O15

end PreoBench.Wave26.ObservedExact16
