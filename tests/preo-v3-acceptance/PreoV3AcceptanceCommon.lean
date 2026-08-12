/-
# PreoV3AcceptanceCommon — one exact observed Quickstart journey

This test-only module supplies the positive observation premises consumed by
the Wave-26 export surface.  The observation relation is deliberately explicit
and local: equality between a world's projected state and the checked state.
-/
import Uwueave.Preo.ObservedBoundResult
import Uwueave.Preo.Quickstart

namespace Canary.PreoV3Acceptance.Common

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart

def observationBoundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state

def runningReach : List AppWorld := [startWorld]

def observedStartReport :
  ObservedBoundResult.ObservedCertifiedReport observationBoundary worldBinding
      runningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld observationBoundary worldBinding runningReach
    startIndex rfl (by change startWorld ∈ [startWorld]; simp)
    (by change startWorld ∈ [startWorld]; simp) QueryCertificate

theorem observed_start_exact :
    observedStartReport.world = startWorld
      ∧ observedStartReport.state = start
      ∧ observedStartReport.world ∈ runningReach
      ∧ observedStartReport.world ∈ worldBinding.worldReach := by
  exact ⟨rfl, rfl, observedStartReport.reach.inRunning,
    observedStartReport.reach.inAuthored⟩

theorem observed_certificate_exact :
    observedStartReport.certificate = QueryCertificate := rfl

end Canary.PreoV3Acceptance.Common
