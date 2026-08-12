import PreoV3AcceptanceCommon

namespace Canary.PreoV3Acceptance.OutOfRunningReach

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common

def emptyRunningReach : List AppWorld := []

def rejected :
    ObservedBoundResult.ObservedCertifiedReport observationBoundary worldBinding
      emptyRunningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld observationBoundary worldBinding
    emptyRunningReach startIndex rfl (by simp [emptyRunningReach])
    (by change startWorld ∈ [startWorld]; simp) QueryCertificate

end Canary.PreoV3Acceptance.OutOfRunningReach
