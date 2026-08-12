import PreoV3AcceptanceCommon

namespace Canary.PreoV3Acceptance.PositiveObserved

open Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common

example : observedStartReport.world = startWorld := rfl
example : observedStartReport.state = start := rfl
example : observedStartReport.certificate = QueryCertificate := rfl
example : observedStartReport.report = certifiedStartReport := rfl

def forgedWorld : AppWorld := ⟨later, 0⟩

theorem forged_world_refused : ¬ observedStartReport.world = forgedWorld :=
  observedStartReport.refuses_forged_world forgedWorld (by
    change ¬ forgedWorld.state = start
    decide)

def staleWorld : AppWorld := { startWorld with generation := 1 }
def staleIndex : Future.WorldIndex appWorldModel := ⟨staleWorld⟩

theorem stale_index_refused :
    ¬ observedStartReport.certified.report.checked.state = staleIndex.world :=
  observedStartReport.refuses_stale_index staleIndex (by
    change staleWorld ≠ startWorld
    decide)

end Canary.PreoV3Acceptance.PositiveObserved
