import Uwueave.Preo.Quickstart
import Uwueave.Preo.Export

namespace Canary.PreoQuickstart.WrongPlan

open Uwueave.Preo
open Uwueave.Preo.Quickstart

def rejected : Artifact.CheckedPlan artifactSession JourneyPlan.Plan :=
  Export.Examples.checkedPlan

end Canary.PreoQuickstart.WrongPlan
