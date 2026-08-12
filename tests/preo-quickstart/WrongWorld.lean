import Uwueave.Preo.Quickstart

namespace Canary.PreoQuickstart.WrongWorld

open Uwueave.Preo
open Uwueave.Preo.Quickstart

def otherWorld : AppWorld := { startWorld with generation := 1 }
def otherIndex : Future.WorldIndex appWorldModel := ⟨otherWorld⟩

theorem rejected :
    certifiedStartReport.report.checked.state = otherIndex.world := rfl

end Canary.PreoQuickstart.WrongWorld
