import PreoV3AcceptanceCommon

namespace Canary.PreoV3Acceptance.ForgedObservedState

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart
open Canary.PreoV3Acceptance.Common

def forged : AppState := later

def rejected : observationBoundary.Authentic startWorld forged := rfl

end Canary.PreoV3Acceptance.ForgedObservedState
