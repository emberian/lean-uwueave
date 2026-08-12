import Uwueave.Preo.Quickstart

namespace Canary.PreoQuickstart.WrongCertificate

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart

def wrongAnswer (_world : AppWorld) : Bool := true

def wrongCertificate :
    Future.CheckedCertificate QueryFuture wrongAnswer queryKey QueryAccepted
      startIndex where
  accepted := True.intro
  soundForAll := by
    intro _ _ _ _
    rfl

def rejected :=
  worldBinding.certifiedReportAtWorld startIndex wrongCertificate (by
    change startWorld ∈ [startWorld]
    simp)

end Canary.PreoQuickstart.WrongCertificate
