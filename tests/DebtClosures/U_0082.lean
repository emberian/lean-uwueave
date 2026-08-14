import Uwueave.Preo.ResultProgram

open Uwueave
open Uwueave.Preo.ResultProgram
open Uwueave.ResultStatus (Status)

#check @SupportedSurface.renderReport
#check @SupportedSurface.Report.eliminate
#check @RenderSix.Carrier6.report

theorem debtClosure_U_0082 :
    openSurfaceReport.eliminate
        (fun _ => 1) (fun _ => 2) 3 4 5 6 = 2 ∧
      (¬ openSurfaceReport.Says (Status.exact 47)) ∧
      Nonempty (RenderSix.Carrier6
        (Evidence.SealedFuture (α := Holes.Val)) Holes.Val) := by
  refine ⟨?_, open_surface_report_refuses_exact, ⟨evidenceCarrier⟩⟩
  rw [openSurfaceReport.eliminate_spec]
  change RenderSix.dispatch6 (fun _ => 1) (fun _ => 2) 3 4 5 6
    (ResultStatus.statusOf Evidence.openW) = 2
  rw [ResultStatus.statusOf_openW]
  rfl
