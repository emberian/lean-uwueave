/-
Negative compile canary for the supported rendering surface.

Expected result: this file does not compile. `SupportedSurface.Report` keeps
both its constructor and checked payload private, and the namespace exports no
raw `report` constructor. The lower-level `RenderSix.Carrier6.report` remains
available only when that semantic API is named explicitly.
-/
import Uwueave.Preo.ResultProgram

open Uwueave.Preo.ResultProgram

#check SupportedSurface.Report.ofChecked
#check SupportedSurface.Report.checked
#check SupportedSurface.report
