import Uwueave.Preo.Elab

namespace PreoBench.Report

open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  invariant nonnegative : marker ≤ marker
  future Delivered on (Future.evidenceWorldModel Holes.Val) :=
    Future.Delivery Holes.Val
  typed derive Next over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)
  protocol P over Unit := Protocol.coalescingProtocol
  session S runs P at ()

#preo_report Subject

end PreoBench.Report
