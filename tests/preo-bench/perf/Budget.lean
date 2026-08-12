import Uwueave.Preo.Elab

namespace PreoBench.Budget

open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  protocol P over Unit := Protocol.coalescingProtocol
  session S runs P at ()

preo_budget Accepted for Subject.S : Scheduling.peerOnlyLimits :=
  Scheduling.coalescedProfileUpperBound

end PreoBench.Budget
