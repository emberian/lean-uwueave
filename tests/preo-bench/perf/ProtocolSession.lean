import Uwueave.Preo.Elab

namespace PreoBench.ProtocolSession

open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  protocol P over Unit := Protocol.coalescingProtocol
  session S runs P at ()

end PreoBench.ProtocolSession
