import Uwueave.Preo.Elab

namespace PreoBench.Typed1

open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  typed derive D00 over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)

end PreoBench.Typed1
