import Uwueave.Preo.Elab

namespace PreoBench.Typed4

open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  typed derive D00 over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)
  typed derive D01 over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)
  typed derive D02 over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)
  typed derive D03 over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)

end PreoBench.Typed4
