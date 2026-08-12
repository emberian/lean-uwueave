import Uwueave.Preo.Elab

namespace PreoBench.Typed16

open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  typed derive D00 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D01 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D02 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D03 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D04 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D05 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D06 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D07 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D08 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D09 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D10 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D11 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D12 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D13 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D14 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)
  typed derive D15 over { schema := [.nat, .nat], reach := [Incremental.before] } :=
    .natSucc (.field 0)

end PreoBench.Typed16
