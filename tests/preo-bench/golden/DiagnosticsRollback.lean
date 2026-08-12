import Uwueave.Preo.Elab
import Uwueave.Preo.ProtocolSurface

namespace PreoBench.Golden.DiagnosticsRollback

open Uwueave Uwueave.Preo Uwueave.Preo.ProtocolSurface

/--
error: preo: `typed derive Broken` was refused by `Preo.Expr.Raw.infer`. The expression is malformed, reads a field outside its schema, applies an operator at the wrong type, or uses raw `.custom`, which has no implementation/locality proof. No typed term or positive analysis was emitted. Kernel reduction said: Tactic `decide` proved that the proposition
  (Expr.Raw.infer Schema Raw).isSome = true
is false
-/
#guard_msgs in
preo Reused where
  field marker : Counter
  typed derive Broken over { schema := [], reach := [] } :=
    .boolNot (.litNat 7)

/- Reusing the failed command's exact declaration name is the rollback gate.
If any namespace constant or report row leaked, this declaration fails. -/
preo Reused where
  field marker : Counter

/--
error: preo_protocol: crossing origin 1 is outside declared crossing count 1
-/
#guard_msgs in
preo_protocol BadCrossing over Unit at () :=
  .operation {
    id := 1,
    crossings := 1,
    needs := [{
      origin := .crossing(1),
      demand := {
        currency := .peerBarrier,
        participants := [0],
        scope := 0,
        epoch := 0,
        evidence := .none,
        round := 0,
        barrier := 0 } }] }

/- The native command is transactional too. -/
preo_protocol BadCrossing over Unit at () :=
  .operation { id := 1, crossings := 0, needs := [] }

end PreoBench.Golden.DiagnosticsRollback
