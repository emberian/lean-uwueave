import Uwueave.Preo.Elab

namespace PreoBench.RollbackNegative

open Uwueave Uwueave.Preo

/--
error: preo: `typed derive Broken` was refused by `Preo.Expr.Raw.infer`. The expression is malformed, reads a field outside its schema, applies an operator at the wrong type, or uses raw `.custom`, which has no implementation/locality proof. No typed term or positive analysis was emitted. Kernel reduction said: Tactic `decide` proved that the proposition
  (Expr.Raw.infer Schema Raw).isSome = true
is false
-/
#guard_msgs in
preo Subject where
  field marker : Counter
  typed derive Broken over { schema := [], reach := [] } :=
    .boolNot (.litNat 7)

end PreoBench.RollbackNegative
