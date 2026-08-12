/-
# Wave27AcceptanceSupport — test-only declaration assertions

Wave-27 acceptance fixtures run in fresh Lean subprocesses.  These commands
observe only whether a transactional command published a declaration.  Keeping
them below `tests/` prevents test machinery from entering the public module
graph or the root trust count.
-/
import Lean

namespace Wave27AcceptanceSupport

open Lean Elab Command

syntax "#assert_decl " ident : command
syntax "#assert_no_decl " ident : command

elab_rules : command
  | `(command| #assert_decl $decl:ident) => do
      let name ← resolveGlobalConstNoOverload decl
      unless (← getEnv).contains name do
        throwErrorAt decl "expected declaration `{name}` to be present"
  | `(command| #assert_no_decl $decl:ident) => do
      let candidate := (← getCurrNamespace) ++ decl.getId
      if (← getEnv).contains candidate then
        throwErrorAt decl "expected declaration `{candidate}` to be absent"

end Wave27AcceptanceSupport
