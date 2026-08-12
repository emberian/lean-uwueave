/-
# PreoV3AcceptanceSupport — test-only environment assertions

The Wave-26 acceptance suite compiles every fixture in a fresh Lean process.
These commands assert the only transactional state visible to a downstream
consumer: whether a generated declaration exists after success or failure.
This module is intentionally outside the public `Uwueave` module tree.
-/
import Lean

namespace PreoV3AcceptanceSupport

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

end PreoV3AcceptanceSupport
