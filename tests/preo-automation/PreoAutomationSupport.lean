/-
# PreoAutomationSupport — test-only metaprogram acceptance helpers.

The automation acceptance suite compiles each fixture in a fresh Lean process.
These commands let a fixture assert the observable environment after a command:
a successful `preo` must publish its promised declarations, while a failed
command must publish none of them and must leave its top-level name reusable.

This module contains no production classification route and deliberately lives
outside the public `Uwueave` module tree.
-/
import Lean

namespace PreoAutomationSupport

open Lean Elab Command

/-- Assert that a declaration is present in the current environment. -/
syntax "#assert_decl " ident : command

/-- Assert that a declaration is absent from the current environment. -/
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

end PreoAutomationSupport
