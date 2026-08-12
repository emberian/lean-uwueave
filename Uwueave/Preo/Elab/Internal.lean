/-
# Uwueave.Preo.Elab.Internal -- shared command-elaboration infrastructure

This module is deliberately small.  The phase modules under `Preo.Elab` use
these operations to emit ordinary Lean declarations while keeping optional
route probes and required declarations on distinct failure paths.
-/
import Uwueave.Preo.Classification
import Uwueave.Preo.Future
import Uwueave.Protocol
import Uwueave.TrustFloor

namespace Uwueave.Preo.Elab.Internal

open Lean Elab Command Term Meta

/-- Render source syntax as one compact line for report metadata. -/
def renderSyntax (stx : Syntax) : String :=
  (((stx.reprint.getD "?").replace "\n" " ").replace "  " " ").trimAscii.toString

/-- Whether a type currently has an instance.

This is only an applicability probe.  Any route selected by it must still emit
and kernel-check its evidence term. -/
def canSynth (tyStx : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyStx
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← Meta.trySynthInstance ty with
      | .some _ => pure true
      | _ => pure false
    catch _ => pure false

/-- Does a written type reduce to the checked-certificate family? -/
def isCheckedCertificateType (tyStx : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars ty
      let ty ← withDefault <| whnf ty
      pure (ty.getAppFn.constName? ==
        some ``Uwueave.Preo.Future.CheckedCertificate)
    catch _ => pure false

/-- Does a source term have `Protocol.Elaboration` at the head of its type? -/
def isProtocolElaborationTerm (termStx : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let value ← Term.elabTerm termStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars (← inferType value)
      let ty ← withDefault <| whnf ty
      pure (ty.getAppFn.constName? == some ``Uwueave.Protocol.Elaboration)
    catch _ => pure false

private def latestError (messages : MessageLog) : CommandElabM String := do
  let errors := messages.toList.filter ( ·.severity == .error )
  match errors.reverse.head? with
  | some message => message.data.toString
  | none => pure "the command did not elaborate"

/-- Attempt an optional generated command transactionally.

Failure returns its diagnostic as data and restores both the environment and
message log.  Macro scopes and name generators deliberately continue forward:
rewinding them would permit two generated commands to reuse hygiene state. -/
def probeCommand (cmd : Syntax) : CommandElabM (Except String Unit) := do
  let savedEnv ← getEnv
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  try
    elabCommand cmd
    let localMessages := (← get).messages
    if localMessages.hasErrors then
      let why ← latestError localMessages
      modify fun state => { state with env := savedEnv, messages := savedMessages }
      return .error why
    modify fun state => { state with messages := savedMessages ++ localMessages }
    return .ok ()
  catch exception =>
    modify fun state => { state with env := savedEnv, messages := savedMessages }
    if exception.isInterrupt then throw exception
    return .error (← exception.toMessageData.toString)

/-- Compatibility spelling for the original elaborator's optional route API. -/
abbrev tryEmit := probeCommand

/-- Emit a mandatory generated command.

Unlike an optional route probe, a logged elaboration error aborts the enclosing
phase.  The failing command's environment is restored, while its diagnostics
remain visible.  An enclosing `withEnvTransaction` then rolls back declarations
emitted by earlier phases of the same surface command. -/
def emitRequired (cmd : Syntax) : CommandElabM Unit := do
  let savedEnv ← getEnv
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  let failure? ←
    try
      elabCommand cmd
      pure none
    catch exception => pure (some exception)
  let localMessages := (← get).messages
  if localMessages.hasErrors || failure?.isSome then
    modify fun state => {
      state with env := savedEnv, messages := savedMessages ++ localMessages }
    match failure? with
    | some exception => throw exception
    | none => throwAbortCommand
  modify fun state => { state with messages := savedMessages ++ localMessages }

/-- Run one surface command as an environment transaction.

Environment extensions are part of `Environment`, so this also rolls back
`preoExt` entries.  Diagnostics survive failure; hygiene/name counters and all
other monotone command state are not rewound. -/
def withEnvTransaction (action : CommandElabM α) : CommandElabM α := do
  let savedEnv ← getEnv
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  let outcome : Except Exception α ←
    try
      pure (Except.ok (← action) : Except Exception α)
    catch exception => pure (Except.error exception : Except Exception α)
  let localMessages := (← get).messages
  match outcome with
  | Except.ok result =>
      if localMessages.hasErrors then
        modify fun state => {
          state with env := savedEnv, messages := savedMessages ++ localMessages }
        throwAbortCommand
      modify fun state => { state with messages := savedMessages ++ localMessages }
      return result
  | Except.error exception =>
      modify fun state => {
        state with env := savedEnv, messages := savedMessages ++ localMessages }
      throw exception

/-- Check that a generated evidence constant stays on the repository axiom floor. -/
def floorCheck (ref : Syntax) (what : String) (constant : Name) : CommandElabM Unit := do
  let stray ← Uwueave.TrustFloor.offFloor constant
  unless stray.isEmpty do
    throwErrorAt ref "preo: the {what} `{constant}` depends on \
      {String.intercalate ", " (stray.toList.map toString)} — outside the \
      axiom floor `propext · Classical.choice · Quot.sound` that `#audit_floor` \
      holds the whole tree to. A `sorry` here is a facet with a hole in it, and \
      `native_decide` is the compiled evaluator rather than the kernel; a row \
      printed off either would be exactly the failure this table exists to make \
      impossible. No row is recorded."

/-- Collect the declared field roots mentioned syntactically by a term. -/
partial def mentions (fields : Array Name) (stx : Syntax) : Array Name :=
  go stx #[]
where
  go (node : Syntax) (acc : Array Name) : Array Name :=
    if node.isIdent then
      let name := node.getId.eraseMacroScopes
      let name := if fields.contains name then name else name.getRoot
      if fields.contains name && !acc.contains name then acc.push name else acc
    else
      node.getArgs.foldl (fun found child => go child found) acc

/-- Projection syntax for field `i` of a right-nested `n`-field state. -/
def projPath (i n : Nat) : CommandElabM Term := do
  let mut expression : Term ← `(s)
  for _ in [0:i] do
    expression ← `($expression.2)
  if i + 1 < n then expression ← `($expression.1)
  return expression

/-- Right-nest a nonempty array of component terms. -/
def nest (terms : Array Term) : CommandElabM Term := do
  let n := terms.size
  let mut expression := terms[n - 1]!
  for k in [0:n-1] do
    expression ← `(($(terms[n - 2 - k]!), $expression))
  return expression

/-- Build the planting section for one component of a right-nested state. -/
def plantFn (i n : Nat) (defaults : Array Term) : CommandElabM Term := do
  let mut terms : Array Term := #[]
  for k in [0:n] do
    if k == i then
      terms := terms.push (← `(v))
    else
      terms := terms.push defaults[k]!
  let body ← nest terms
  `(fun v => $body)

end Uwueave.Preo.Elab.Internal
