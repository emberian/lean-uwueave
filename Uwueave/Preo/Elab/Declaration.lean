/-
# Uwueave.Preo.Elab.Declaration -- transactional `preo` phase orchestrator
-/
import Uwueave.Preo.Elab.State
import Uwueave.Preo.Elab.Invariant
import Uwueave.Preo.Elab.DocumentSeam
import Uwueave.Preo.Elab.Future
import Uwueave.Preo.Elab.TypedDerive
import Uwueave.Preo.Elab.Derive
import Uwueave.Preo.Elab.Protocol

namespace Uwueave.Preo.Elab.Declaration

open Lean Elab Command

/-- Non-registered implementation of one `preo` declaration.

The phase order and row order are part of the surface ABI.  The environment
extension is updated only after every generated declaration and floor check has
succeeded; `withEnvTransaction` also removes all preceding generated constants
if any required late phase fails. -/
def elabPreoDeclCore : CommandElab := fun stx =>
    Internal.withEnvTransaction do
  let `(command| preo $declId:ident where
      $fields:preoField* $invariants:preoInv* $futures:preoFuture*
      $typedDerives:preoTypedDerive* $derives:preoDerive*
      $protocols:preoProtocol* $sessions:preoSession*) := stx
    | throwError "preo: malformed declaration"

  let (ctx, fieldRows) ← State.emit declId fields
  let mut rows := fieldRows
  let mut declarationSeams : Array Invariant.FiredSeam := #[]
  let mut declarationFrees : Array Ident := #[]

  for invariant in invariants do
    let result ← Invariant.emit ctx invariant
    rows := rows.push result.row
    if let some seam := result.seam? then
      declarationSeams := declarationSeams.push seam
    if let some free := result.freeOnState? then
      declarationFrees := declarationFrees.push free

  let _ ← DocumentSeam.emit ctx declarationSeams declarationFrees declId

  let common : Future.Context := {
    declName := ctx.declName, ns := ctx.ns, fullDecl := ctx.fullDecl }
  for future in futures do
    rows := rows.push (← Future.emit common future)
  for typedDerive in typedDerives do
    rows := rows.push (← TypedDerive.emit common typedDerive)

  let deriveCtx : Derive.Context := {
    toContext := common
    stateId := ctx.stateId
    fieldNames := ctx.fieldNames
    fieldIdents := ctx.fieldIdents
    carriers := ctx.carriers }
  for derive in derives do
    rows := rows.push (← Derive.emit deriveCtx derive)

  rows := rows ++ (← Protocol.emitOpaqueProtocols
    ctx.declName ctx.ns ctx.fullDecl protocols)
  rows := rows ++ (← Protocol.emitSessions
    ctx.declName ctx.ns ctx.fullDecl sessions)

  modifyEnv fun env => rows.foldl (fun current row => preoExt.addEntry current row) env
  logInfo m!"preo {ctx.declName}: {ctx.size} field(s), \
    {invariants.size} invariant(s), {futures.size} future(s), \
    {typedDerives.size} typed derive(s), {derives.size} ordinary derive(s), \
    {protocols.size} protocol(s), {sessions.size} session(s) — \
    `#preo_report {ctx.declName}` for the table"

end Uwueave.Preo.Elab.Declaration
