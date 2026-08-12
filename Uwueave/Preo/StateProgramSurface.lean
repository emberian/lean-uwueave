/-
# Uwueave.Preo.StateProgramSurface — explicit application-state typed queries.

`preo_program` is standalone and punctuation-delimited.  It never infers a
field name or state projection: the author writes the application `State`, the
typed `Schema`, `State → Env Schema`, finite state reach, raw expression,
future identity, resolution syntax, and presentation policy.  Every generated
declaration is required and the whole command is one environment transaction.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Preo.StateProgram

namespace Uwueave.Preo.StateProgramSurface

open Lean Elab Command Uwueave.Preo.Elab.Internal

/-- Bind one raw typed query to an explicitly named application state and
projection.  Terms are separated by parser-hard commas and braces. -/
syntax (name := preoProgramCommand) "preo_program " ident ppSpace &"over" ppSpace "{"
  &"state" " := " term:51 ","
  &"schema" " := " term:51 ","
  &"project" " := " term:51 ","
  &"reach" " := " term:51 ","
  &"raw" " := " term:51 ","
  &"futureId" " := " term:51 ","
  &"resolution" " := " term:51 ","
  &"policy" " := " term "}" : command

/-- The predictable generated API.  The top-level `whole` constant is the
whole checked `StateProgram`; all other constants live below the same prefix. -/
structure Names where
  whole : Ident
  state : Ident
  schema : Ident
  raw : Ident
  program : Ident
  project : Ident
  stateReach : Ident
  envReach : Ident
  type : Ident
  term : Ident
  eval : Ident
  future : Ident
  futureId : Ident
  resolution : Ident
  policy : Ident
  result : Ident
  carrier : Ident
  cache : Ident
  buildCache : Ident
  report : Ident
  reportAt : Ident

def Names.ofSurface (name : Ident) : Names where
  whole := name
  state := mkIdent (name.getId ++ `State)
  schema := mkIdent (name.getId ++ `Schema)
  raw := mkIdent (name.getId ++ `Raw)
  program := mkIdent (name.getId ++ `Program)
  project := mkIdent (name.getId ++ `Project)
  stateReach := mkIdent (name.getId ++ `StateReach)
  envReach := mkIdent (name.getId ++ `EnvReach)
  type := mkIdent (name.getId ++ `Type)
  term := mkIdent (name.getId ++ `Term)
  eval := mkIdent (name.getId ++ `Eval)
  future := mkIdent (name.getId ++ `Future)
  futureId := mkIdent (name.getId ++ `FutureId)
  resolution := mkIdent (name.getId ++ `Resolution)
  policy := mkIdent (name.getId ++ `Policy)
  result := mkIdent (name.getId ++ `Result)
  carrier := mkIdent (name.getId ++ `Carrier)
  cache := mkIdent (name.getId ++ `Cache)
  buildCache := mkIdent (name.getId ++ `buildCache)
  report := mkIdent (name.getId ++ `Report)
  reportAt := mkIdent (name.getId ++ `reportAt)

/-- Non-registered implementation, separated for direct transactional tests. -/
def elabPreoProgramCore : CommandElab := fun stx => withEnvTransaction do
  let `(command| preo_program $name:ident over {
      state := $stateTy,
      schema := $schema,
      project := $project,
      reach := $reach,
      raw := $raw,
      futureId := $futureId,
      resolution := $resolution,
      policy := $policy }) := stx
    | throwErrorAt stx "preo_program: malformed declaration"
  let n := Names.ofSurface name
  emitRequired (← `(command|
    /-- The explicitly authored application state type. -/
    abbrev $(n.state) : Type := $stateTy))
  emitRequired (← `(command|
    /-- The explicitly authored typed query schema. -/
    abbrev $(n.schema) : Uwueave.Preo.Expr.Schema := $schema))
  emitRequired (← `(command|
    /-- The raw expression before checked inference. -/
    def $(n.raw) : Uwueave.Preo.Expr.Raw := $raw))
  match ← probeCommand (← `(command|
      /-- The checked expression; its typed term comes only from `Raw.infer`. -/
      def $(n.program) : Uwueave.Preo.Expr.Program $(n.schema) where
        raw := $(n.raw)
        success := by decide)) with
  | .ok _ => pure ()
  | .error why =>
      throwErrorAt raw "preo_program: `{name.getId}` was refused by \
        `Preo.Expr.Raw.infer`. The raw expression is malformed, reads outside \
        the explicit schema, applies an operator at the wrong type, or is \
        opaque. No checked program or result artifact was emitted. Kernel \
        reduction said: {why}"
  let ns ← getCurrNamespace
  floorCheck name "state program" (ns ++ n.program.getId)
  emitRequired (← `(command|
    /-- The authored application-state to typed-environment projection. -/
    def $(n.project) : $(n.state) → Uwueave.Preo.Expr.Env $(n.schema) := $project))
  emitRequired (← `(command|
    /-- The authored finite application-state analysis reach. This is not a
    discovered or authenticated runtime reach. -/
    def $(n.stateReach) : List $(n.state) := $reach))
  emitRequired (← `(command|
    /-- The whole checked binding: program, projection, and authored reach. -/
    def $(n.whole) : Uwueave.Preo.StateProgram $(n.state) $(n.schema) where
      program := $(n.program)
      project := $(n.project)
      stateReach := $(n.stateReach)))
  emitRequired (← `(command|
    /-- Exactly the image of `StateReach` through `Project`. -/
    def $(n.envReach) : List (Uwueave.Preo.Expr.Env $(n.schema)) :=
      Uwueave.Preo.StateProgram.envReach $(n.whole)))
  emitRequired (← `(command|
    /-- The result type inferred from the raw expression. -/
    abbrev $(n.type) : Uwueave.Preo.Expr.Ty := $(n.program).type))
  emitRequired (← `(command|
    /-- The intrinsically typed term returned by raw inference. -/
    def $(n.term) : Uwueave.Preo.Expr.Term $(n.schema) $(n.type) :=
      $(n.program).term))
  emitRequired (← `(command|
    /-- Evaluation of application state through the explicit projection. -/
    def $(n.eval) : $(n.state) → Uwueave.Preo.Expr.Ty.denote $(n.type) :=
      Uwueave.Preo.StateProgram.eval $(n.whole)))
  emitRequired (← `(command|
    /-- The exact pure-query future: equality of projected environments. -/
    abbrev $(n.future) : Uwueave.Evidence.Future $(n.state) :=
      Uwueave.Preo.StateProgram.Future $(n.whole)))
  emitRequired (← `(command|
    /-- Exportable authored identity for this query future. -/
    def $(n.futureId) : String := $futureId))
  emitRequired (← `(command|
    /-- Explicit fork-resolution syntax; no policy is inferred. -/
    def $(n.resolution) :
        Uwueave.StatusEffects.Resolution $(n.state)
          (Uwueave.Preo.Expr.Ty.denote $(n.type)) := $resolution))
  emitRequired (← `(command|
    /-- Explicit presentation and disclosure policy. -/
    def $(n.policy) :
        Uwueave.Preo.ResultProgram.SurfacePolicy $(n.state)
          (Uwueave.Preo.Expr.Ty.denote $(n.type)) := $policy))
  let resultName := Syntax.mkStrLit s!"{ns ++ name.getId}"
  emitRequired (← `(command|
    /-- Checked six-status result over application states. -/
    def $(n.result) :=
      Uwueave.Preo.StateProgram.declaration $(n.whole) $resultName
        $(n.futureId) $(n.resolution) $(n.policy)))
  floorCheck name "state result program" (ns ++ n.result.getId)
  emitRequired (← `(command|
    /-- Reference six-way carrier at application-state sites. -/
    abbrev $(n.carrier) :=
      Uwueave.RenderSix.stdCarrier6 $(n.future)
        (Uwueave.Preo.Expr.Ty.denote $(n.type))))
  emitRequired (← `(command|
    /-- A cache over the exact projected environment. -/
    abbrev $(n.cache) := Uwueave.Preo.Incremental.ProgramCache $(n.program)))
  emitRequired (← `(command|
    /-- Project one application state and build its checked typed cache. -/
    def $(n.buildCache) (state : $(n.state)) : $(n.cache) :=
      Uwueave.Preo.StateProgram.buildCache $(n.whole) state))
  emitRequired (← `(command|
    /-- A generic checked report retaining state-reach membership. -/
    abbrev $(n.report) :=
      Uwueave.Preo.ResultProgram.ReachReport $(n.result) $(n.carrier)))
  emitRequired (← `(command|
    /-- Report only at a state explicitly admitted by `StateReach`. -/
    def $(n.reportAt) (state : $(n.state))
        (inReach : state ∈ $(n.stateReach)) : $(n.report) :=
      Uwueave.Preo.StateProgram.reportAt $(n.whole) $resultName
        $(n.futureId) $(n.resolution) $(n.policy) state inReach))

@[command_elab preoProgramCommand]
def elabPreoProgram : CommandElab := elabPreoProgramCore

end Uwueave.Preo.StateProgramSurface
