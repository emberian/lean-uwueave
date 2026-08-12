/-
# Uwueave.Preo.Elab.Future — named-future elaboration worker

This module is the small command-elaboration phase for `future` rows inside a
`preo` declaration.  Keeping the phase independent lets the command driver
sequence it without re-elaborating the much larger invariant registry.

The worker returns display metadata only after both emitted declarations have
kernel-checked and the future value has passed the repository axiom floor.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Preo.Future

namespace Uwueave.Preo.Elab

open Lean Elab Command

namespace Future

/-- Declaration identity carried into the named-future phase. `fullDecl` is
stored explicitly so a caller cannot accidentally recompute report identity
under a changed namespace. -/
structure Context where
  declName : Name
  ns : Name
  fullDecl : Name
  deriving Inhabited

/-- Emit one named, explicitly world-model-indexed future and return its row.

The model abbreviation is emitted first, followed by the checked relation and
its floor check. This order is part of the public generated-declaration ABI. -/
def emit (ctx : Context) (future : Syntax) : CommandElabM Row := do
  let `(preoFuture| future $nm on $model := $body) := future
    | throwErrorAt future "preo: malformed future declaration"
  let modelId := mkIdent (ctx.declName ++ (nm.getId ++ `WorldModel))
  let futureId := mkIdent (ctx.declName ++ nm.getId)
  Internal.emitRequired (← `(command|
    /-- The explicit retained-world model indexing this named future. -/
    abbrev $modelId : Uwueave.Preo.Future.WorldModel := $model))
  Internal.emitRequired (← `(command|
    /-- A checked named relation on the retained world carrier. -/
    def $futureId : Uwueave.Preo.Future.FutureDecl $modelId := $body))
  Internal.floorCheck nm "future declaration" (ctx.ns ++ futureId.getId)
  return {
    decl := ctx.fullDecl, kind := .future, name := nm.getId.toString
    detail := Internal.renderSyntax model, detail₂ := Internal.renderSyntax body
    evidence := ctx.ns ++ futureId.getId, isObligation := false
    cite := "Preo.Future.FutureDecl at the explicit WorldModel (kernel-checked)"
    seamCite := "" }

end Future
end Uwueave.Preo.Elab
