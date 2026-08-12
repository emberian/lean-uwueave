/-
# Uwueave.Preo.Elab.TypedDerive — intrinsically typed derive worker

This phase emits the exact `Raw.infer` witness, typed term, analyses,
incremental cache/update API, equality-only snapshot future, six-status result,
and checked report for one `typed derive` row.
-/
import Uwueave.Preo.Elab.Future
import Uwueave.Preo.Incremental
import Uwueave.Preo.ResultProgram

namespace Uwueave.Preo.Elab.TypedDerive

open Lean Elab Command

private def withoutAuxiliaryStructureMetadata (scope : Scope) : Scope :=
  let options := (scope.opts.setBool `genSizeOf false).setBool `genInjectivity false
  { scope with opts := options.setBool `genCtorIdx false }

/-- Emit one intrinsically typed query and all declarations derived from its
single checked `Expr.Program` witness.

Nothing after `Program` is emitted when kernel reduction refuses `Raw.infer`.
In particular, the generated result future is definitionally the program's
equality-only snapshot future; the worker does not infer a stronger relation
from merge or monotonicity certificates. -/
def emit (ctx : Future.Context) (typedDer : Syntax) : CommandElabM Row := do
  let `(preoTypedDerive| typed derive $nm over { schema := $schema, reach := $reach } := $raw) := typedDer
    | throwErrorAt typedDer "preo: malformed `typed derive`"
  let schemaId := mkIdent (ctx.declName ++ (nm.getId ++ `Schema))
  let rawId := mkIdent (ctx.declName ++ (nm.getId ++ `Raw))
  let programId := mkIdent (ctx.declName ++ (nm.getId ++ `Program))
  let checkedId := mkIdent (ctx.declName ++ (nm.getId ++ `Checked))
  let typeId := mkIdent (ctx.declName ++ (nm.getId ++ `Type))
  let termId := mkIdent (ctx.declName ++ (nm.getId ++ `Term))
  let evalId := mkIdent (ctx.declName ++ (nm.getId ++ `Eval))
  let holesId := mkIdent (ctx.declName ++ (nm.getId ++ `Holes))
  let readsId := mkIdent (ctx.declName ++ (nm.getId ++ `Reads))
  let mergeSafeId := mkIdent (ctx.declName ++ (nm.getId ++ `MergeSafe?))
  let monotoneSafeId := mkIdent (ctx.declName ++ (nm.getId ++ `MonotoneSafe?))
  let cacheId := mkIdent (ctx.declName ++ (nm.getId ++ `Cache))
  let buildCacheId := mkIdent (ctx.declName ++ (nm.getId ++ `buildCache))
  let updateId := mkIdent (ctx.declName ++ (nm.getId ++ `update))
  let updateCacheId := mkIdent (ctx.declName ++ (nm.getId ++ `updateCache))
  let updateCorrectId := mkIdent (ctx.declName ++ (nm.getId ++ `update_correct))
  let zeroId := mkIdent (ctx.declName ++ (nm.getId ++ `update_off_dependency_zero))
  let reachId := mkIdent (ctx.declName ++ (nm.getId ++ `Reach))
  let resultFutureId := mkIdent (ctx.declName ++ (nm.getId ++ `ResultFuture))
  let resultId := mkIdent (ctx.declName ++ (nm.getId ++ `Result))
  let resultCarrierId := mkIdent (ctx.declName ++ (nm.getId ++ `ResultCarrier))
  let reachReportId := mkIdent (ctx.declName ++ (nm.getId ++ `ReachReport))
  let reportAtId := mkIdent (ctx.declName ++ (nm.getId ++ `reportAt))
  Internal.emitRequired (← `(command|
    /-- The explicitly written first-order input schema. -/
    abbrev $schemaId : Uwueave.Preo.Expr.Schema := $schema))
  Internal.emitRequired (← `(command|
    /-- The raw typed-derive syntax before inference. -/
    def $rawId : Uwueave.Preo.Expr.Raw := $raw))
  match ← Internal.probeCommand (← `(command|
      /-- The checked program. Its only typed term is extracted from
      `Raw.infer`; the success proof is kernel reduction, not a cast. -/
      def $programId : Uwueave.Preo.Expr.Program $schemaId where
        raw := $rawId
        success := by decide)) with
  | .error why =>
      throwErrorAt raw "preo: `typed derive {nm.getId}` was refused by \
        `Preo.Expr.Raw.infer`. The expression is malformed, reads a field \
        outside its schema, applies an operator at the wrong type, or uses \
        raw `.custom`, which has no implementation/locality proof. No typed \
        term or positive analysis was emitted. Kernel reduction said: {why}"
  | .ok _ => pure ()
  Internal.floorCheck nm "typed program" (ctx.fullDecl ++ (nm.getId ++ `Program))
  Internal.emitRequired (← `(command|
    /-- The exact existential result returned by `Raw.infer`. -/
    def $checkedId : Uwueave.Preo.Expr.Checked $schemaId :=
      Uwueave.Preo.Expr.Program.checked $programId))
  Internal.emitRequired (← `(command|
    /-- The result type inferred from the raw expression. -/
    abbrev $typeId : Uwueave.Preo.Expr.Ty :=
      Uwueave.Preo.Expr.Program.type $programId))
  Internal.emitRequired (← `(command|
    /-- The intrinsically typed term extracted from `Raw.infer`. -/
    def $termId : Uwueave.Preo.Expr.Term $schemaId $typeId :=
      Uwueave.Preo.Expr.Program.term $programId))
  Internal.emitRequired (← `(command|
    /-- Evaluation hook for runtime and six-state result adapters. -/
    def $evalId : Uwueave.Preo.Expr.Env $schemaId →
        Uwueave.Preo.Expr.Ty.denote $typeId :=
      Uwueave.Preo.Expr.Program.eval $programId))
  Internal.emitRequired (← `(command|
    /-- Exact positional dependency occurrences. -/
    def $holesId : List Uwueave.Preo.Expr.Hole :=
      Uwueave.Preo.Expr.Program.holes $programId))
  Internal.emitRequired (← `(command|
    /-- Exact field reads, definitionally the erasure of `Holes`. -/
    def $readsId : List Nat := Uwueave.Preo.Expr.Program.reads $programId))
  Internal.emitRequired (← `(command|
    /-- Proof-carrying positive merge classification; `none` is no claim. -/
    def $mergeSafeId :
        Option (Uwueave.Preo.Expr.MergeSafe $termId) :=
      Uwueave.Preo.Expr.certifyMergeSafe $termId))
  Internal.emitRequired (← `(command|
    /-- Proof-carrying positive monotonicity classification; `none` is no
    claim and is not a refutation. -/
    def $monotoneSafeId :
        Option (Uwueave.Preo.Expr.MonotoneSafe $termId) :=
      Uwueave.Preo.Expr.certifyMonotone $termId))
  Internal.emitRequired (← `(command|
    /-- A cache indexed by this exact inferred term. -/
    abbrev $cacheId := Uwueave.Preo.Incremental.ProgramCache $programId))
  Internal.emitRequired (← `(command|
    /-- Build a cache whose value is proved equal to fresh evaluation. -/
    def $buildCacheId (env : Uwueave.Preo.Expr.Env $schemaId) : $cacheId :=
      Uwueave.Preo.Incremental.buildProgramCache $programId env))
  Internal.emitRequired (← `(command|
    /-- Checked differential update: zero root evaluations on a proved miss,
    exactly one full root evaluation on a conservative hit. -/
    def $updateId (cache : $cacheId)
        (delta : Uwueave.Preo.Incremental.EnvDelta cache.env) :=
      Uwueave.Preo.Incremental.updateProgram $programId cache delta))
  Internal.emitRequired (← `(command|
    theorem $updateCorrectId (cache : $cacheId)
        (delta : Uwueave.Preo.Incremental.EnvDelta cache.env) :
        ($updateId cache delta).value = $evalId delta.after :=
      Uwueave.Preo.Incremental.updateProgram_correct $programId cache delta))
  Internal.emitRequired (← `(command|
    /-- Chain a checked update into the cache for the next typed delta,
    without reevaluating the term. -/
    def $updateCacheId (cache : $cacheId)
        (delta : Uwueave.Preo.Incremental.EnvDelta cache.env) : $cacheId :=
      Uwueave.Preo.Incremental.updateProgramCache $programId cache delta))
  Internal.emitRequired (← `(command|
    theorem $zeroId (cache : $cacheId)
        (delta : Uwueave.Preo.Incremental.EnvDelta cache.env)
        (h : Uwueave.Preo.Incremental.touched delta $termId = false) :
        ($updateId cache delta).recomputations = 0 ∧
          ($updateId cache delta).value = cache.value :=
      Uwueave.Preo.Incremental.updateProgram_off_dependency_zero
        $programId cache delta h))
  Internal.emitRequired (← `(command|
    /-- The author-declared finite reach used for least six-status effect
    inference. It is intentionally independent of the document State unless
    the author supplies a projection into this typed environment. -/
    def $reachId : List (Uwueave.Preo.Expr.Env $schemaId) := $reach))
  Internal.emitRequired (← `(command|
    /-- The honest snapshot future for this pure query: equality only. -/
    abbrev $resultFutureId :
        Uwueave.Evidence.Future (Uwueave.Preo.Expr.Env $schemaId) :=
      Uwueave.Preo.Incremental.TypedResult.Future $programId))
  let resultName := Syntax.mkStrLit s!"{ctx.fullDecl}.{nm.getId}"
  let futureName := Syntax.mkStrLit s!"{ctx.fullDecl}.{nm.getId}/snapshot-equality"
  let surfaceName := Syntax.mkStrLit s!"{ctx.fullDecl}.{nm.getId}/inspectable"
  Internal.emitRequired (← `(command|
    /-- A checked six-status declaration consuming this exact typed
    evaluator and finite reach. Resolution is explicitly preserve-fork;
    equality is the only admitted future. -/
    def $resultId :=
      Uwueave.Preo.Incremental.TypedResult.declaration $programId
        $resultName $futureName $surfaceName $reachId))
  Internal.floorCheck nm "typed result program" (ctx.fullDecl ++ (nm.getId ++ `Result))
  Internal.emitRequired (← `(command|
    /-- The reference six-way carrier used by the generated checked report. -/
    abbrev $resultCarrierId :=
      Uwueave.RenderSix.stdCarrier6 $resultFutureId
        (Uwueave.Preo.Expr.Ty.denote $typeId)))
  Command.withScope withoutAuxiliaryStructureMetadata do
    Internal.emitRequired (← `(command|
      /-- A checked report that retains proof its evaluated site belongs to the
      finite reach used by effect inference. Compiler-generated `SizeOf` and
      injectivity metadata are intentionally suppressed: the constructor,
      projections, recursors, and semantic report API remain public. -/
      structure $reachReportId where
        checked :
          Uwueave.Preo.ResultProgram.CheckedReport $resultId $resultCarrierId
        inReach : checked.state ∈ $reachId))
  Internal.emitRequired (← `(command|
    /-- A checked report whose site, status, future, resolution, visibility
    and disclosure are all computed from the generated result declaration. -/
    def $reportAtId (env : Uwueave.Preo.Expr.Env $schemaId)
        (inReach : env ∈ $reachId) : $reachReportId where
      checked := Uwueave.Preo.ResultProgram.CheckedReport.renderAt
        $resultId $resultCarrierId env
      inReach := inReach))
  return {
    decl := ctx.fullDecl, kind := .typedDerive, name := nm.getId.toString
    detail := Internal.renderSyntax schema
    detail₂ := Internal.renderSyntax raw ++ " on reach " ++ Internal.renderSyntax reach
    evidence := ctx.fullDecl ++ (nm.getId ++ `Program), isObligation := false
    cite := "Expr.Raw.infer → proof-carrying merge/monotone analyses → checked cache/update → finite-reach six-status Result/report"
    seamCite := "" }

end Uwueave.Preo.Elab.TypedDerive
