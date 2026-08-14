/-
# Uwueave.Preo.ArtifactV3Surface — transactional checked V3 export

`preo_export_v3` consumes the exact proof-bearing values retained by the state
program, authenticated world observation, checked scheduling plan, and checked
five-currency budget.  Result status, effect, visibility, disclosure, and the
certificate row are never accepted as first-order caller input: they are
projected only through `ArtifactV3Checked` builders.

The command is a separate syntax kind from the immutable V2 `preo_export`.
Every generated declaration belongs to one environment transaction.  An
explicit finite work limit is checked before result construction, and V3
validation remains the final fail-closed admission boundary.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Preo.ObservedBoundResult
import Uwueave.Preo.ArtifactV3Checked
import Uwueave.Preo.ArtifactV3Durable
import Uwueave.Preo.ProjectionV3Core

namespace Uwueave.Preo.ArtifactV3Surface

open Lean Elab Command
open Uwueave.Preo.Elab.Internal

set_option autoImplicit false

/-! ## Explicit work accounting -/

/-- A small, deterministic source-size estimate used only to refuse automatic
surface expansion before constructing checked result rows or running V3
validation.  It counts all authored outer rows, the variable-size plan/session
payloads, query dependencies, hole paths, and state analysis sites. -/
def workEstimate {State : Type} {Γ : Uwueave.Preo.Expr.Schema}
    (base : Uwueave.Preo.Artifact.Artifact)
    (source : Uwueave.Preo.StateProgram State Γ) : Nat :=
  1 + base.fields.length + base.invariants.length + base.futures.length +
    base.sessions.length + base.plans.length + base.budgets.length +
    (base.sessions.map (fun row => row.obligations.length)).sum +
    (base.plans.map (fun row => row.actions.length + row.profile.length)).sum +
    (base.budgets.map
      (fun row => row.limits.length + row.realizedProfile.length)).sum +
    source.stateReach.length + source.program.reads.length +
    source.program.holes.length +
    (source.program.holes.map (fun hole => hole.path.length)).sum

/-! ## Exact authenticated-observation gate -/

/-- Identity eliminator whose argument head is the real authenticated observed
report family.  The elaborator deliberately routes the surface term through
this function instead of accepting any record with similarly named
projections. -/
def exactObserved
    {M : Uwueave.Preo.Future.WorldModel} {State β : Type}
    {stateFuture : Uwueave.Evidence.Future State}
    {resolution : Uwueave.StatusEffects.Resolution State β}
    {future : Uwueave.Preo.Future.FutureDecl M}
    {source : Uwueave.Preo.ResultProgram.CheckedDeclaration
      State β stateFuture resolution}
    {boundary : Uwueave.Preo.ResultProgram.ObservationBoundary M.World State}
    {binding : Uwueave.Preo.BoundResult.WorldBinding future source}
    {runningReach : List M.World} {K : Type} {key : M.World → K} {C : K → Prop}
    {index : Uwueave.Preo.Future.WorldIndex M}
    (report : Uwueave.Preo.ObservedBoundResult.ObservedCertifiedReport
      boundary binding runningReach key C index) :
    Uwueave.Preo.ObservedBoundResult.ObservedCertifiedReport
      boundary binding runningReach key C index :=
  report

/-- A checked certificate kept behind the exact `CheckedResult` which fixes its
otherwise non-invertible `StateProgram.declaration` indices. -/
structure CertificatePackage
    {State : Type} {Γ : Uwueave.Preo.Expr.Schema}
    {source : Uwueave.Preo.StateProgram State Γ}
    {stateResolution : Uwueave.StatusEffects.Resolution
      State source.program.type.denote}
    {name futureName : String}
    {stateSurface : Uwueave.Preo.ResultProgram.SurfacePolicy
      State source.program.type.denote}
    {M : Uwueave.Preo.Future.WorldModel}
    {futureDecl : Uwueave.Preo.Future.FutureDecl M}
    {binding : Uwueave.Preo.BoundResult.WorldBinding futureDecl
      (source.declaration name futureName stateResolution stateSurface)}
    {K : Type} {key : M.World → K} {C : K → Prop}
    {index : Uwueave.Preo.Future.WorldIndex M}
    {base : Uwueave.Preo.Artifact.Artifact}
    {query : Uwueave.Preo.ArtifactV3.CheckedQuery base source}
    {future : Uwueave.Preo.Artifact.CheckedFuture futureDecl.future}
    {world : Uwueave.Preo.ArtifactV3.CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (_result : Uwueave.Preo.ArtifactV3.CheckedResult query future world report) where
  checked : Uwueave.Preo.ArtifactV3.CheckedCertificate
    (future := future) (world := world) report

/-- Construct the package only through the checked V3 certificate builder. -/
def certificateOfCheckedResult
    {State : Type} {Γ : Uwueave.Preo.Expr.Schema}
    {source : Uwueave.Preo.StateProgram State Γ}
    {stateResolution : Uwueave.StatusEffects.Resolution
      State source.program.type.denote}
    {name futureName : String}
    {stateSurface : Uwueave.Preo.ResultProgram.SurfacePolicy
      State source.program.type.denote}
    {M : Uwueave.Preo.Future.WorldModel}
    {futureDecl : Uwueave.Preo.Future.FutureDecl M}
    {binding : Uwueave.Preo.BoundResult.WorldBinding futureDecl
      (source.declaration name futureName stateResolution stateSurface)}
    {K : Type} {key : M.World → K} {C : K → Prop}
    {index : Uwueave.Preo.Future.WorldIndex M}
    {base : Uwueave.Preo.Artifact.Artifact}
    {query : Uwueave.Preo.ArtifactV3.CheckedQuery base source}
    {future : Uwueave.Preo.Artifact.CheckedFuture futureDecl.future}
    {world : Uwueave.Preo.ArtifactV3.CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (result : Uwueave.Preo.ArtifactV3.CheckedResult query future world report)
    (id : Uwueave.Preo.ArtifactV3.CertificateId) : CertificatePackage result :=
  ⟨Uwueave.Preo.ArtifactV3.CheckedCertificate.ofCertifiedReport
    (future := future) (world := world) report id⟩

/-- Append a packaged certificate through the checked aggregate builder. -/
def addCertificateOfCheckedResult
    {State : Type} {Γ : Uwueave.Preo.Expr.Schema}
    {source : Uwueave.Preo.StateProgram State Γ}
    {stateResolution : Uwueave.StatusEffects.Resolution
      State source.program.type.denote}
    {name futureName : String}
    {stateSurface : Uwueave.Preo.ResultProgram.SurfacePolicy
      State source.program.type.denote}
    {M : Uwueave.Preo.Future.WorldModel}
    {futureDecl : Uwueave.Preo.Future.FutureDecl M}
    {binding : Uwueave.Preo.BoundResult.WorldBinding futureDecl
      (source.declaration name futureName stateResolution stateSurface)}
    {K : Type} {key : M.World → K} {C : K → Prop}
    {index : Uwueave.Preo.Future.WorldIndex M}
    {base : Uwueave.Preo.Artifact.Artifact}
    {query : Uwueave.Preo.ArtifactV3.CheckedQuery base source}
    {future : Uwueave.Preo.Artifact.CheckedFuture futureDecl.future}
    {world : Uwueave.Preo.ArtifactV3.CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    {result : Uwueave.Preo.ArtifactV3.CheckedResult query future world report}
    (encoding : Uwueave.Preo.ArtifactV3.ArtifactV3Encoding)
    (certificate : CertificatePackage result)
    (futurePresent : encoding.base.futures.any
      (fun row => row.id == future.id.value) = true)
    (worldPresent : encoding.worlds.contains world.id = true)
    (idOrdered : ∀ previous ∈ encoding.certificates,
      previous.id.value < certificate.checked.id.value) :
    Uwueave.Preo.ArtifactV3.ArtifactV3Encoding :=
  encoding.addCertificate certificate.checked futurePresent worldPresent idOrdered

/-- Assemble the one-query checked V3 encoding without re-elaborating the
append-only builder proofs below every exported prefix.  The arguments retain
the same checked indices and exact base-membership premise as that builder
chain; its four singleton appends are written in their reduced record form.
This avoids generating nine large, prefix-specific auxiliary proof
declarations for each export. -/
def encodingOfCheckedResult
    {State : Type} {Γ : Uwueave.Preo.Expr.Schema}
    {source : Uwueave.Preo.StateProgram State Γ}
    {stateResolution : Uwueave.StatusEffects.Resolution
      State source.program.type.denote}
    {name futureName : String}
    {stateSurface : Uwueave.Preo.ResultProgram.SurfacePolicy
      State source.program.type.denote}
    {M : Uwueave.Preo.Future.WorldModel}
    {futureDecl : Uwueave.Preo.Future.FutureDecl M}
    {binding : Uwueave.Preo.BoundResult.WorldBinding futureDecl
      (source.declaration name futureName stateResolution stateSurface)}
    {K : Type} {key : M.World → K} {C : K → Prop}
    {index : Uwueave.Preo.Future.WorldIndex M}
    {base : Uwueave.Preo.Artifact.Artifact}
    {query : Uwueave.Preo.ArtifactV3.CheckedQuery base source}
    {future : Uwueave.Preo.Artifact.CheckedFuture futureDecl.future}
    {world : Uwueave.Preo.ArtifactV3.CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    {result : Uwueave.Preo.ArtifactV3.CheckedResult query future world report}
    (exactBranch : report.ExactBranch)
    (certificate : CertificatePackage result)
    (_futurePresent : base.futures.any
      (fun row => row.id == future.id) = true) :
    Uwueave.Preo.ArtifactV3.ArtifactV3Encoding where
  base := base.canonicalEncoding
  schema := query.schema
  worlds := [world.id]
  queries := [query.toRow]
  results := [result.toExactRow exactBranch]
  certificates := [certificate.checked.toRow]

/-- Extract the validated value once `ValidationResult.isOk` has been checked.
The command emits only a call to this shared eliminator, rather than a fresh
dependent match and its auxiliary declarations below every export prefix. -/
noncomputable def validatedOfIsOk
    (validation : Uwueave.Preo.ProjectionV3.ValidationResult
      Uwueave.Preo.ProjectionV3.ValidatedProjectionV3)
    (accepted : validation.isOk = true) :
    Uwueave.Preo.ProjectionV3.ValidatedProjectionV3 :=
  match validation with
  | .ok value => value
  | .error _ => False.elim (Bool.noConfusion accepted)

/-! ## Parser-hard surface -/

/-- Export one exact checked state program and authenticated certified report.
Arbitrary Lean terms are punctuation-delimited.  `maxWork` and `config` are
both explicit: the first bounds command expansion and the second bounds the
data-only V3 validator. -/
syntax (name := preoExportV3Command)
  "preo_export_v3 " ident ppSpace &"from" ppSpace ident ppSpace ":=" ppSpace "{"
  ppLine colGe (&"base" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"futureDecl" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"binding" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"index" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"observed" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"certificate" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"plan" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"budget" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"query" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"future" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"world" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"resolutionId" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"surfaceId" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"reasonId" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"certificateId" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"branch" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"maxWork" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"config" ppSpace ":=" ppSpace term)
  ppLine colGe "}" : command

/-- Compatibility-sensitive names emitted below one export prefix. -/
structure Names where
  stateProgram : Ident
  base : Ident
  futureDecl : Ident
  binding : Ident
  index : Ident
  observedReport : Ident
  report : Ident
  certificateSource : Ident
  plan : Ident
  budget : Ident
  query : Ident
  future : Ident
  world : Ident
  resolution : Ident
  surface : Ident
  result : Ident
  exactBranch : Ident
  certificate : Ident
  encoding : Ident
  projection : Ident
  validationConfig : Ident
  validation : Ident
  validationOk : Ident
  validated : Ident
  checked : Ident
  durableFormat : Ident
  bytes : Ident
  workLimit : Ident
  workEstimate : Ident
  workOk : Ident
  observedBindingExact : Ident
  observedIndexExact : Ident
  certificateExact : Ident
  planInBase : Ident
  budgetInBase : Ident
  budgetPlanExact : Ident
  futureInBase : Ident

private def suffix (base : Ident) (tail : Name) : Ident :=
  mkIdent (base.getId ++ tail)

def Names.ofSurface (name : Ident) : Names where
  stateProgram := suffix name `StateProgram
  base := suffix name `Base
  futureDecl := suffix name `FutureDecl
  binding := suffix name `Binding
  index := suffix name `Index
  observedReport := suffix name `ObservedReport
  report := suffix name `Report
  certificateSource := suffix name `CertificateSource
  plan := suffix name `Plan
  budget := suffix name `Budget
  query := suffix name `Query
  future := suffix name `Future
  world := suffix name `World
  resolution := suffix name `Resolution
  surface := suffix name `Surface
  result := suffix name `Result
  exactBranch := suffix name `ExactBranch
  certificate := suffix name `Certificate
  encoding := suffix name `Encoding
  projection := suffix name `Projection
  validationConfig := suffix name `ValidationConfig
  validation := suffix name `Validation
  validationOk := suffix name `validation_ok
  validated := suffix name `Validated
  checked := suffix name `Checked
  durableFormat := suffix name `DurableFormat
  bytes := suffix name `Bytes
  workLimit := suffix name `WorkLimit
  workEstimate := suffix name `WorkEstimate
  workOk := suffix name `work_ok
  observedBindingExact := suffix name `observed_binding_exact
  observedIndexExact := suffix name `observed_index_exact
  certificateExact := suffix name `certificate_exact
  planInBase := suffix name `plan_in_base
  budgetInBase := suffix name `budget_in_base
  budgetPlanExact := suffix name `budget_plan_exact
  futureInBase := suffix name `future_in_base

/-- Emit one mandatory declaration while replacing its raw Lean failure with a
surface-phase diagnostic.  `probeCommand` commits successful declarations and
rolls back only the failed command; the enclosing transaction owns the prefix. -/
private def emitPhase (ref : Syntax) (phase : String) (cmd : Syntax) :
    CommandElabM Unit := do
  match ← probeCommand cmd with
  | .ok _ => pure ()
  | .error why =>
      throwErrorAt ref "preo_export_v3: {phase}. The whole export prefix was \
        rolled back and may be reused. Kernel elaboration said: {why}"

/-- Preflight a reducible proposition directly in the term elaborator.  This
turns a false finite check into one phase diagnostic before its public theorem
is emitted; the theorem is still emitted and kernel checked after acceptance. -/
private def requireDecidable (ref : Syntax) (phase : String) (proposition : Term) :
    CommandElabM Unit := do
  let savedMessages := (← get).messages
  modify fun state => { state with messages := {} }
  let outcome ← try
    liftTermElabM do
      let expected ← Term.elabType proposition
      let proof ← Term.elabTerm (← `(by decide)) expected
      Term.synthesizeSyntheticMVarsNoPostponing
      discard <| instantiateMVars proof
    pure true
  catch exception =>
    if exception.isInterrupt then throw exception
    pure false
  let localMessages := (← get).messages
  let accepted := outcome && !localMessages.hasErrors
  modify fun state => { state with messages := savedMessages }
  unless accepted do
    throwErrorAt ref "preo_export_v3: {phase}. The whole export prefix was \
      rolled back and may be reused."

/-- Non-registered implementation for direct transaction testing. -/
def elabPreoExportV3Core : CommandElab := fun stx => withEnvTransaction do
  let `(command| preo_export_v3 $name:ident from $program:ident := {
      base := $base,
      futureDecl := $futureDecl,
      binding := $binding,
      index := $index,
      observed := $observed,
      certificate := $certificate,
      plan := $plan,
      budget := $budget,
      query := $query,
      future := $future,
      world := $world,
      resolutionId := $resolutionId,
      surfaceId := $surfaceId,
      reasonId := $reasonId,
      certificateId := $certificateId,
      branch := $branch,
      maxWork := $maxWork,
      config := $config
    }) := stx
    | throwErrorAt stx "preo_export_v3: malformed checked export"
  let n := Names.ofSurface name
  let programResult := suffix program `Result
  let programResolution := suffix program `Resolution
  let programPolicy := suffix program `Policy
  let programState := suffix program `State
  let programSchema := suffix program `Schema
  let programFutureId := suffix program `FutureId
  let ns ← getCurrNamespace

  emitPhase program "the source must be an exact checked `StateProgram`" <| ← `(command|
    def $(n.stateProgram) := $program)
  emitPhase base "the base artifact did not elaborate" <| ← `(command|
    def $(n.base) : Uwueave.Preo.Artifact.Artifact := $base)
  emitPhase futureDecl "the future declaration did not elaborate" <| ← `(command|
    def $(n.futureDecl) := $futureDecl)
  emitPhase binding "the binding is not for the exact future declaration and \
      state-program result" <| ← `(command|
    def $(n.binding) : Uwueave.Preo.BoundResult.WorldBinding
        $(n.futureDecl) $programResult := $binding)
  emitPhase index "the world index did not elaborate" <| ← `(command|
    def $(n.index) := $index)
  emitPhase observed "the observed input is not an exact \
      `ObservedBoundResult.ObservedCertifiedReport`; a bare certified report or \
      a lookalike record does not retain the external authenticity and separate \
      running-reach premises" <| ← `(command|
    def $(n.observedReport) :=
      Uwueave.Preo.ArtifactV3Surface.exactObserved $observed)
  emitPhase observed "the observed report is for a different binding/future" <| ← `(command|
    theorem $(n.observedBindingExact) :
        ($(n.observedReport)).binding = $(n.binding) := rfl)
  emitPhase observed "the observed report is for a different world index" <| ← `(command|
    theorem $(n.observedIndexExact) :
        ($(n.observedReport)).index = $(n.index) := rfl)
  emitPhase observed "the observed value does not expose the exact certified \
      report required by V3" <| ← `(command|
    def $(n.report) := ($(n.observedReport)).report)
  emitPhase certificate "the certificate is not the exact certificate retained \
      by the authenticated observed report" <| ← `(command|
    def $(n.certificateSource) := $certificate)
  emitPhase certificate "the certificate differs from the report's exact \
      future, answer function, or world index" <| ← `(command|
    theorem $(n.certificateExact) :
        $(n.certificateSource) = ($(n.observedReport)).certificate := rfl)

  emitPhase plan "the checked plan did not elaborate" <| ← `(command|
    def $(n.plan) := $plan)
  requireDecidable plan "the exact checked plan row is absent from the supplied \
    base artifact" (← `(Uwueave.Preo.Artifact.CheckedPlan.toArtifact $(n.plan) ∈
      ($(n.base)).plans))
  emitPhase plan "the exact checked plan row is absent from the supplied base \
      artifact" <| ← `(command|
    theorem $(n.planInBase) :
        Uwueave.Preo.Artifact.CheckedPlan.toArtifact $(n.plan) ∈
          ($(n.base)).plans := by decide)
  emitPhase budget "the checked five-currency budget did not elaborate" <| ← `(command|
    def $(n.budget) := $budget)
  requireDecidable budget "the exact checked budget row is absent from the \
    supplied base artifact" (← `(Uwueave.Preo.Artifact.CheckedBudget.toArtifact
      $(n.budget) ∈ ($(n.base)).budgets))
  emitPhase budget "the exact checked budget row is absent from the supplied \
      base artifact" <| ← `(command|
    theorem $(n.budgetInBase) :
        Uwueave.Preo.Artifact.CheckedBudget.toArtifact $(n.budget) ∈
          ($(n.base)).budgets := by decide)
  requireDecidable budget "the checked budget names a different exact checked \
    plan" (← `(($(n.budget)).planId = ($(n.plan)).id))
  emitPhase budget "the checked budget names a different exact checked plan" <| ← `(command|
    theorem $(n.budgetPlanExact) :
        ($(n.budget)).planId = ($(n.plan)).id := by decide)

  emitPhase query "the checked query is not indexed by the exact supplied base \
      and StateProgram" <| ← `(command|
    def $(n.query) : Uwueave.Preo.ArtifactV3.CheckedQuery
        $(n.base) $(n.stateProgram) := $query)
  emitPhase future "the checked future is not indexed by the exact future \
      declaration" <| ← `(command|
    def $(n.future) : Uwueave.Preo.Artifact.CheckedFuture
        ($(n.futureDecl)).future := $future)
  emitPhase future "the exact checked future row is absent from the supplied \
      base artifact" <| ← `(command|
    theorem $(n.futureInBase) :
        ($(n.base)).futures.any
          (fun row => row.id == ($(n.future)).id) = true := by decide)
  emitPhase world "the checked world is not indexed by the exact observed world \
      index" <| ← `(command|
    def $(n.world) : Uwueave.Preo.ArtifactV3.CheckedWorld $(n.index) := $world)

  emitPhase maxWork "the explicit work limit did not elaborate" <| ← `(command|
    def $(n.workLimit) : Nat := $maxWork)
  emitPhase maxWork "the automatic V3 route exceeded `maxWork`; reduce the \
      authored base/program scope or raise the explicit cap" <| ← `(command|
    def $(n.workEstimate) : Nat :=
      Uwueave.Preo.ArtifactV3Surface.workEstimate
        $(n.base) $(n.stateProgram))
  requireDecidable maxWork "the automatic V3 route exceeded `maxWork`; reduce \
    the authored base/program scope or raise the explicit cap"
    (← `(($(n.workEstimate) ≤ $(n.workLimit))))
  emitPhase maxWork "the automatic V3 route exceeded `maxWork`; reduce the \
      authored base/program scope or raise the explicit cap" <| ← `(command|
    theorem $(n.workOk) : $(n.workEstimate) ≤ $(n.workLimit) := by decide)

  emitPhase resolutionId "the resolution identity map did not match the exact \
      StateProgram resolution" <| ← `(command|
    def $(n.resolution) : Uwueave.Preo.ArtifactV3.CheckedResolution
        $programResolution :=
      Uwueave.Preo.ArtifactV3.CheckedResolution.ofResolution
        $programResolution $resolutionId)
  emitPhase surfaceId "the surface/reason identities did not match the exact \
      StateProgram policy" <| ← `(command|
    def $(n.surface) : Uwueave.Preo.ArtifactV3.CheckedSurface $programPolicy :=
      Uwueave.Preo.ArtifactV3.CheckedSurface.ofPolicy
        $programPolicy $surfaceId $reasonId)
  emitPhase observed "the query, future, world, certificate-gated report, \
      resolution, or surface are not one exact checked result" <| ← `(command|
    def $(n.result) :=
      Uwueave.Preo.ArtifactV3.CheckedResult.ofCertifiedReport
        $(n.query) $(n.future) $(n.world) $(n.report)
        $(n.resolution) $(n.surface))
  emitPhase branch "the exact branch does not select the value certified by \
      this exact report" <| ← `(command|
    def $(n.exactBranch) : ($(n.report)).ExactBranch := $branch)
  emitPhase certificateId "the certificate ID did not elaborate for the exact \
      future/world/report triple" <| ← `(command|
    def $(n.certificate) :=
      Uwueave.Preo.ArtifactV3Surface.certificateOfCheckedResult
        (State := $programState) (Γ := $programSchema)
        (source := $(n.stateProgram))
        (stateResolution := $programResolution)
        (futureName := $programFutureId)
        (stateSurface := $programPolicy)
        (futureDecl := $(n.futureDecl)) (binding := $(n.binding))
        (index := $(n.index)) (base := $(n.base))
        (query := $(n.query)) (future := $(n.future)) (world := $(n.world))
        (report := $(n.report)) $(n.result) $certificateId)

  emitPhase name "the checked append-only V3 builder chain was refused" <| ← `(command|
    def $(n.encoding) : Uwueave.Preo.ArtifactV3.ArtifactV3Encoding :=
      Uwueave.Preo.ArtifactV3Surface.encodingOfCheckedResult
        (State := $programState) (Γ := $programSchema)
        (source := $(n.stateProgram))
        (stateResolution := $programResolution)
        (futureName := $programFutureId)
        (stateSurface := $programPolicy)
        (futureDecl := $(n.futureDecl)) (binding := $(n.binding))
        (index := $(n.index)) (base := $(n.base))
        (query := $(n.query)) (future := $(n.future)) (world := $(n.world))
        (report := $(n.report)) (result := $(n.result))
        $(n.exactBranch) $(n.certificate) $(n.futureInBase))
  emitRequired (← `(command|
    def $(n.projection) : Uwueave.Preo.ProjectionV3.Projection :=
      Uwueave.Preo.ProjectionV3.Projection.ofEncoding $(n.encoding)))
  emitPhase config "the explicit V3 validation config did not elaborate" <| ← `(command|
    def $(n.validationConfig) : Uwueave.Preo.ProjectionV3.ValidationConfig := $config)
  emitRequired (← `(command|
    def $(n.validation) : Uwueave.Preo.ProjectionV3.ValidationResult
        Uwueave.Preo.ProjectionV3.ValidatedProjectionV3 :=
      Uwueave.Preo.ProjectionV3.validate
        $(n.validationConfig) $(n.projection)))
  requireDecidable config "V3 validation refused the checked encoding (resource \
    bound, stable identity, ordering, or cross-row reference failure)"
    (← `((($(n.validation)).isOk = true)))
  emitPhase config "V3 validation refused the checked encoding (resource bound, \
      stable identity, ordering, or cross-row reference failure)" <| ← `(command|
    theorem $(n.validationOk) : ($(n.validation)).isOk = true := by decide)
  emitRequired (← `(command|
    noncomputable def $(n.validated) :
        Uwueave.Preo.ProjectionV3.ValidatedProjectionV3 :=
      Uwueave.Preo.ArtifactV3Surface.validatedOfIsOk
        $(n.validation) $(n.validationOk)))
  emitRequired (← `(command|
    /-- The whole validation-admitted export value. -/
    noncomputable def $(n.checked) :
        Uwueave.Preo.ProjectionV3.ValidatedProjectionV3 := $(n.validated)))
  emitRequired (← `(command|
    def $(n.durableFormat) : Uwueave.Durable.FormatTag :=
      Uwueave.Preo.ArtifactV3Durable.artifactV3Format))
  emitRequired (← `(command|
    noncomputable def $(n.bytes) : Uwueave.Preo.ArtifactV3Durable.Bytes :=
      Uwueave.Preo.ArtifactV3Durable.projectionBytes $(n.encoding)))

  floorCheck program "V3 StateProgram" (ns ++ n.stateProgram.getId)
  floorCheck observed "authenticated observed report"
    (ns ++ n.observedReport.getId)
  floorCheck certificate "exact observed certificate"
    (ns ++ n.certificateExact.getId)
  floorCheck plan "checked plan" (ns ++ n.plan.getId)
  floorCheck budget "checked budget" (ns ++ n.budget.getId)
  floorCheck name "checked V3 result" (ns ++ n.result.getId)
  floorCheck name "checked V3 encoding" (ns ++ n.encoding.getId)
  floorCheck name "validated V3 export" (ns ++ n.validated.getId)

@[command_elab preoExportV3Command]
def elabPreoExportV3 : CommandElab := elabPreoExportV3Core

end Uwueave.Preo.ArtifactV3Surface
