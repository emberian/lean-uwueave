/-
# Uwueave.Audit — the trust gate, total.

One command, whole-tree coverage: `#audit_floor` walks **every constant in the
`Uwueave` namespace** — not a curated list — and fails the build if any of them
depends on an axiom outside Lean's own floor:

    propext · Classical.choice · Quot.sound

That floor is what "a Lean proof" already means; the gate exists for what it
EXCLUDES. `sorry` compiles to `sorryAx` (a plain `lake build` only *warns* on
sorry — without a gate, a hole in a proof ships green). `native_decide`
introduces a generated axiom bridging the compiled evaluator (on the pinned
Lean it is named under `_native.native_decide.ax_…`). Any future custom axiom
lands the same way. All of them are hard build failures here, for every theorem
— including ones written five minutes ago that no list was updated to mention.

## Why this replaced 113 per-theorem `#guard_msgs` pins (2026-08-10)

The previous design pinned each keystone's exact axiom list as a message
string. Honest accounting of what that bought and cost:

  * It DID make `sorry`/`native_decide` a build failure — but only for the
    113 pinned names, lagging the tree by construction (~226 theorems).
  * The per-name footprint strings were noise: whether a proof uses
    `Classical.choice` *within the floor* changes nothing anyone should
    decide by, and the exact-string format broke builds over formatting,
    never over trust.
  * Every lane spent effort ferrying verbatim footprints into the pin file,
    and counts advertised in prose rotted on schedule.

The total gate keeps the tripwire (stronger: total, zero-lag), deletes the
ritual, and drops the within-floor vanity distinctions. Per-theorem axiom
profiles remain one command away for anyone curious: `#print axioms <name>`.
The curated public surface lives in `docs/MAP.md`'s keystone ledger — a
*reading* aid, no longer a trust mechanism.

The gate also carries a vacuity tripwire: if the namespace walk ever audits
suspiciously few constants (an import breaks, a rename empties the filter),
it fails rather than passing on nothing. A gate that cannot go red is not a
gate.

## What this gate does NOT prove — `docs/TRUST.md`

`#audit_floor` establishes **logical hygiene, not semantic adequacy** (the
distinction is codex's, from an external review of this repo). A green gate
says every constant in the namespace was built from `propext`,
`Classical.choice` and `Quot.sound` and nothing else. It says nothing about
whether a theorem's statement corresponds to the protocol we meant; whether a
model is missing an operation or a failure mode; whether the states a theorem
quantifies over are reachable through the shipping API; whether the serialized
bytes implement the abstract state that was proved about; or whether any
docstring — including this one — accurately describes what it sits above. Those
are read by humans and other models, not by the elaborator, and the gate is
blind to all of them by construction. This file is also *not itself a theorem*:
it is an unverified metaprogram auditing the tree from inside the tree.
`docs/TRUST.md` carries the full accounting as three separate ledgers —
logical TCB, execution TCB, environment/model premises — each row classified as
an irreducible premise or a transmutable obligation with a named next step.
-/
import Lean
import Uwueave.TrustFloor
import Uwueave.ListProofs
import Uwueave.Choreo
import Uwueave.Weave
import Uwueave.ORSet
import Uwueave.Causality
import Uwueave.MVRegister
import Uwueave.Segmented
import Uwueave.Undo
import Uwueave.Delta
import Uwueave.Sequence
import Uwueave.ORMap
import Uwueave.Automata
import Uwueave.Authority
import Uwueave.ExecRefine
import Uwueave.Ceiling
import Uwueave.Seams
import Uwueave.Necessity
import Uwueave.CausalReach
import Uwueave.Liveness
import Uwueave.Traces
import Uwueave.Nary
import Uwueave.KernelCFCS
import Uwueave.SeqKernel
import Uwueave.Era
import Uwueave.EraKernel
import Uwueave.Gated
import Uwueave.Fugue
import Uwueave.WeaveState
import Uwueave.GatedEra
import Uwueave.Ancestral
import Uwueave.RALin
import Uwueave.SeamAlgebra
import Uwueave.Gluing
import Uwueave.Holes
import Uwueave.Cost
import Uwueave.JoinHom
import Uwueave.Evidence
import Uwueave.Wellformed
import Uwueave.Exits
import Uwueave.CoordEffect
import Uwueave.SeamColoring
import Uwueave.Budget
import Uwueave.WorldFuture
import Uwueave.Temporal
import Uwueave.MinimalSummary
import Uwueave.ContextCompiler
import Uwueave.FiniteSummaryCodec
import Uwueave.Repair
import Uwueave.MergeModel
import Uwueave.ResultStatus
import Uwueave.StatusEffects
import Uwueave.Recoverable
import Uwueave.CompositeDelta
import Uwueave.HonestRender
import Uwueave.Histories
import Uwueave.FiniteHistory
import Uwueave.HistoryEngine
import Uwueave.HistoryRuntime
import Uwueave.FiniteHistoryGrowth
import Uwueave.ResolvedHistoryGrowth
import Uwueave.TextSummary
import Uwueave.LiveBudget
import Uwueave.EraCertificate
import Uwueave.CliqueLive
import Uwueave.ClashGraph
import Uwueave.RepairMenu
import Uwueave.HistoryPolicy
import Uwueave.LiveCost
import Uwueave.CertificateScope
import Uwueave.LiveSegmented
import Uwueave.ForkGrade
import Uwueave.RenderProgress
import Uwueave.HistoryBase
import Uwueave.RenderSix
import Uwueave.WovenEdit
import Uwueave.Bounds
import Uwueave.MenuTotality
import Uwueave.Preo.Demo
import Uwueave.ChoreoChoice
import Uwueave.Scheduling
import Uwueave.ScheduleSynthesis
import Uwueave.Protocol
import Uwueave.ChoreoRec
import Uwueave.Specification
import Uwueave.Frontier
import Uwueave.WorldContext
import Uwueave.Authenticity
import Uwueave.Byzantine
import Uwueave.AuthenticatedAdmission
import Uwueave.AuthenticatedFrontier
import Uwueave.AuthenticatedWorldContext
import Uwueave.AuthenticatedEraCertificate
import Uwueave.Durable
import Uwueave.PersistentRuntime
import Uwueave.PersistentHistoryRuntime
import Uwueave.FiniteHistoryDelivery
import Uwueave.FiniteHistoryProtocol
import Uwueave.EvidenceGraph
import Uwueave.Preo.Future
import Uwueave.Preo.ArtifactData
import Uwueave.Preo.ArtifactChecked
import Uwueave.Preo.ArtifactDiagnostics
import Uwueave.Preo.Artifact
import Uwueave.Preo.Export
import Uwueave.Preo.Expr
import Uwueave.Preo.Incremental
import Uwueave.Preo.ResultProgram
import Uwueave.Preo.StateProgram
import Uwueave.Preo.BoundResult
import Uwueave.Preo.ObservedBoundResult
import Uwueave.Preo.DerivedProgram
import Uwueave.Preo.StateProgramSurface
import Uwueave.Preo.StateProgramSurfaceTests
import Uwueave.Preo.ProtocolSurface
import Uwueave.Preo.Planning
import Uwueave.Preo.PlanningSurface
import Uwueave.Preo.ArtifactDurableCore
import Uwueave.Preo.ArtifactDurable
import Uwueave.Preo.ArtifactJournalKernel
import Uwueave.Preo.ArtifactJournalDiagnostics
import Uwueave.Preo.ProjectionV1
import Uwueave.Preo.ProjectionV1Core
import Uwueave.Preo.ProjectionV1Diagnostics
import Uwueave.Preo.ProjectionV1Examples
import Uwueave.Preo.ProjectionV1Fixtures
import Uwueave.Preo.ProjectionV2
import Uwueave.Preo.ProjectionV2Core
import Uwueave.Preo.ProjectionV2Diagnostics
import Uwueave.Preo.ProjectionV2Examples
import Uwueave.Preo.ProjectionV2Fixtures
import Uwueave.Preo.ArtifactV3Data
import Uwueave.Preo.ArtifactV3Diagnostics
import Uwueave.Preo.ArtifactV3Durable
import Uwueave.Preo.ArtifactV3Fixtures
import Uwueave.Preo.ArtifactV3Checked
import Uwueave.Preo.ArtifactV3Surface
import Uwueave.Preo.ProjectionV3Core
import Uwueave.Preo.ProjectionV3
import Uwueave.Preo.ProjectionV3Diagnostics
import Uwueave.Preo.ProjectionV3Examples
import Uwueave.Preo.ProjectionV3Fixtures
import Uwueave.Preo.ArtifactV3Examples
import Uwueave.Preo.ArtifactInspectionV1
import Uwueave.Preo.ArtifactEmit
import Uwueave.Preo.Quickstart
import Uwueave.StatusSemanticsAcceptance
import Uwueave.RepairSynthesis
import Uwueave.FiniteRepairMenu
import Uwueave.FiniteProductSearch
import Uwueave.FiniteProductClosure
import Uwueave.FiniteCertificateClassifier
import Uwueave.BoundedEraAnnouncement
import Uwueave.RuntimeAuthV4
import Uwueave.RuntimeAuthV4Kernel
import Uwueave.Preo.RuntimeAuthV4Data
import Uwueave.Preo.RuntimeAuthV4Checked
import Uwueave.Preo.RuntimeAuthV4Durable
import Uwueave.Preo.RuntimeAuthV4ProjectionCore
import Uwueave.Preo.RuntimeAuthV4Projection
import Uwueave.Preo.RuntimeAuthV4Examples
import Uwueave.Preo.RuntimeAuthV4Fixtures
import Uwueave.RuntimeInit
import Uwueave.Tactics.Verdict
import Uwueave.Tactics

open Lean Elab Command in
/-- Fail if any library module on disk is absent from this aggregate's imported
environment.  The only exceptions are the two executable entry modules which
both declare root `main` and therefore cannot coexist.  Their exact direct
Uwueave dependencies must still be loaded here.  Each executable invokes its
own EOF-enforced current-module audit; subprocess canaries additionally audit
the serialized modules through Lean's declaration-ownership table. -/
elab "#gate_covers_disk" : command => do
  let env ← getEnv
  let disk ← liftIO <| Uwueave.TrustFloor.leanModulesUnder "Uwueave"
  let loaded := env.mainModule :: env.header.moduleNames.toList
  let exceptions : List (Name × System.FilePath) :=
    [(`Uwueave.Preo.ArtifactEmitMain, "Uwueave/Preo/ArtifactEmitMain.lean"),
     (`Uwueave.Preo.ArtifactInspectionMain,
       "Uwueave/Preo/ArtifactInspectionMain.lean")]
  let exceptionNames := exceptions.map Prod.fst
  if let some failure :=
      Uwueave.TrustFloor.moduleCoverageFailure? disk loaded exceptionNames then
    throwError failure
  for (moduleName, path) in exceptions do
    let pathModule ← liftIO <| Uwueave.TrustFloor.moduleNameOfLeanPath path
    unless pathModule == moduleName do
      throwError "disk-coverage exception path `{path}` maps to `{pathModule}`, not allowlisted module `{moduleName}`"
    let imports ← liftIO <| Uwueave.TrustFloor.directImports path
    let missingDependencies := imports.toList.filterMap fun dependency =>
      if (`Uwueave).isPrefixOf dependency.module &&
          !(loaded.contains dependency.module) then
        some dependency.module
      else
        none
    unless missingDependencies.isEmpty do
      throwError "disk-coverage exception `{moduleName}` imports local module(s) {missingDependencies} which the aggregate audit does not load"
  if disk.length < 20 then
    throwError "disk-coverage tripwire: found only {disk.length} Lean modules under `Uwueave/`"
  logInfo m!"#gate_covers_disk: {disk.length} nested disk modules under `Uwueave/`; {disk.length - exceptionNames.length} loaded by the aggregate and {exceptionNames.length} separately self-audited executable exceptions; root aggregate `Uwueave.lean` is outside this nested census and self-audits at EOF"

open Lean Elab Command in
/-- Fail the build if any module the ROOT (`Uwueave.lean`) imports is absent
from this file's environment — i.e. if the gate's walk does not cover the
library. `#audit_floor` can only see constants from modules it has imported, so
a module in the root and not here is silently unaudited. The root cannot be
imported (it imports this file), so coverage is checked against the source
header with Lean's own parser rather than inherited or approximated by a line
scanner. Found by `docs/COHERENCE.md`: `Choreo` sat in the root and outside the
gate for a full wave, beneath four "total by construction" claims, and a
hand-maintained import list reproduces that gap once per wave. -/
elab "#gate_covers_root" : command => do
  let env ← getEnv
  let imports ← liftIO <| Uwueave.TrustFloor.directImports "Uwueave.lean"
  let wanted := imports.toList.filterMap fun imp =>
    if (`Uwueave).isPrefixOf imp.module && imp.module != `Uwueave.Audit then
      some imp.module
    else
      none
  let loaded := env.header.moduleNames.toList
  let missing := wanted.filter fun m => !(loaded.contains m)
  unless missing.isEmpty do
    throwError "gate coverage hole: the root imports {missing} which this file does not \
      reach, so #audit_floor cannot see their constants. Add the import(s) here."
  if wanted.length < 20 then
    throwError "gate-coverage tripwire: Lean parsed only {wanted.length} Uwueave root imports"
  logInfo m!"#gate_covers_root: {wanted.length} root modules, all reached by the gate"

#gate_covers_disk

#gate_covers_root

#audit_floor_modules Uwueave

#audit_floor

#audit_floor_current
