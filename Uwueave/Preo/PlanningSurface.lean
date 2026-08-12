/-
# Uwueave.Preo.PlanningSurface — checked finite planning command

`preo_plan` is a deliberately thin surface over `Planning.synthesize`.  It
checks an authored action universe before exposing it, fixes the problem to one
named protocol session, and always emits the proof-carrying `Planning.Result`.
A refusal stops there: its exhaustive theorem remains inside `Result.refused`.
A selected form additionally requires an explicit proof that the computed
result selected, then exposes the exact schedule and all five of its currencies,
the selected repair and all eight axes of its `Repair.Price`, and the problem's
coupling proof.

No coordinate is scalarized or converted.  In particular, a schedule limit is
never reconstructed from a repair price or crossing count.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Preo.Planning

namespace Uwueave.Preo.PlanningSurface

open Lean Elab Command
open Uwueave
open Uwueave.Preo.Elab.Internal

/-! ## Checked extractors -/

/-- Recover the accepted scope from the executable universe check.  The proof
rules out both evidence-bearing refusal constructors. -/
def acceptedUniverse {actions : List Scheduling.Demand} {maxChoices : Nat}
    (check : Planning.ActionUniverseCheck actions maxChoices)
    (accepted : check.isAccepted = true) : Planning.ActionUniverse :=
  match check with
  | .accepted scope _ _ => scope
  | .duplicate _ => by cases accepted
  | .tooLarge _ => by cases accepted

/-- Recover the dependent selected witness from the exact Boolean observation
required by the surface. -/
def selectedOf {promise : Repair.Promise} {problem : Planning.Problem promise}
    (result : Planning.Result problem) (selected : result.isSelected = true) :
    Planning.Selected problem :=
  match result with
  | .selected witness => witness
  | .refused _ => by cases selected

/-! ## Parser-hard surface -/

declare_syntax_cat preoPlanMode
syntax (name := preoPlanResultMode) "result" : preoPlanMode
syntax (name := preoPlanSelectedMode) "selected" ppSpace "by" ppSpace
  term : preoPlanMode

/-- Run one finite planning problem against an explicitly bounded action
universe. Braces, commas, and `:=` terminate every arbitrary Lean term. -/
syntax (name := preoPlan) "preo_plan " ident ppSpace &"for" ppSpace ident
  ppSpace &"over" ppSpace term:51 ppSpace ":=" ppSpace "{"
  ppLine colGe (&"actions" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"maxChoices" ppSpace ":=" ppSpace term:51 ",")
  ppLine colGe (&"problem" ppSpace ":=" ppSpace term)
  ppLine colGe ("}" ppSpace preoPlanMode) : command

private def suffix (base : Ident) (tail : Name) : Ident :=
  mkIdent (base.getId ++ tail)

private def emitUniverseRefusalChecks (name actions : Ident)
    (check : Ident) : CommandElabM Unit := do
  let duplicateProbe ← `(command|
    example : ($check).refusalKind? =
        some Uwueave.Preo.Planning.ActionUniverseCheck.RefusalKind.duplicate :=
      by decide)
  if (← probeCommand duplicateProbe).isOk then
    throwErrorAt actions "preo_plan: `{name.getId}` action universe contains \
      duplicate demand identities. Duplicate actions add no scheduling power \
      but duplicate generated choices; remove them before planning."
  let tooLargeProbe ← `(command|
    example : ($check).refusalKind? =
        some Uwueave.Preo.Planning.ActionUniverseCheck.RefusalKind.tooLarge :=
      by decide)
  if (← probeCommand tooLargeProbe).isOk then
    throwErrorAt actions "preo_plan: `{name.getId}` action universe exceeds \
      `maxChoices`; the command refuses before materializing its exponential \
      action-choice list. Raise the explicit cap or reduce the authored scope."

private def emitSelected (name : Ident) (promise : Term) (proof : Term) :
    CommandElabM Unit := do
  let resultId := suffix name `Result
  let problemId := suffix name `Problem
  let selectedProofId := suffix name `isSelected
  let selectedId := suffix name `Selected
  let limitsId := suffix name `Limits
  let planId := suffix name `Plan
  let boundId := suffix name `ProfileUpperBound
  let planExactId := suffix name `plan_exact
  let peerId := suffix name `PeerBarrierLimit
  let arbiterId := suffix name `ArbiterCutLimit
  let roundId := suffix name `NetworkRoundLimit
  let promptId := suffix name `UserPromptLimit
  let rollbackId := suffix name `RollbackLimit
  let candidateId := suffix name `RepairCandidate
  let repairId := suffix name `RepairId
  let priceId := suffix name `RepairPrice
  let seamCrossingsId := suffix name `RepairSeamCrossings
  let repairArbiterId := suffix name `RepairArbiterCuts
  let rollbackWindowId := suffix name `RepairRollbackWindow
  let writesId := suffix name `RepairResolutionWrites
  let evidenceId := suffix name `RepairRetainsEvidence
  let pluralId := suffix name `RepairPluralRead
  let restrictsId := suffix name `RepairRestrictsReachability
  let assumptionsId := suffix name `RepairAssumptions
  let couplingId := suffix name `Coupled
  let refusedProbe ← `(command|
    example : Uwueave.Preo.Planning.Result.isSelected $resultId = false := by decide)
  if (← probeCommand refusedProbe).isOk then
    throwErrorAt proof "preo_plan: `{name.getId}` was declared `selected`, \
      but the exact generated result is a refusal. No selected projections \
      were emitted."
  let selectedCommand ← `(command|
    /-- Kernel-checked evidence that this exact computed result selected. -/
    theorem $selectedProofId : ($resultId).isSelected = true := $proof)
  emitRequired selectedCommand
  floorCheck proof "planning selection proof" ((← getCurrNamespace) ++ selectedProofId.getId)
  emitRequired (← `(command|
    /-- The dependent selected witness recovered from `Result`. -/
    def $selectedId : Uwueave.Preo.Planning.Selected $problemId :=
      Uwueave.Preo.PlanningSurface.selectedOf $resultId $selectedProofId))
  emitRequired (← `(command|
    /-- The problem's five independent schedule limits. -/
    abbrev $limitsId : Uwueave.Scheduling.Currency → Nat := ($problemId).limits))
  emitRequired (← `(command|
    /-- The exact selected schedule plan. -/
    def $planId : Uwueave.Scheduling.Plan ($problemId).session :=
      ($selectedId).schedule.plan))
  emitRequired (← `(command|
    /-- The selected plan's proof that all five coordinates fit together. -/
    def $boundId : Uwueave.Scheduling.ProfileUpperBound
        ($problemId).session $limitsId := ($selectedId).schedule))
  emitRequired (← `(command|
    theorem $planExactId : ($boundId).plan = $planId := rfl))
  emitRequired (← `(command| abbrev $peerId : Nat := $limitsId .peerBarrier))
  emitRequired (← `(command| abbrev $arbiterId : Nat := $limitsId .arbiterCut))
  emitRequired (← `(command| abbrev $roundId : Nat := $limitsId .networkRound))
  emitRequired (← `(command| abbrev $promptId : Nat := $limitsId .userPrompt))
  emitRequired (← `(command| abbrev $rollbackId : Nat := $limitsId .rollback))
  emitRequired (← `(command|
    /-- The exact selected repair candidate, including its dependent target. -/
    def $candidateId : Uwueave.RepairSynthesis.Candidate $promise :=
      ($selectedId).repair.candidate))
  emitRequired (← `(command|
    /-- Stable identity of the selected repair candidate. -/
    def $repairId : Uwueave.RepairSynthesis.CandidateId := ($candidateId).id))
  emitRequired (← `(command|
    /-- The complete, non-scalarized eight-axis repair price. -/
    def $priceId : Uwueave.Repair.Price := ($candidateId).price))
  emitRequired (← `(command| abbrev $seamCrossingsId : Nat := ($priceId).seamCrossings))
  emitRequired (← `(command| abbrev $repairArbiterId : Nat := ($priceId).arbiterCuts))
  emitRequired (← `(command| abbrev $rollbackWindowId : Nat := ($priceId).rollbackWindow))
  emitRequired (← `(command| abbrev $writesId : Nat := ($priceId).resolutionWrites))
  emitRequired (← `(command| abbrev $evidenceId : Bool := ($priceId).retainsEvidence))
  emitRequired (← `(command| abbrev $pluralId : Bool := ($priceId).pluralRead))
  emitRequired (← `(command| abbrev $restrictsId : Bool := ($priceId).restrictsReachability))
  emitRequired (← `(command|
    abbrev $assumptionsId : List Uwueave.Repair.Premise := ($priceId).assumptions))
  emitRequired (← `(command|
    /-- The application-specific relation tying this exact plan and repair. -/
    theorem $couplingId :
        ($problemId).compatible $planId $candidateId := ($selectedId).coupled))
  floorCheck name "selected planning result" ((← getCurrNamespace) ++ selectedId.getId)
  floorCheck name "selected planning profile" ((← getCurrNamespace) ++ boundId.getId)
  floorCheck name "selected repair price" ((← getCurrNamespace) ++ priceId.getId)
  floorCheck name "planning coupling" ((← getCurrNamespace) ++ couplingId.getId)

@[command_elab preoPlan]
def elabPreoPlan : CommandElab := fun stx => withEnvTransaction do
  let `(command| preo_plan $name for $protocol over $promise := {
      actions := $actions,
      maxChoices := $maxChoices,
      problem := $problem
    } $mode:preoPlanMode) := stx
    | throwError "preo_plan: malformed declaration"
  let actionsId := suffix name `Actions
  let maxChoicesId := suffix name `MaxChoices
  let checkId := suffix name `ActionUniverseCheck
  let acceptedId := suffix name `ActionUniverseAccepted
  let universeId := suffix name `ActionUniverse
  let sessionId := suffix name `Session
  let problemId := suffix name `Problem
  let sessionExactId := suffix name `problem_session_exact
  let actionsExactId := suffix name `problem_actions_exact
  let maxChoicesExactId := suffix name `problem_maxChoices_exact
  let resultId := suffix name `Result
  emitRequired (← `(command|
    abbrev $actionsId : List Uwueave.Scheduling.Demand := $actions))
  emitRequired (← `(command| abbrev $maxChoicesId : Nat := $maxChoices))
  emitRequired (← `(command|
    def $checkId := Uwueave.Preo.Planning.checkActionUniverse
      $actionsId $maxChoicesId))
  emitUniverseRefusalChecks name actionsId checkId
  emitRequired (← `(command|
    theorem $acceptedId : ($checkId).isAccepted = true := by decide))
  emitRequired (← `(command|
    def $universeId : Uwueave.Preo.Planning.ActionUniverse :=
      Uwueave.Preo.PlanningSurface.acceptedUniverse $checkId $acceptedId))
  let protocolSessionId := mkIdent (protocol.getId ++ `Session)
  emitRequired (← `(command|
    abbrev $sessionId : Uwueave.Scheduling.Session := $protocolSessionId))
  emitRequired (← `(command|
    def $problemId : Uwueave.Preo.Planning.Problem $promise := $problem))
  emitRequired (← `(command|
    theorem $sessionExactId : ($problemId).session = $sessionId := rfl))
  emitRequired (← `(command|
    theorem $actionsExactId :
        ($problemId).actionUniverse.actions = $actionsId := rfl))
  emitRequired (← `(command|
    theorem $maxChoicesExactId :
        ($problemId).actionUniverse.maxChoices = $maxChoicesId := rfl))
  emitRequired (← `(command|
    /-- The total evidence-bearing result of both finite searches. -/
    def $resultId : Uwueave.Preo.Planning.Result $problemId :=
      Uwueave.Preo.Planning.synthesize $problemId))
  floorCheck name "finite planning result" ((← getCurrNamespace) ++ resultId.getId)
  if mode.raw.getKind == ``preoPlanResultMode then
      let refusedProbe ← `(command|
        example : Uwueave.Preo.Planning.Result.isSelected $resultId = false := by decide)
      match ← probeCommand refusedProbe with
      | .ok _ => pure ()
      | .error _ =>
          throwErrorAt mode "preo_plan: `{name.getId}` used result-only mode, \
            but the exact result selected. Write `selected by <proof>` to emit \
            its checked plan, five limits, repair price, and coupling."
  else if mode.raw.getKind == ``preoPlanSelectedMode then
    let `(preoPlanMode| selected by $proof) := mode
      | throwErrorAt mode "preo_plan: malformed `selected by` mode"
    emitSelected name promise proof
  else
    throwErrorAt mode "preo_plan: expected `result` or `selected by <proof>`"

/-! ## Executed acceptance and refusal fixtures -/

namespace NativeFixture

open Uwueave.Preo.Planning.Examples

preo_plan Selected for ProtocolSurface.NativeFixture over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := nativeSurfaceActions.actions,
  maxChoices := 8,
  problem := nativeSurfaceProblem
} selected by native_protocol_surface_is_plannable

/-- Whole-value acceptance: the command exposes the engine's exact dependent
selection rather than rebuilding either chosen witness. -/
theorem selected_is_engine_witness :
    Selected.Result = nativeSurfaceResult := rfl

theorem selected_profile_is_exact :
    Selected.ProfileUpperBound = Selected.Selected.schedule := rfl

theorem selected_plan_is_exact :
    Selected.Plan = Selected.Selected.schedule.plan := rfl

theorem selected_price_is_full :
    Selected.RepairPrice = Repair.restrictionPrice := by decide

theorem selected_limits_retain_five_currencies :
    Selected.PeerBarrierLimit = 2
      ∧ Selected.ArbiterCutLimit = 0
      ∧ Selected.NetworkRoundLimit = 1
      ∧ Selected.UserPromptLimit = 2
      ∧ Selected.RollbackLimit = 0 := by decide

theorem selected_price_retains_eight_axes :
    Selected.RepairSeamCrossings = 0
      ∧ Selected.RepairArbiterCuts = 0
      ∧ Selected.RepairRollbackWindow = 0
      ∧ Selected.RepairResolutionWrites = 0
      ∧ Selected.RepairRetainsEvidence = false
      ∧ Selected.RepairPluralRead = false
      ∧ Selected.RepairRestrictsReachability = true
      ∧ Selected.RepairAssumptions = [] := by decide

theorem selected_coupling_is_exact :
    Planning.SelectedPartitionCompatible ProtocolSurface.NativeFixture.Session
      ⟨202⟩ Selected.Plan Selected.RepairCandidate :=
  Selected.Coupled

/- The existing budget surface consumes the selected profile directly; no
second hand-written plan is introduced. -/
preo_budget SelectedBudget for ProtocolSurface.NativeFixture.Elaboration :
  Selected.Limits := Selected.ProfileUpperBound

theorem budget_is_selected_profile :
    SelectedBudget = Selected.ProfileUpperBound := rfl

preo_plan ScheduleRefused for ProtocolSurface.NativeCoalescing over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} result

theorem schedule_refusal_is_exact :
    Planning.Result.refusalKind? ScheduleRefused.Result =
      some Planning.Result.RefusalKind.schedule := by decide

preo_plan RepairRefused for ProtocolSurface.NativeCoalescing over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := repairRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := repairRefusalProblem
} result

theorem repair_refusal_is_exact :
    Planning.Result.refusalKind? RepairRefused.Result =
      some Planning.Result.RefusalKind.repair := by decide

/--
error: preo_plan: `Duplicate` action universe contains duplicate demand identities. Duplicate actions add no scheduling power but duplicate generated choices; remove them before planning.
-/
#guard_msgs in
preo_plan Duplicate for ProtocolSurface.NativeFixture over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := [Scheduling.sharedDemand, Scheduling.sharedDemand],
  maxChoices := 4,
  problem := nativeSurfaceProblem
} result

/--
error: preo_plan: `TooLarge` action universe exceeds `maxChoices`; the command refuses before materializing its exponential action-choice list. Raise the explicit cap or reduce the authored scope.
-/
#guard_msgs in
preo_plan TooLarge for ProtocolSurface.NativeFixture over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := nativeSurfaceActions.actions,
  maxChoices := 4,
  problem := nativeSurfaceProblem
} result

/--
error: preo_plan: `Reusable` was declared `selected`, but the exact generated result is a refusal. No selected projections were emitted.
-/
#guard_msgs in
preo_plan Reusable for ProtocolSurface.NativeCoalescing over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} selected by by decide

/- Identical-name reuse proves the failed transaction leaked no generated
constant. The successful retry intentionally emits only its refusal `Result`. -/
preo_plan Reusable for ProtocolSurface.NativeCoalescing over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} result

theorem rollback_reuse_is_exact :
    Planning.Result.refusalKind? Reusable.Result =
      some Planning.Result.RefusalKind.schedule := by decide

/- A wrong named protocol fails only after the bounded universe declarations
were attempted. The following same-name declaration proves transactionality. -/
/--
error: Unknown identifier `ProtocolSurface.DoesNotExist.Session`
-/
#guard_msgs in
preo_plan WrongName for ProtocolSurface.DoesNotExist over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} result

preo_plan WrongName for ProtocolSurface.NativeCoalescing over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} result

theorem wrong_name_rollback_reuse_is_exact :
    Planning.Result.refusalKind? WrongName.Result =
      some Planning.Result.RefusalKind.schedule := by decide

end NativeFixture
end Uwueave.Preo.PlanningSurface
