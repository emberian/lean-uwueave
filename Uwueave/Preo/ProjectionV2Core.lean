/-
# Uwueave.Preo.ProjectionV2Core — data-only V2 validation

V2 is the first host projection which admits the five-currency budget rows
exported from checked `ProfileUpperBound` witnesses.  The boundary remains
one-way and data-only: validation establishes structural consistency and
finite host bounds, but does not reconstruct a `Scheduling.Plan`, proof,
verdict, permit, or authority token.

The data-only V1 core is reused on a budget-cleared view for its declaration,
reference, crossing, and resource checks.  V2 then checks the properties which
V1 intentionally does not express: exact action histograms, first-order
schedule coverage, and budget identity/reference/profile/limit consistency.

This module performs no rendering and imports no diagnostics or examples.
`ProjectionV2` renders every `Nat` as decimal text, so the generated Rust
contract never narrows Lean naturals to machine integers. Optional `Repr`,
proof-indexed examples, and exact strings live in the corresponding
Diagnostics, Examples, and Fixtures modules.
-/
import Uwueave.Preo.ProjectionV1Core

namespace Uwueave.Preo.ProjectionV2

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

/-! ## §1. Versioned input and explicit bounds -/

def schema : String := "uwueave/preo-projection/v2"

structure Projection where
  schema : String
  encoding : ArtifactEncoding
  deriving DecidableEq

def Projection.ofEncoding (encoding : ArtifactEncoding) : Projection :=
  ⟨Uwueave.Preo.ProjectionV2.schema, encoding⟩

/-- V2 retains every V1 bound and adds explicit budget/profile bounds. -/
structure ValidationBounds where
  maxFields : Nat
  maxInvariants : Nat
  maxFutures : Nat
  maxSessions : Nat
  maxPlans : Nat
  maxBudgets : Nat
  maxObligationsPerSession : Nat
  maxActionsPerPlan : Nat
  maxProfileEntriesPerPlan : Nat
  maxProfileEntriesPerBudget : Nat
  maxParticipantsPerDemand : Nat
  maxWitnessWords : Nat
  deriving DecidableEq

structure ValidationConfig where
  bounds : ValidationBounds
  deriving DecidableEq

private def ValidationConfig.toV1 (config : ValidationConfig) :
    ProjectionV1.ValidationConfig where
  bounds := ({
    maxFields := config.bounds.maxFields
    maxInvariants := config.bounds.maxInvariants
    maxFutures := config.bounds.maxFutures
    maxSessions := config.bounds.maxSessions
    maxPlans := config.bounds.maxPlans
    maxObligationsPerSession := config.bounds.maxObligationsPerSession
    maxActionsPerPlan := config.bounds.maxActionsPerPlan
    maxProfileEntriesPerPlan := config.bounds.maxProfileEntriesPerPlan
    maxParticipantsPerDemand := config.bounds.maxParticipantsPerDemand
    maxWitnessWords := config.bounds.maxWitnessWords } : ProjectionV1.ValidationBounds)

inductive BudgetBoundedList where
  | budgets
  | limits (budgetId : Nat)
  | realizedProfile (budgetId : Nat)
  deriving DecidableEq

inductive ValidationError where
  | wrongSchema (expected found : String)
  | base (error : ProjectionV1.ValidationError)
  | budgetListTooLarge (list : BudgetBoundedList) (actual limit : Nat)
  | duplicateBudgetId (id : Nat)
  | danglingBudgetSession (budgetId sessionId : Nat)
  | danglingBudgetPlan (budgetId planId : Nat)
  | budgetPlanSessionMismatch (budgetId budgetSessionId planSessionId : Nat)
  | nonCanonicalPlanProfile (planId : Nat) (found : List Currency)
  | planProfileMismatch (planId : Nat)
      (declared computed : List (Currency × Nat))
  | uncoveredObligation (planId sessionId obligationIndex : Nat)
  | nonCanonicalBudgetLimits (budgetId : Nat) (found : List Currency)
  | nonCanonicalBudgetProfile (budgetId : Nat) (found : List Currency)
  | budgetProfileMismatch (budgetId planId : Nat)
  | budgetLimitExceeded (budgetId : Nat) (currency : Currency)
      (realized limit : Nat)
  deriving DecidableEq

abbrev ValidationResult (alpha : Type) := Except ValidationError alpha

/-! ## §2. Private validated boundary -/

structure ValidatedProjectionV2 where private mk ::
  projection : Projection
  config : ValidationConfig
  deriving DecidableEq

def ValidatedProjectionV2.schema (validated : ValidatedProjectionV2) : String :=
  validated.projection.schema

def ValidatedProjectionV2.encoding
    (validated : ValidatedProjectionV2) : ArtifactEncoding :=
  validated.projection.encoding

def ValidatedProjectionV2.validationConfig
    (validated : ValidatedProjectionV2) : ValidationConfig :=
  validated.config

/-! ## §3. Exact plan and budget validation -/

private def canonicalProfileCurrencies : List Currency :=
  [.peerBarrier, .arbiterCut, .networkRound, .userPrompt, .rollback]

private def firstDuplicate? : List Nat → Option Nat
  | [] => none
  | id :: ids => if ids.contains id then some id else firstDuplicate? ids

private def checkBudgetBound (list : BudgetBoundedList) (actual limit : Nat) :
    ValidationResult Unit :=
  if actual ≤ limit then pure ()
  else throw (.budgetListTooLarge list actual limit)

private def actionCount (currency : Currency) (actions : List DemandArtifact) : Nat :=
  (actions.filter fun action => action.currency == currency).length

/-- The exact histogram implied by the first-order action list. -/
private def actionProfile (actions : List DemandArtifact) : List (Currency × Nat) :=
  [(.peerBarrier, actionCount .peerBarrier actions),
   (.arbiterCut, actionCount .arbiterCut actions),
   (.networkRound, actionCount .networkRound actions),
   (.userPrompt, actionCount .userPrompt actions),
   (.rollback, actionCount .rollback actions)]

private def checkPlan (sessions : List SessionArtifactEncoding)
    (plan : PlanArtifactEncoding) : ValidationResult Unit := do
  let currencies := plan.profile.map Prod.fst
  if currencies = canonicalProfileCurrencies then pure ()
  else throw (.nonCanonicalPlanProfile plan.id currencies)
  let computed := actionProfile plan.actions
  if plan.profile = computed then pure ()
  else throw (.planProfileMismatch plan.id plan.profile computed)
  let session ← match sessions.find? (fun session => session.id == plan.sessionId) with
    | some session => pure session
    | none => throw (.base (.danglingPlanSession plan.id plan.sessionId))
  for (obligation, obligationIndex) in session.obligations.zipIdx do
    if plan.actions.contains obligation.demand then pure ()
    else throw (.uncoveredObligation plan.id session.id obligationIndex)

private def checkBudgetFits (budgetId : Nat) :
    List (Currency × Nat) → List (Currency × Nat) → ValidationResult Unit
  | [], [] => pure ()
  | (currency, realized) :: realizedRest, (_, limit) :: limitRest => do
      if realized ≤ limit then
        checkBudgetFits budgetId realizedRest limitRest
      else
        throw (.budgetLimitExceeded budgetId currency realized limit)
  | _, _ => pure () -- canonical shape checks run before this helper

private def checkBudget (bounds : ValidationBounds)
    (sessions : List SessionArtifactEncoding) (plans : List PlanArtifactEncoding)
    (budget : BudgetArtifactEncoding) : ValidationResult Unit := do
  if sessions.any (fun session => session.id == budget.sessionId) then pure ()
  else throw (.danglingBudgetSession budget.id budget.sessionId)
  let plan ← match plans.find? (fun plan => plan.id == budget.planId) with
    | some plan => pure plan
    | none => throw (.danglingBudgetPlan budget.id budget.planId)
  if plan.sessionId = budget.sessionId then pure ()
  else throw (.budgetPlanSessionMismatch budget.id budget.sessionId plan.sessionId)
  checkBudgetBound (.limits budget.id) budget.limits.length
    bounds.maxProfileEntriesPerBudget
  checkBudgetBound (.realizedProfile budget.id) budget.realizedProfile.length
    bounds.maxProfileEntriesPerBudget
  let limitCurrencies := budget.limits.map Prod.fst
  if limitCurrencies = canonicalProfileCurrencies then pure ()
  else throw (.nonCanonicalBudgetLimits budget.id limitCurrencies)
  let profileCurrencies := budget.realizedProfile.map Prod.fst
  if profileCurrencies = canonicalProfileCurrencies then pure ()
  else throw (.nonCanonicalBudgetProfile budget.id profileCurrencies)
  if budget.realizedProfile = plan.profile then pure ()
  else throw (.budgetProfileMismatch budget.id plan.id)
  checkBudgetFits budget.id budget.realizedProfile budget.limits

/-- Validate V2 by first applying V1 to the budget-cleared base, then checking
the new exact-plan and budget-bearing contract.  A successful value remains
first-order data and is constructible only along this path. -/
def validate (config : ValidationConfig) (projection : Projection) :
    ValidationResult ValidatedProjectionV2 := do
  if projection.schema = schema then pure ()
  else throw (.wrongSchema schema projection.schema)

  let encoding := projection.encoding
  let baseProjection : ProjectionV1.Projection := {
    schema := ProjectionV1.schema
    encoding := { encoding with budgets := [] } }
  match ProjectionV1.validate config.toV1 baseProjection with
  | .ok _ => pure ()
  | .error error => throw (.base error)

  for plan in encoding.plans do
    checkPlan encoding.sessions plan

  checkBudgetBound .budgets encoding.budgets.length config.bounds.maxBudgets
  match firstDuplicate? (encoding.budgets.map BudgetArtifactEncoding.id) with
  | some id => throw (.duplicateBudgetId id)
  | none => pure ()
  for budget in encoding.budgets do
    checkBudget config.bounds encoding.sessions encoding.plans budget

  pure ⟨projection, config⟩

/-! ## §4. Deterministic V2 Rust source -/
