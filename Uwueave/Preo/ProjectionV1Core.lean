/-
# Uwueave.Preo.ProjectionV1Core — data-only V1 validation

This leaf owns the V1 schema, untrusted input types, precise validation errors,
private validated boundary, and fail-closed validator. It imports only neutral
`ArtifactData`; V1 rendering lives in `ProjectionV1`. Derived `Repr`, checked
examples, and exact source fixtures are separate opt-in modules, so importing
this core does not inherit `ArtifactDiagnostics`, proof-indexed `Export`, or
the fixture proof terms and elevated recursion settings.
-/
import Uwueave.Preo.ArtifactData

namespace Uwueave.Preo.ProjectionV1

open Uwueave.Preo.Artifact

set_option autoImplicit false

/-! ## Versioned untrusted input and explicit resource policy -/

/-- The exact schema identifier for this typed projection. -/
def schema : String := "uwueave/preo-projection/v1"

/-- Untrusted, neutral input to the V1 validator. -/
structure Projection where
  schema : String
  encoding : ArtifactEncoding
  deriving DecidableEq

/-- Construct a correctly tagged input from a first-order artifact encoding. -/
def Projection.ofEncoding (encoding : ArtifactEncoding) : Projection :=
  ⟨Uwueave.Preo.ProjectionV1.schema, encoding⟩

/-- Every variable-length collection checked before a host receives a
validated projection. -/
structure ValidationBounds where
  maxFields : Nat
  maxInvariants : Nat
  maxFutures : Nat
  maxSessions : Nat
  maxPlans : Nat
  maxObligationsPerSession : Nat
  maxActionsPerPlan : Nat
  maxProfileEntriesPerPlan : Nat
  maxParticipantsPerDemand : Nat
  maxWitnessWords : Nat
  deriving DecidableEq

structure ValidationConfig where
  bounds : ValidationBounds
  deriving DecidableEq

inductive StableIdKind where
  | field
  | invariant
  | future
  | session
  | plan
  deriving DecidableEq

inductive DeclarationRowKind where
  | field
  | invariant
  | future
  | session
  deriving DecidableEq

inductive WitnessSide where
  | left
  | right
  deriving DecidableEq

inductive DemandLocation where
  | sessionObligation (sessionId obligationIndex : Nat)
  | planAction (planId actionIndex : Nat)
  deriving DecidableEq

/-- A precise name for every bounded list in the typed projection. -/
inductive BoundedList where
  | fields
  | invariants
  | futures
  | sessions
  | plans
  | sessionObligations (sessionId : Nat)
  | planActions (planId : Nat)
  | planProfile (planId : Nat)
  | demandParticipants (location : DemandLocation)
  | clashWitness (invariantId : Nat) (side : WitnessSide)
  deriving DecidableEq

/-- Fail-closed validation failures. -/
inductive ValidationError where
  | wrongSchema (expected found : String)
  | listTooLarge (list : BoundedList) (actual limit : Nat)
  | duplicateStableId (kind : StableIdKind) (id : Nat)
  | wrongDeclarationReference (kind : DeclarationRowKind) (rowId expected found : Nat)
  | danglingPlanSession (planId sessionId : Nat)
  | crossingIndexOutOfRange
      (sessionId obligationIndex crossingIndex crossings : Nat)
  | nonCanonicalPlanProfile (planId : Nat) (found : List Currency)
  | budgetsNotSupported (actual : Nat)
  deriving DecidableEq

abbrev ValidationResult (alpha : Type) := Except ValidationError alpha

/-! ## The private validated boundary -/

/-- A validated projection is constructible only by this module's successful
validator.  It remains first-order inspection data, not authority. -/
structure ValidatedProjectionV1 where private mk ::
  projection : Projection
  config : ValidationConfig
  deriving DecidableEq

def ValidatedProjectionV1.schema (validated : ValidatedProjectionV1) : String :=
  validated.projection.schema

def ValidatedProjectionV1.encoding
    (validated : ValidatedProjectionV1) : ArtifactEncoding :=
  validated.projection.encoding

def ValidatedProjectionV1.validationConfig
    (validated : ValidatedProjectionV1) : ValidationConfig :=
  validated.config

/-! ## Deterministic fail-closed validation -/

private def firstDuplicate? : List Nat → Option Nat
  | [] => none
  | id :: ids =>
      if ids.contains id then some id else firstDuplicate? ids

private def checkBound (list : BoundedList) (actual limit : Nat) :
    ValidationResult Unit :=
  if actual ≤ limit then
    pure ()
  else
    throw (.listTooLarge list actual limit)

private def checkUnique (kind : StableIdKind) (ids : List Nat) :
    ValidationResult Unit :=
  match firstDuplicate? ids with
  | none => pure ()
  | some id => throw (.duplicateStableId kind id)

private def checkDeclarationReference (kind : DeclarationRowKind)
    (rowId expected found : Nat) : ValidationResult Unit :=
  if found = expected then
    pure ()
  else
    throw (.wrongDeclarationReference kind rowId expected found)

private def checkDemand (bounds : ValidationBounds) (location : DemandLocation)
    (demand : DemandArtifact) : ValidationResult Unit :=
  checkBound (.demandParticipants location) demand.participants.length
    bounds.maxParticipantsPerDemand

private def canonicalProfileCurrencies : List Currency :=
  [.peerBarrier, .arbiterCut, .networkRound, .userPrompt, .rollback]

private def checkInvariant (bounds : ValidationBounds)
    (invariant : InvariantArtifactEncoding) : ValidationResult Unit := do
  match invariant.verdict with
  | .free => pure ()
  | .clash left right =>
      checkBound (.clashWitness invariant.id .left) left.length bounds.maxWitnessWords
      checkBound (.clashWitness invariant.id .right) right.length bounds.maxWitnessWords

private def checkSession (bounds : ValidationBounds)
    (session : SessionArtifactEncoding) : ValidationResult Unit := do
  checkBound (.sessionObligations session.id) session.obligations.length
    bounds.maxObligationsPerSession
  for (obligation, obligationIndex) in session.obligations.zipIdx do
    checkDemand bounds (.sessionObligation session.id obligationIndex) obligation.demand
    match obligation.origin with
    | .ambient => pure ()
    | .crossing crossingIndex =>
        if crossingIndex < session.crossings then
          pure ()
        else
          throw (.crossingIndexOutOfRange session.id obligationIndex crossingIndex
            session.crossings)

private def checkPlan (bounds : ValidationBounds) (sessionIds : List Nat)
    (plan : PlanArtifactEncoding) : ValidationResult Unit := do
  if sessionIds.contains plan.sessionId then
    pure ()
  else
    throw (.danglingPlanSession plan.id plan.sessionId)
  checkBound (.planActions plan.id) plan.actions.length bounds.maxActionsPerPlan
  checkBound (.planProfile plan.id) plan.profile.length bounds.maxProfileEntriesPerPlan
  let currencies := plan.profile.map Prod.fst
  if currencies = canonicalProfileCurrencies then
    pure ()
  else
    throw (.nonCanonicalPlanProfile plan.id currencies)
  for (action, actionIndex) in plan.actions.zipIdx do
    checkDemand bounds (.planAction plan.id actionIndex) action

/-- Validate one V1 host projection.  Success is structural acceptance only;
it does not reconstruct checked semantic evidence. -/
def validate (config : ValidationConfig) (projection : Projection) :
    ValidationResult ValidatedProjectionV1 := do
  if projection.schema = schema then
    pure ()
  else
    throw (.wrongSchema schema projection.schema)

  let encoding := projection.encoding
  if encoding.budgets.isEmpty then
    pure ()
  else
    throw (.budgetsNotSupported encoding.budgets.length)
  let bounds := config.bounds
  checkBound .fields encoding.fields.length bounds.maxFields
  checkBound .invariants encoding.invariants.length bounds.maxInvariants
  checkBound .futures encoding.futures.length bounds.maxFutures
  checkBound .sessions encoding.sessions.length bounds.maxSessions
  checkBound .plans encoding.plans.length bounds.maxPlans

  checkUnique .field (encoding.fields.map FieldArtifactEncoding.id)
  checkUnique .invariant (encoding.invariants.map InvariantArtifactEncoding.id)
  checkUnique .future (encoding.futures.map FutureArtifactEncoding.id)
  checkUnique .session (encoding.sessions.map SessionArtifactEncoding.id)
  checkUnique .plan (encoding.plans.map PlanArtifactEncoding.id)

  let declarationId := encoding.declaration.id
  for field in encoding.fields do
    checkDeclarationReference .field field.id declarationId field.declarationId
  for invariant in encoding.invariants do
    checkDeclarationReference .invariant invariant.id declarationId invariant.declarationId
    checkInvariant bounds invariant
  for future in encoding.futures do
    checkDeclarationReference .future future.id declarationId future.declarationId
  for session in encoding.sessions do
    checkDeclarationReference .session session.id declarationId session.declarationId
    checkSession bounds session

  let sessionIds := encoding.sessions.map SessionArtifactEncoding.id
  for plan in encoding.plans do
    checkPlan bounds sessionIds plan

  pure ⟨projection, config⟩

end Uwueave.Preo.ProjectionV1
