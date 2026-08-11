/-
# Uwueave.Preo.ProjectionV2 — budget-bearing neutral host projection

V2 is the first host projection which admits the five-currency budget rows
exported from checked `ProfileUpperBound` witnesses.  The boundary remains
one-way and data-only: validation establishes structural consistency and
finite host bounds, but does not reconstruct a `Scheduling.Plan`, proof,
verdict, permit, or authority token.

The V1 validator is reused on a budget-cleared view for its declaration,
reference, crossing, and resource checks.  V2 then checks the properties which
V1 intentionally does not express: exact action histograms, first-order
schedule coverage, and budget identity/reference/profile/limit consistency.
All `Nat` values render as decimal strings, so the generated Rust contract
never narrows Lean naturals to machine integers.
-/
import Uwueave.Preo.ProjectionV1

namespace Uwueave.Preo.ProjectionV2

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

/-! ## §1. Versioned input and explicit bounds -/

def schema : String := "uwueave/preo-projection/v2"

structure Projection where
  schema : String
  encoding : ArtifactEncoding
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

structure ValidationConfig where
  bounds : ValidationBounds
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

abbrev ValidationResult (alpha : Type) := Except ValidationError alpha

/-! ## §2. Private validated boundary -/

structure ValidatedProjectionV2 where private mk ::
  projection : Projection
  config : ValidationConfig
  deriving DecidableEq, Repr

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

private def rustUnicodeEscape (character : Char) : String :=
  "\\u{" ++ String.ofList (Nat.toDigits 16 character.toNat) ++ "}"

private def rustEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | character =>
      if 0x20 ≤ character.toNat then
        if character.toNat ≤ 0x7e then character.toString
        else rustUnicodeEscape character
      else rustUnicodeEscape character

private def rustStringLiteral (value : String) : String :=
  "\"" ++ String.intercalate "" (value.toList.map rustEscapeChar) ++ "\""

private def rustDecimal (value : Nat) : String :=
  rustStringLiteral (toString value)

private def rustSlice {alpha : Type} (render : alpha → String)
    (values : List alpha) : String :=
  "&[" ++ String.intercalate ", " (values.map render) ++ "]"

private def rustDecimalSlice (values : List Nat) : String :=
  rustSlice rustDecimal values

private def rustOptionalDecimal : Option Nat → String
  | none => "None"
  | some value => "Some(" ++ rustDecimal value ++ ")"

private def renderCurrency : Currency → String
  | .peerBarrier => "UwueavePreoCurrencyV2::PeerBarrier"
  | .arbiterCut => "UwueavePreoCurrencyV2::ArbiterCut"
  | .networkRound => "UwueavePreoCurrencyV2::NetworkRound"
  | .userPrompt => "UwueavePreoCurrencyV2::UserPrompt"
  | .rollback => "UwueavePreoCurrencyV2::Rollback"

private def renderEvidenceKey : EvidenceKey → String
  | .none => "UwueavePreoEvidenceKeyV2::None"
  | .named key => "UwueavePreoEvidenceKeyV2::Named(" ++ rustDecimal key ++ ")"

private def renderDemand (demand : DemandArtifact) : String :=
  "UwueavePreoDemandV2 { currency: " ++ renderCurrency demand.currency ++
    ", participants_decimal: " ++ rustDecimalSlice demand.participants ++
    ", scope_decimal: " ++ rustDecimal demand.scope ++
    ", epoch_decimal: " ++ rustDecimal demand.epoch ++
    ", evidence: " ++ renderEvidenceKey demand.evidence ++
    ", round_decimal: " ++ rustDecimal demand.round ++
    ", barrier_decimal: " ++ rustDecimal demand.barrier ++ " }"

private def renderOrigin : OriginArtifact → String
  | .ambient => "UwueavePreoOriginV2::Ambient"
  | .crossing index =>
      "UwueavePreoOriginV2::Crossing { index_decimal: " ++ rustDecimal index ++ " }"

private def renderObligation (obligation : ObligationArtifact) : String :=
  "UwueavePreoObligationV2 { origin: " ++ renderOrigin obligation.origin ++
    ", demand: " ++ renderDemand obligation.demand ++ " }"

private def renderDeclaration (declaration : DeclarationArtifactEncoding) : String :=
  "UwueavePreoDeclarationV2 { id_decimal: " ++ rustDecimal declaration.id ++
    ", state_type_id_decimal: " ++ rustDecimal declaration.stateTypeId ++
    ", schema_version_decimal: " ++ rustDecimal declaration.schemaVersion ++ " }"

private def renderField (field : FieldArtifactEncoding) : String :=
  "UwueavePreoFieldV2 { id_decimal: " ++ rustDecimal field.id ++
    ", declaration_id_decimal: " ++ rustDecimal field.declarationId ++
    ", kind_id_decimal: " ++ rustDecimal field.kindId ++
    ", carrier_type_id_decimal: " ++ rustDecimal field.carrierTypeId ++
    ", key_type_id_decimal: " ++ rustOptionalDecimal field.keyTypeId ++ " }"

private def renderVerdict : VerdictEvidence → String
  | .free => "UwueavePreoVerdictEvidenceV2::Free"
  | .clash left right =>
      "UwueavePreoVerdictEvidenceV2::Clash { left_words_decimal: " ++
        rustDecimalSlice left ++ ", right_words_decimal: " ++
        rustDecimalSlice right ++ " }"

private def renderInvariant (invariant : InvariantArtifactEncoding) : String :=
  "UwueavePreoInvariantV2 { id_decimal: " ++ rustDecimal invariant.id ++
    ", declaration_id_decimal: " ++ rustDecimal invariant.declarationId ++
    ", carrier_type_id_decimal: " ++ rustDecimal invariant.carrierTypeId ++
    ", verdict: " ++ renderVerdict invariant.verdict ++ " }"

private def renderFuture (future : FutureArtifactEncoding) : String :=
  "UwueavePreoFutureV2 { id_decimal: " ++ rustDecimal future.id ++
    ", declaration_id_decimal: " ++ rustDecimal future.declarationId ++
    ", world_type_id_decimal: " ++ rustDecimal future.worldTypeId ++
    ", relation_id_decimal: " ++ rustDecimal future.relationId ++ " }"

private def renderSession (session : SessionArtifactEncoding) : String :=
  "UwueavePreoSessionV2 { id_decimal: " ++ rustDecimal session.id ++
    ", declaration_id_decimal: " ++ rustDecimal session.declarationId ++
    ", crossings_decimal: " ++ rustDecimal session.crossings ++
    ", obligations: " ++ rustSlice renderObligation session.obligations ++ " }"

private def renderProfileEntry (entry : Currency × Nat) : String :=
  "UwueavePreoProfileEntryV2 { currency: " ++ renderCurrency entry.1 ++
    ", value_decimal: " ++ rustDecimal entry.2 ++ " }"

private def renderPlan (plan : PlanArtifactEncoding) : String :=
  "UwueavePreoPlanV2 { id_decimal: " ++ rustDecimal plan.id ++
    ", session_id_decimal: " ++ rustDecimal plan.sessionId ++
    ", actions: " ++ rustSlice renderDemand plan.actions ++
    ", profile: " ++ rustSlice renderProfileEntry plan.profile ++ " }"

private def renderBudget (budget : BudgetArtifactEncoding) : String :=
  "UwueavePreoBudgetV2 { id_decimal: " ++ rustDecimal budget.id ++
    ", session_id_decimal: " ++ rustDecimal budget.sessionId ++
    ", plan_id_decimal: " ++ rustDecimal budget.planId ++
    ", limits: " ++ rustSlice renderProfileEntry budget.limits ++
    ", realized_profile: " ++ rustSlice renderProfileEntry budget.realizedProfile ++ " }"

private def rustTypeDeclarations : List String :=
  ["    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoCurrencyV2 { PeerBarrier, ArbiterCut, NetworkRound, UserPrompt, Rollback }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoEvidenceKeyV2 { None, Named(&'static str) }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoDemandV2 { pub currency: UwueavePreoCurrencyV2, pub participants_decimal: &'static [&'static str], pub scope_decimal: &'static str, pub epoch_decimal: &'static str, pub evidence: UwueavePreoEvidenceKeyV2, pub round_decimal: &'static str, pub barrier_decimal: &'static str }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoOriginV2 { Crossing { index_decimal: &'static str }, Ambient }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoObligationV2 { pub origin: UwueavePreoOriginV2, pub demand: UwueavePreoDemandV2 }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoDeclarationV2 { pub id_decimal: &'static str, pub state_type_id_decimal: &'static str, pub schema_version_decimal: &'static str }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoFieldV2 { pub id_decimal: &'static str, pub declaration_id_decimal: &'static str, pub kind_id_decimal: &'static str, pub carrier_type_id_decimal: &'static str, pub key_type_id_decimal: Option<&'static str> }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoVerdictEvidenceV2 { Free, Clash { left_words_decimal: &'static [&'static str], right_words_decimal: &'static [&'static str] } }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoInvariantV2 { pub id_decimal: &'static str, pub declaration_id_decimal: &'static str, pub carrier_type_id_decimal: &'static str, pub verdict: UwueavePreoVerdictEvidenceV2 }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoFutureV2 { pub id_decimal: &'static str, pub declaration_id_decimal: &'static str, pub world_type_id_decimal: &'static str, pub relation_id_decimal: &'static str }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoSessionV2 { pub id_decimal: &'static str, pub declaration_id_decimal: &'static str, pub crossings_decimal: &'static str, pub obligations: &'static [UwueavePreoObligationV2] }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoProfileEntryV2 { pub currency: UwueavePreoCurrencyV2, pub value_decimal: &'static str }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoPlanV2 { pub id_decimal: &'static str, pub session_id_decimal: &'static str, pub actions: &'static [UwueavePreoDemandV2], pub profile: &'static [UwueavePreoProfileEntryV2] }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoBudgetV2 { pub id_decimal: &'static str, pub session_id_decimal: &'static str, pub plan_id_decimal: &'static str, pub limits: &'static [UwueavePreoProfileEntryV2], pub realized_profile: &'static [UwueavePreoProfileEntryV2] }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoProjectionV2 { pub schema: &'static str, pub declaration: UwueavePreoDeclarationV2, pub fields: &'static [UwueavePreoFieldV2], pub invariants: &'static [UwueavePreoInvariantV2], pub futures: &'static [UwueavePreoFutureV2], pub sessions: &'static [UwueavePreoSessionV2], pub plans: &'static [UwueavePreoPlanV2], pub budgets: &'static [UwueavePreoBudgetV2] }"]

private def rustProjectionLines (validated : ValidatedProjectionV2) : List String :=
  let encoding := validated.encoding
  ["    pub static UWUEAVE_PREO_PROJECTION_V2: UwueavePreoProjectionV2 =",
   "        UwueavePreoProjectionV2 {",
   "            schema: UWUEAVE_PREO_PROJECTION_V2_SCHEMA,",
   "            declaration: " ++ renderDeclaration encoding.declaration ++ ",",
   "            fields: " ++ rustSlice renderField encoding.fields ++ ",",
   "            invariants: " ++ rustSlice renderInvariant encoding.invariants ++ ",",
   "            futures: " ++ rustSlice renderFuture encoding.futures ++ ",",
   "            sessions: " ++ rustSlice renderSession encoding.sessions ++ ",",
   "            plans: " ++ rustSlice renderPlan encoding.plans ++ ",",
   "            budgets: " ++ rustSlice renderBudget encoding.budgets ++ ",",
   "        };"]

def renderRustSource (validated : ValidatedProjectionV2) : String :=
  String.intercalate "\n" <|
    ["// @generated by Uwueave.Preo.ProjectionV2.renderRustSource; do not edit.",
     "// Validated first-order coordination data only; no verifier or permit API.",
     "", "pub mod uwueave_preo_projection_v2 {",
     "    pub const UWUEAVE_PREO_PROJECTION_V2_SCHEMA: &str = " ++
       rustStringLiteral schema ++ ";", ""] ++
    rustTypeDeclarations ++ [""] ++ rustProjectionLines validated ++ ["}", ""]

def validateAndRender (config : ValidationConfig) (projection : Projection) :
    ValidationResult String :=
  (validate config projection).map renderRustSource

theorem renderRustSource_eq_of_encoding_eq
    {left right : ValidatedProjectionV2} (same : left.encoding = right.encoding) :
    renderRustSource left = renderRustSource right := by
  simp only [renderRustSource, rustProjectionLines]
  rw [same]

theorem validateAndRender_error {config : ValidationConfig} {projection : Projection}
    {error : ValidationError} (refused : validate config projection = .error error) :
    validateAndRender config projection = .error error := by
  rw [validateAndRender, refused]
  rfl

/-! ## §5. Executable acceptance and adversarial refusals -/

namespace Examples

private def validationError? {alpha : Type} :
    ValidationResult alpha → Option ValidationError
  | .ok _ => none
  | .error error => some error

def config : ValidationConfig where
  bounds := {
    maxFields := 8
    maxInvariants := 8
    maxFutures := 8
    maxSessions := 8
    maxPlans := 8
    maxBudgets := 8
    maxObligationsPerSession := 8
    maxActionsPerPlan := 8
    maxProfileEntriesPerPlan := 5
    maxProfileEntriesPerBudget := 5
    maxParticipantsPerDemand := 8
    maxWitnessWords := 8 }

def fullEncoding : ArtifactEncoding :=
  Export.Examples.bundle.project.encoding

def fullExport : Projection := Projection.ofEncoding fullEncoding

/-- Acceptance exercises the proof-originated Export bundle with every row
family nonempty, including its exact five-currency budget. -/
theorem full_export_is_nonempty :
    fullEncoding.fields.length = 1
      ∧ fullEncoding.invariants.length = 1
      ∧ fullEncoding.futures.length = 1
      ∧ fullEncoding.sessions.length = 1
      ∧ fullEncoding.plans.length = 1
      ∧ fullEncoding.budgets.length = 1 := by decide

theorem full_export_validates : (validate config fullExport).isOk = true := by decide

def duplicateBudget : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets ++ fullEncoding.budgets } }

theorem duplicate_budget_refused :
    validationError? (validate config duplicateBudget) =
      some (.duplicateBudgetId 411) := by decide

def danglingBudgetSession : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with sessionId := 999 } } }

theorem dangling_budget_session_refused :
    validationError? (validate config danglingBudgetSession) =
      some (.danglingBudgetSession 411 999) := by decide

def danglingBudgetPlan : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with planId := 999 } } }

theorem dangling_budget_plan_refused :
    validationError? (validate config danglingBudgetPlan) =
      some (.danglingBudgetPlan 411 999) := by decide

def mismatchedBudgetSession : Projection :=
  { fullExport with encoding :=
      { fullEncoding with
        sessions := fullEncoding.sessions ++ fullEncoding.sessions.map fun session =>
          { session with id := 999 }
        budgets := fullEncoding.budgets.map fun budget =>
          { budget with sessionId := 999 } } }

theorem mismatched_budget_session_refused :
    validationError? (validate config mismatchedBudgetSession) =
      some (.budgetPlanSessionMismatch 411 999 407) := by decide

def zeroProfile : List (Currency × Nat) :=
  [(.peerBarrier, 0), (.arbiterCut, 0), (.networkRound, 0),
   (.userPrompt, 0), (.rollback, 0)]

def actionProfileLie : Projection :=
  { fullExport with encoding :=
      { fullEncoding with plans := fullEncoding.plans.map fun plan =>
          { plan with profile := zeroProfile } } }

theorem action_profile_lie_refused :
    validationError? (validate config actionProfileLie) =
      some (.planProfileMismatch 408 zeroProfile
        [(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
         (.userPrompt, 0), (.rollback, 0)]) := by decide

def mismatchedBudgetProfile : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with realizedProfile := zeroProfile } } }

theorem mismatched_budget_profile_refused :
    validationError? (validate config mismatchedBudgetProfile) =
      some (.budgetProfileMismatch 411 408) := by decide

def nonCanonicalBudgetLimits : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with limits := [] } } }

theorem noncanonical_budget_limits_refused :
    validationError? (validate config nonCanonicalBudgetLimits) =
      some (.nonCanonicalBudgetLimits 411 []) := by decide

def exceededBudgetLimit : Projection :=
  { fullExport with encoding :=
      { fullEncoding with budgets := fullEncoding.budgets.map fun budget =>
          { budget with limits := zeroProfile } } }

theorem exceeded_budget_limit_refused :
    validationError? (validate config exceededBudgetLimit) =
      some (.budgetLimitExceeded 411 .peerBarrier 2 0) := by decide

/-- Coverage is checked from session data to the exact referenced plan.  This
fabricated empty action list cannot cover either exported obligation even when
its profile is changed to an honest empty histogram. -/
def uncoveredObligation : Projection :=
  { fullExport with encoding :=
      { fullEncoding with
        plans := fullEncoding.plans.map fun plan =>
          { plan with actions := [], profile := zeroProfile }
        budgets := [] } }

theorem uncovered_obligation_refused :
    validationError? (validate config uncoveredObligation) =
      some (.uncoveredObligation 408 407 0) := by decide

def zeroBudgetBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxBudgets := 0 } }

theorem budget_bound_refused :
    validationError? (validate zeroBudgetBound fullExport) =
      some (.budgetListTooLarge .budgets 1 0) := by decide

def wrongSchema : Projection := { fullExport with schema := ProjectionV1.schema }

theorem wrong_schema_refused :
    validationError? (validate config wrongSchema) =
      some (.wrongSchema schema ProjectionV1.schema) := by decide

set_option maxRecDepth 10000 in
theorem renderer_budget_is_v2 :
    renderBudget ⟨411, 407, 408, zeroProfile, zeroProfile⟩ =
      "UwueavePreoBudgetV2 { id_decimal: \"411\", session_id_decimal: \"407\", plan_id_decimal: \"408\", limits: &[UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::PeerBarrier, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::ArbiterCut, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::NetworkRound, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::UserPrompt, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::Rollback, value_decimal: \"0\" }], realized_profile: &[UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::PeerBarrier, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::ArbiterCut, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::NetworkRound, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::UserPrompt, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::Rollback, value_decimal: \"0\" }] }" := by
  rfl

/-- The public renderer path preserves a precise refusal and therefore cannot
manufacture a private validated value as fallback. -/
theorem renderer_preserves_error :
    validateAndRender config exceededBudgetLimit =
      .error (.budgetLimitExceeded 411 .peerBarrier 2 0) := by
  rfl

/-- Decimal output is deliberately wider than every Rust machine integer. -/
theorem unbounded_decimal_fixture :
    rustDecimal (2 ^ 100) = "\"1267650600228229401496703205376\"" := by decide

end Examples

end Uwueave.Preo.ProjectionV2
