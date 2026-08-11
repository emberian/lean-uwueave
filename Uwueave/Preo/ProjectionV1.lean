/-
# Uwueave.Preo.ProjectionV1 — bounded neutral host projection

`Preo.Artifact` deliberately stops at closed first-order data.  This module
adds the versioned validation boundary a host needs before inspecting that
data.  Validation checks schema, resource bounds, stable-ID uniqueness and
the references whose consistency is visible in the projection.  It does not
turn `VerdictEvidence.free` back into a proof, authorize an operation, or issue
a permit.

Every number remains a Lean `Nat`.  A later byte or generated-source adapter
must preserve that unbounded representation (for example as canonical decimal
text) rather than silently narrowing it to a machine integer.
-/
import Uwueave.Preo.Export

namespace Uwueave.Preo.ProjectionV1

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

/-! ## §1. Versioned untrusted input and explicit resource policy -/

/-- The exact schema identifier for this typed projection. -/
def schema : String := "uwueave/preo-projection/v1"

/-- Untrusted, neutral input to the V1 validator.  The artifact encoding is
still only first-order inspection data. -/
structure Projection where
  schema : String
  encoding : ArtifactEncoding
  deriving DecidableEq, Repr

/-- Construct a correctly tagged input from a first-order artifact encoding.
This supplies only the tag; callers must still invoke `validate`. -/
def Projection.ofEncoding (encoding : ArtifactEncoding) : Projection :=
  ⟨Uwueave.Preo.ProjectionV1.schema, encoding⟩

/-- Every variable-length collection checked before a host receives a
validated projection.  There are intentionally no implicit defaults: a host
must select its own resource policy. -/
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
  deriving DecidableEq, Repr

/-- Validation policy kept as a structure so later versions can add explicit
non-semantic host limits without changing the validator's argument shape. -/
structure ValidationConfig where
  bounds : ValidationBounds
  deriving DecidableEq, Repr

inductive StableIdKind where
  | field
  | invariant
  | future
  | session
  | plan
  deriving DecidableEq, Repr

inductive DeclarationRowKind where
  | field
  | invariant
  | future
  | session
  deriving DecidableEq, Repr

inductive WitnessSide where
  | left
  | right
  deriving DecidableEq, Repr

inductive DemandLocation where
  | sessionObligation (sessionId obligationIndex : Nat)
  | planAction (planId actionIndex : Nat)
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

/-- Fail-closed validation failures.  Unknown enum constructors cannot inhabit
the typed Lean input at all.  The representable tag-shape inconsistency is a
plan profile whose currency tags are missing, duplicated, reordered, or
extended; `nonCanonicalPlanProfile` rejects all of those cases. -/
inductive ValidationError where
  | wrongSchema (expected found : String)
  | listTooLarge (list : BoundedList) (actual limit : Nat)
  | duplicateStableId (kind : StableIdKind) (id : Nat)
  | wrongDeclarationReference (kind : DeclarationRowKind) (rowId expected found : Nat)
  | danglingPlanSession (planId sessionId : Nat)
  | crossingIndexOutOfRange
      (sessionId obligationIndex crossingIndex crossings : Nat)
  | nonCanonicalPlanProfile (planId : Nat) (found : List Currency)
  deriving DecidableEq, Repr

abbrev ValidationResult (alpha : Type) := Except ValidationError alpha

/-! ## §2. The private validated boundary -/

/-- A validated projection is constructible only by this module's successful
validator.  Its public surface remains inspection data: it contains no proof,
permit, admission token, or Boolean acceptance judgement. -/
structure ValidatedProjectionV1 where private mk ::
  projection : Projection
  config : ValidationConfig
  deriving DecidableEq, Repr

/-- Inspect the exact validated schema tag. -/
def ValidatedProjectionV1.schema (validated : ValidatedProjectionV1) : String :=
  validated.projection.schema

/-- Inspect the first-order encoding.  In particular, an invariant's `.free`
constructor remains `VerdictEvidence`, not a reconstructed `Spec.Verdict`. -/
def ValidatedProjectionV1.encoding
    (validated : ValidatedProjectionV1) : ArtifactEncoding :=
  validated.projection.encoding

/-- Inspect the resource policy under which the projection was accepted. -/
def ValidatedProjectionV1.validationConfig
    (validated : ValidatedProjectionV1) : ValidationConfig :=
  validated.config

/-! ## §3. Deterministic fail-closed validation -/

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

/-- Validate one V1 host projection.  Checks are deliberately structural and
resource-oriented.  Success does not semantically endorse the data: only the
proof-indexed constructors in `Preo.Artifact` originate such evidence. -/
def validate (config : ValidationConfig) (projection : Projection) :
    ValidationResult ValidatedProjectionV1 := do
  if projection.schema = schema then
    pure ()
  else
    throw (.wrongSchema schema projection.schema)

  let encoding := projection.encoding
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

/-! ## §4. Deterministic data-only Rust source -/

private def rustUnicodeEscape (character : Char) : String :=
  "\\u{" ++ String.ofList (Nat.toDigits 16 character.toNat) ++ "}"

/-- Canonical Rust string escaping.  Printable ASCII is retained except for
the two string delimiters; every other Unicode scalar has one lowercase
`\\u{...}` spelling. -/
private def rustEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | character =>
      if 0x20 ≤ character.toNat then
        if character.toNat ≤ 0x7e then character.toString
        else rustUnicodeEscape character
      else
        rustUnicodeEscape character

private def rustStringLiteral (value : String) : String :=
  "\"" ++ String.intercalate "" (value.toList.map rustEscapeChar) ++ "\""

/-- A `Nat` is emitted only as decimal text inside a Rust string literal. -/
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
  | .peerBarrier => "UwueavePreoCurrencyV1::PeerBarrier"
  | .arbiterCut => "UwueavePreoCurrencyV1::ArbiterCut"
  | .networkRound => "UwueavePreoCurrencyV1::NetworkRound"
  | .userPrompt => "UwueavePreoCurrencyV1::UserPrompt"
  | .rollback => "UwueavePreoCurrencyV1::Rollback"

private def renderEvidenceKey : EvidenceKey → String
  | .none => "UwueavePreoEvidenceKeyV1::None"
  | .named key => "UwueavePreoEvidenceKeyV1::Named(" ++ rustDecimal key ++ ")"

private def renderDemand (demand : DemandArtifact) : String :=
  "UwueavePreoDemandV1 { currency: " ++ renderCurrency demand.currency ++
    ", participants_decimal: " ++ rustDecimalSlice demand.participants ++
    ", scope_decimal: " ++ rustDecimal demand.scope ++
    ", epoch_decimal: " ++ rustDecimal demand.epoch ++
    ", evidence: " ++ renderEvidenceKey demand.evidence ++
    ", round_decimal: " ++ rustDecimal demand.round ++
    ", barrier_decimal: " ++ rustDecimal demand.barrier ++ " }"

private def renderOrigin : OriginArtifact → String
  | .ambient => "UwueavePreoOriginV1::Ambient"
  | .crossing index =>
      "UwueavePreoOriginV1::Crossing { index_decimal: " ++ rustDecimal index ++ " }"

private def renderObligation (obligation : ObligationArtifact) : String :=
  "UwueavePreoObligationV1 { origin: " ++ renderOrigin obligation.origin ++
    ", demand: " ++ renderDemand obligation.demand ++ " }"

private def renderDeclaration (declaration : DeclarationArtifactEncoding) : String :=
  "UwueavePreoDeclarationV1 { id_decimal: " ++ rustDecimal declaration.id ++
    ", state_type_id_decimal: " ++ rustDecimal declaration.stateTypeId ++
    ", schema_version_decimal: " ++ rustDecimal declaration.schemaVersion ++ " }"

private def renderField (field : FieldArtifactEncoding) : String :=
  "UwueavePreoFieldV1 { id_decimal: " ++ rustDecimal field.id ++
    ", declaration_id_decimal: " ++ rustDecimal field.declarationId ++
    ", kind_id_decimal: " ++ rustDecimal field.kindId ++
    ", carrier_type_id_decimal: " ++ rustDecimal field.carrierTypeId ++
    ", key_type_id_decimal: " ++ rustOptionalDecimal field.keyTypeId ++ " }"

private def renderVerdict : VerdictEvidence → String
  | .free => "UwueavePreoVerdictEvidenceV1::Free"
  | .clash left right =>
      "UwueavePreoVerdictEvidenceV1::Clash { left_words_decimal: " ++
        rustDecimalSlice left ++ ", right_words_decimal: " ++ rustDecimalSlice right ++ " }"

private def renderInvariant (invariant : InvariantArtifactEncoding) : String :=
  "UwueavePreoInvariantV1 { id_decimal: " ++ rustDecimal invariant.id ++
    ", declaration_id_decimal: " ++ rustDecimal invariant.declarationId ++
    ", carrier_type_id_decimal: " ++ rustDecimal invariant.carrierTypeId ++
    ", verdict: " ++ renderVerdict invariant.verdict ++ " }"

private def renderFuture (future : FutureArtifactEncoding) : String :=
  "UwueavePreoFutureV1 { id_decimal: " ++ rustDecimal future.id ++
    ", declaration_id_decimal: " ++ rustDecimal future.declarationId ++
    ", world_type_id_decimal: " ++ rustDecimal future.worldTypeId ++
    ", relation_id_decimal: " ++ rustDecimal future.relationId ++ " }"

private def renderSession (session : SessionArtifactEncoding) : String :=
  "UwueavePreoSessionV1 { id_decimal: " ++ rustDecimal session.id ++
    ", declaration_id_decimal: " ++ rustDecimal session.declarationId ++
    ", crossings_decimal: " ++ rustDecimal session.crossings ++
    ", obligations: " ++ rustSlice renderObligation session.obligations ++ " }"

private def renderProfileEntry (entry : Currency × Nat) : String :=
  "UwueavePreoProfileEntryV1 { currency: " ++ renderCurrency entry.1 ++
    ", value_decimal: " ++ rustDecimal entry.2 ++ " }"

private def renderPlan (plan : PlanArtifactEncoding) : String :=
  "UwueavePreoPlanV1 { id_decimal: " ++ rustDecimal plan.id ++
    ", session_id_decimal: " ++ rustDecimal plan.sessionId ++
    ", actions: " ++ rustSlice renderDemand plan.actions ++
    ", profile: " ++ rustSlice renderProfileEntry plan.profile ++ " }"

private def rustTypeDeclarations : List String :=
  ["    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoCurrencyV1 {",
   "        PeerBarrier,",
   "        ArbiterCut,",
   "        NetworkRound,",
   "        UserPrompt,",
   "        Rollback,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoEvidenceKeyV1 {",
   "        None,",
   "        Named(&'static str),",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoDemandV1 {",
   "        pub currency: UwueavePreoCurrencyV1,",
   "        pub participants_decimal: &'static [&'static str],",
   "        pub scope_decimal: &'static str,",
   "        pub epoch_decimal: &'static str,",
   "        pub evidence: UwueavePreoEvidenceKeyV1,",
   "        pub round_decimal: &'static str,",
   "        pub barrier_decimal: &'static str,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoOriginV1 {",
   "        Crossing { index_decimal: &'static str },",
   "        Ambient,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoObligationV1 {",
   "        pub origin: UwueavePreoOriginV1,",
   "        pub demand: UwueavePreoDemandV1,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoDeclarationV1 {",
   "        pub id_decimal: &'static str,",
   "        pub state_type_id_decimal: &'static str,",
   "        pub schema_version_decimal: &'static str,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoFieldV1 {",
   "        pub id_decimal: &'static str,",
   "        pub declaration_id_decimal: &'static str,",
   "        pub kind_id_decimal: &'static str,",
   "        pub carrier_type_id_decimal: &'static str,",
   "        pub key_type_id_decimal: Option<&'static str>,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoVerdictEvidenceV1 {",
   "        Free,",
   "        Clash {",
   "            left_words_decimal: &'static [&'static str],",
   "            right_words_decimal: &'static [&'static str],",
   "        },",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoInvariantV1 {",
   "        pub id_decimal: &'static str,",
   "        pub declaration_id_decimal: &'static str,",
   "        pub carrier_type_id_decimal: &'static str,",
   "        pub verdict: UwueavePreoVerdictEvidenceV1,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoFutureV1 {",
   "        pub id_decimal: &'static str,",
   "        pub declaration_id_decimal: &'static str,",
   "        pub world_type_id_decimal: &'static str,",
   "        pub relation_id_decimal: &'static str,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoSessionV1 {",
   "        pub id_decimal: &'static str,",
   "        pub declaration_id_decimal: &'static str,",
   "        pub crossings_decimal: &'static str,",
   "        pub obligations: &'static [UwueavePreoObligationV1],",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoProfileEntryV1 {",
   "        pub currency: UwueavePreoCurrencyV1,",
   "        pub value_decimal: &'static str,",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoPlanV1 {",
   "        pub id_decimal: &'static str,",
   "        pub session_id_decimal: &'static str,",
   "        pub actions: &'static [UwueavePreoDemandV1],",
   "        pub profile: &'static [UwueavePreoProfileEntryV1],",
   "    }",
   "",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoProjectionV1 {",
   "        pub schema: &'static str,",
   "        pub declaration: UwueavePreoDeclarationV1,",
   "        pub fields: &'static [UwueavePreoFieldV1],",
   "        pub invariants: &'static [UwueavePreoInvariantV1],",
   "        pub futures: &'static [UwueavePreoFutureV1],",
   "        pub sessions: &'static [UwueavePreoSessionV1],",
   "        pub plans: &'static [UwueavePreoPlanV1],",
   "    }"]

/-- The static value portion of generated source.  Keeping this helper on the
validated type makes it possible to fixture every emitted row without opening
a second renderer over raw encodings. -/
private def rustProjectionLines (validated : ValidatedProjectionV1) : List String :=
  let encoding := validated.encoding
  ["    pub static UWUEAVE_PREO_PROJECTION_V1: UwueavePreoProjectionV1 =",
   "        UwueavePreoProjectionV1 {",
   "            schema: UWUEAVE_PREO_PROJECTION_V1_SCHEMA,",
   "            declaration: " ++ renderDeclaration encoding.declaration ++ ",",
   "            fields: " ++ rustSlice renderField encoding.fields ++ ",",
   "            invariants: " ++ rustSlice renderInvariant encoding.invariants ++ ",",
   "            futures: " ++ rustSlice renderFuture encoding.futures ++ ",",
   "            sessions: " ++ rustSlice renderSession encoding.sessions ++ ",",
   "            plans: " ++ rustSlice renderPlan encoding.plans ++ ",",
   "        };"]

/-- Render deterministic, namespaced, data-only Rust source.  The only entry
argument is a value that already crossed `validate`; there is no renderer from
raw `ArtifactEncoding`.  Every list is mapped without sorting, so declaration
row and nested order is exactly the validated artifact order.  Validation
bounds are host-local policy and are intentionally not serialized. -/
def renderRustSource (validated : ValidatedProjectionV1) : String :=
  String.intercalate "\n" <|
    ["// @generated by Uwueave.Preo.ProjectionV1.renderRustSource; do not edit.",
     "// Validated first-order coordination data only; no verifier or permit API.",
     "",
     "pub mod uwueave_preo_projection_v1 {",
     "    pub const UWUEAVE_PREO_PROJECTION_V1_SCHEMA: &str = " ++
       rustStringLiteral schema ++ ";",
     ""] ++ rustTypeDeclarations ++ [""] ++ rustProjectionLines validated ++
    ["}", ""]

/-- The public raw-input convenience path still validates first.  `Except.map`
does not invoke the renderer when validation returns an error. -/
def validateAndRender (config : ValidationConfig) (projection : Projection) :
    ValidationResult String :=
  (validate config projection).map renderRustSource

/-- Rendering is a pure function of the validated first-order encoding.  The
host-local bounds used to establish validation do not alter generated bytes. -/
theorem renderRustSource_eq_of_encoding_eq
    {left right : ValidatedProjectionV1} (same : left.encoding = right.encoding) :
    renderRustSource left = renderRustSource right := by
  simp only [renderRustSource, rustProjectionLines]
  rw [same]

/-- Any validation refusal is preserved verbatim and cannot enter the private
validated renderer. -/
theorem validateAndRender_error {config : ValidationConfig} {projection : Projection}
    {error : ValidationError} (refused : validate config projection = .error error) :
    validateAndRender config projection = .error error := by
  rw [validateAndRender, refused]
  rfl

/-! ## §5. Executable acceptance, refusal, and source fixtures -/

namespace Examples

private def validationError? {alpha : Type} :
    ValidationResult alpha → Option ValidationError
  | .ok _ => none
  | .error error => some error

private def validatedProjectionLines? (config : ValidationConfig)
    (projection : Projection) : Option (List String) :=
  match validate config projection with
  | .ok validated => some (rustProjectionLines validated)
  | .error _ => none

/-- Deliberately finite test policy.  Production hosts must choose their own
limits instead of treating these example values as protocol constants. -/
def config : ValidationConfig where
  bounds := {
    maxFields := 8
    maxInvariants := 8
    maxFutures := 8
    maxSessions := 8
    maxPlans := 8
    maxObligationsPerSession := 8
    maxActionsPerPlan := 8
    maxProfileEntriesPerPlan := 5
    maxParticipantsPerDemand := 8
    maxWitnessWords := 8 }

def emptyConfig : ValidationConfig where
  bounds := {
    maxFields := 0
    maxInvariants := 0
    maxFutures := 0
    maxSessions := 0
    maxPlans := 0
    maxObligationsPerSession := 0
    maxActionsPerPlan := 0
    maxProfileEntriesPerPlan := 0
    maxParticipantsPerDemand := 0
    maxWitnessWords := 0 }

def emptyProjection : Projection :=
  Projection.ofEncoding {
    declaration := ⟨1, 2, 3⟩
    fields := []
    invariants := []
    futures := []
    sessions := []
    plans := [] }

/-- Canonical escaping has one exact spelling for delimiters, controls, and
non-ASCII Unicode. -/
theorem rust_string_literal_fixture :
    rustStringLiteral "A\"\\\nλ" = "\"A\\\"\\\\\\u{a}\\u{3bb}\"" := by decide

/-- Decimal emission is not bounded by a Rust machine word. -/
theorem unbounded_decimal_fixture :
    rustDecimal (2 ^ 100) = "\"1267650600228229401496703205376\"" := by decide

def emptyRustFixture : String := r###"// @generated by Uwueave.Preo.ProjectionV1.renderRustSource; do not edit.
// Validated first-order coordination data only; no verifier or permit API.

pub mod uwueave_preo_projection_v1 {
    pub const UWUEAVE_PREO_PROJECTION_V1_SCHEMA: &str = "uwueave/preo-projection/v1";

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum UwueavePreoCurrencyV1 {
        PeerBarrier,
        ArbiterCut,
        NetworkRound,
        UserPrompt,
        Rollback,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum UwueavePreoEvidenceKeyV1 {
        None,
        Named(&'static str),
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoDemandV1 {
        pub currency: UwueavePreoCurrencyV1,
        pub participants_decimal: &'static [&'static str],
        pub scope_decimal: &'static str,
        pub epoch_decimal: &'static str,
        pub evidence: UwueavePreoEvidenceKeyV1,
        pub round_decimal: &'static str,
        pub barrier_decimal: &'static str,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum UwueavePreoOriginV1 {
        Crossing { index_decimal: &'static str },
        Ambient,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoObligationV1 {
        pub origin: UwueavePreoOriginV1,
        pub demand: UwueavePreoDemandV1,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoDeclarationV1 {
        pub id_decimal: &'static str,
        pub state_type_id_decimal: &'static str,
        pub schema_version_decimal: &'static str,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoFieldV1 {
        pub id_decimal: &'static str,
        pub declaration_id_decimal: &'static str,
        pub kind_id_decimal: &'static str,
        pub carrier_type_id_decimal: &'static str,
        pub key_type_id_decimal: Option<&'static str>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum UwueavePreoVerdictEvidenceV1 {
        Free,
        Clash {
            left_words_decimal: &'static [&'static str],
            right_words_decimal: &'static [&'static str],
        },
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoInvariantV1 {
        pub id_decimal: &'static str,
        pub declaration_id_decimal: &'static str,
        pub carrier_type_id_decimal: &'static str,
        pub verdict: UwueavePreoVerdictEvidenceV1,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoFutureV1 {
        pub id_decimal: &'static str,
        pub declaration_id_decimal: &'static str,
        pub world_type_id_decimal: &'static str,
        pub relation_id_decimal: &'static str,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoSessionV1 {
        pub id_decimal: &'static str,
        pub declaration_id_decimal: &'static str,
        pub crossings_decimal: &'static str,
        pub obligations: &'static [UwueavePreoObligationV1],
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoProfileEntryV1 {
        pub currency: UwueavePreoCurrencyV1,
        pub value_decimal: &'static str,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoPlanV1 {
        pub id_decimal: &'static str,
        pub session_id_decimal: &'static str,
        pub actions: &'static [UwueavePreoDemandV1],
        pub profile: &'static [UwueavePreoProfileEntryV1],
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct UwueavePreoProjectionV1 {
        pub schema: &'static str,
        pub declaration: UwueavePreoDeclarationV1,
        pub fields: &'static [UwueavePreoFieldV1],
        pub invariants: &'static [UwueavePreoInvariantV1],
        pub futures: &'static [UwueavePreoFutureV1],
        pub sessions: &'static [UwueavePreoSessionV1],
        pub plans: &'static [UwueavePreoPlanV1],
    }

    pub static UWUEAVE_PREO_PROJECTION_V1: UwueavePreoProjectionV1 =
        UwueavePreoProjectionV1 {
            schema: UWUEAVE_PREO_PROJECTION_V1_SCHEMA,
            declaration: UwueavePreoDeclarationV1 { id_decimal: "1", state_type_id_decimal: "2", schema_version_decimal: "3" },
            fields: &[],
            invariants: &[],
            futures: &[],
            sessions: &[],
            plans: &[],
        };
}
"###

def artifactExample : Projection :=
  Projection.ofEncoding Artifact.Examples.bundle.canonicalEncoding

def exportExample : Projection :=
  Projection.ofEncoding Export.Examples.bundle.project.encoding

def rendererDemand : DemandArtifact where
  currency := .peerBarrier
  participants := [0, 1]
  scope := 7
  epoch := 3
  evidence := .named 11
  round := 0
  barrier := 5

def rendererProfile : List (Currency × Nat) :=
  [(.peerBarrier, 1), (.arbiterCut, 0), (.networkRound, 0),
   (.userPrompt, 0), (.rollback, 0)]

/-- A compact first-order fixture spelling every renderer shape explicitly.
It is still raw input and must pass `validate` before the public renderer can
consume it. -/
def rendererFixture : Projection :=
  Projection.ofEncoding {
    declaration := ⟨100, 200, 1⟩
    fields := [⟨101, 100, 10, 200, none⟩]
    invariants := [⟨102, 100, 200, .free⟩, ⟨106, 100, 201, .clash [1, 0] [0, 1]⟩]
    futures := [⟨103, 100, 200, 300⟩]
    sessions := [⟨104, 100, 1, [⟨.crossing 0, rendererDemand⟩]⟩]
    plans := [⟨105, 104, [rendererDemand], rendererProfile⟩] }

/-- Exact static-value fixture for the empty shape.  Even this degenerate case
must pass validation before the renderer implementation can be called. -/
theorem empty_projection_lines_fixture :
    validatedProjectionLines? emptyConfig emptyProjection = some
      ["    pub static UWUEAVE_PREO_PROJECTION_V1: UwueavePreoProjectionV1 =",
       "        UwueavePreoProjectionV1 {",
       "            schema: UWUEAVE_PREO_PROJECTION_V1_SCHEMA,",
       "            declaration: UwueavePreoDeclarationV1 { id_decimal: \"1\", state_type_id_decimal: \"2\", schema_version_decimal: \"3\" },",
       "            fields: &[],",
       "            invariants: &[],",
       "            futures: &[],",
       "            sessions: &[],",
       "            plans: &[],",
       "        };"] := by decide

/-- Exact nonempty row fixtures.  Together with
`renderer_fixture_validates`, these pin every V1 row family, both verdict tags,
nested demand/origin/evidence data, every stable reference, and the complete
five-currency profile in artifact order. -/
theorem renderer_declaration_rust_fixture :
    renderDeclaration rendererFixture.encoding.declaration =
      "UwueavePreoDeclarationV1 { id_decimal: \"100\", state_type_id_decimal: \"200\", schema_version_decimal: \"1\" }" := by
  rfl

set_option maxRecDepth 2000 in
theorem renderer_fields_rust_fixture :
    rustSlice renderField rendererFixture.encoding.fields =
      "&[UwueavePreoFieldV1 { id_decimal: \"101\", declaration_id_decimal: \"100\", kind_id_decimal: \"10\", carrier_type_id_decimal: \"200\", key_type_id_decimal: None }]" := by
  rfl

set_option maxRecDepth 4000 in
theorem renderer_invariants_rust_fixture :
    rustSlice renderInvariant rendererFixture.encoding.invariants =
      "&[UwueavePreoInvariantV1 { id_decimal: \"102\", declaration_id_decimal: \"100\", carrier_type_id_decimal: \"200\", verdict: UwueavePreoVerdictEvidenceV1::Free }, UwueavePreoInvariantV1 { id_decimal: \"106\", declaration_id_decimal: \"100\", carrier_type_id_decimal: \"201\", verdict: UwueavePreoVerdictEvidenceV1::Clash { left_words_decimal: &[\"1\", \"0\"], right_words_decimal: &[\"0\", \"1\"] } }]" := by
  rfl

set_option maxRecDepth 2000 in
theorem renderer_futures_rust_fixture :
    rustSlice renderFuture rendererFixture.encoding.futures =
      "&[UwueavePreoFutureV1 { id_decimal: \"103\", declaration_id_decimal: \"100\", world_type_id_decimal: \"200\", relation_id_decimal: \"300\" }]" := by
  rfl

set_option maxRecDepth 4000 in
theorem renderer_demand_rust_fixture :
    renderDemand rendererDemand =
      "UwueavePreoDemandV1 { currency: UwueavePreoCurrencyV1::PeerBarrier, participants_decimal: &[\"0\", \"1\"], scope_decimal: \"7\", epoch_decimal: \"3\", evidence: UwueavePreoEvidenceKeyV1::Named(\"11\"), round_decimal: \"0\", barrier_decimal: \"5\" }" := by
  rfl

set_option maxRecDepth 6000 in
theorem renderer_obligation_rust_fixture :
    renderObligation ⟨.crossing 0, rendererDemand⟩ =
      "UwueavePreoObligationV1 { origin: UwueavePreoOriginV1::Crossing { index_decimal: \"0\" }, demand: UwueavePreoDemandV1 { currency: UwueavePreoCurrencyV1::PeerBarrier, participants_decimal: &[\"0\", \"1\"], scope_decimal: \"7\", epoch_decimal: \"3\", evidence: UwueavePreoEvidenceKeyV1::Named(\"11\"), round_decimal: \"0\", barrier_decimal: \"5\" } }" := by
  rfl

theorem renderer_session_reference_rust_fixture :
    renderSession ⟨104, 100, 1, []⟩ =
      "UwueavePreoSessionV1 { id_decimal: \"104\", declaration_id_decimal: \"100\", crossings_decimal: \"1\", obligations: &[] }" := by
  rfl

set_option maxRecDepth 6000 in
theorem renderer_profile_rust_fixture :
    rustSlice renderProfileEntry rendererProfile =
      "&[UwueavePreoProfileEntryV1 { currency: UwueavePreoCurrencyV1::PeerBarrier, value_decimal: \"1\" }, UwueavePreoProfileEntryV1 { currency: UwueavePreoCurrencyV1::ArbiterCut, value_decimal: \"0\" }, UwueavePreoProfileEntryV1 { currency: UwueavePreoCurrencyV1::NetworkRound, value_decimal: \"0\" }, UwueavePreoProfileEntryV1 { currency: UwueavePreoCurrencyV1::UserPrompt, value_decimal: \"0\" }, UwueavePreoProfileEntryV1 { currency: UwueavePreoCurrencyV1::Rollback, value_decimal: \"0\" }]" := by
  rfl

theorem renderer_plan_reference_rust_fixture :
    renderPlan ⟨105, 104, [], []⟩ =
      "UwueavePreoPlanV1 { id_decimal: \"105\", session_id_decimal: \"104\", actions: &[], profile: &[] }" := by
  rfl

/-- The artifact example has every row class and both verdict constructors. -/
theorem artifact_example_validates :
    (validate config artifactExample).isOk = true := by decide

/-- The proof-indexed export example includes a certified ERA future and a
real protocol elaboration. -/
theorem export_example_validates :
    (validate config exportExample).isOk = true := by decide

theorem renderer_fixture_validates :
    (validate config rendererFixture).isOk = true := by decide

def duplicateField : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with fields := encoding.fields ++ encoding.fields } }

theorem duplicate_field_refused : validationError? (validate config duplicateField) =
    some (.duplicateStableId .field 101) := by decide

/-- The public raw-input convenience path preserves the refusal; it has no
fallback constructor with which to invoke `renderRustSource`. -/
theorem duplicate_field_cannot_reach_renderer :
    validationError? (validateAndRender config duplicateField) =
      some (.duplicateStableId .field 101) := by decide

def wrongFieldDeclaration : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with fields := encoding.fields.map fun field =>
          { field with declarationId := 999 } } }

theorem wrong_field_declaration_refused :
    validationError? (validate config wrongFieldDeclaration) =
    some (.wrongDeclarationReference .field 101 100 999) := by decide

def danglingPlan : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with plans := encoding.plans.map fun plan =>
          { plan with sessionId := 999 } } }

theorem dangling_plan_session_refused : validationError? (validate config danglingPlan) =
    some (.danglingPlanSession 105 999) := by decide

def outOfRangeCrossing : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with sessions := encoding.sessions.map fun session =>
          { session with crossings := 0 } } }

theorem out_of_range_crossing_refused :
    validationError? (validate config outOfRangeCrossing) =
    some (.crossingIndexOutOfRange 104 0 0 0) := by decide

def nonCanonicalProfile : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with plans := encoding.plans.map fun plan =>
          { plan with profile := [] } } }

theorem noncanonical_profile_refused :
    validationError? (validate config nonCanonicalProfile) =
    some (.nonCanonicalPlanProfile 105 []) := by decide

def zeroFieldBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxFields := 0 } }

theorem field_bound_enforced :
    validationError? (validate zeroFieldBound artifactExample) =
    some (.listTooLarge .fields 1 0) := by decide

def oneWitnessWordBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxWitnessWords := 1 } }

theorem witness_bound_enforced :
    validationError? (validate oneWitnessWordBound artifactExample) =
    some (.listTooLarge (.clashWitness 106 .left) 2 1) := by decide

def zeroObligationBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxObligationsPerSession := 0 } }

theorem obligation_bound_enforced :
    validationError? (validate zeroObligationBound artifactExample) =
    some (.listTooLarge (.sessionObligations 104) 1 0) := by decide

def wrongSchema : Projection :=
  { artifactExample with schema := "uwueave/preo-projection/v2" }

theorem wrong_schema_refused : validationError? (validate config wrongSchema) =
    some (.wrongSchema schema "uwueave/preo-projection/v2") := by decide

theorem wrong_schema_cannot_reach_renderer :
    validationError? (validateAndRender config wrongSchema) =
      some (.wrongSchema schema "uwueave/preo-projection/v2") := by decide

end Examples

end Uwueave.Preo.ProjectionV1
