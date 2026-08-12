/-
# Uwueave.Preo.ProjectionV2 — V2 validated Rust rendering

The data-only validator lives in ProjectionV2Core. This production surface adds
only deterministic rendering from the private validated boundary; diagnostics,
worked exports, and giant exact-string fixtures are opt-in modules. A direct
import therefore no longer carries the historical `Repr` or `Examples`
surface: import `ProjectionV2Diagnostics`, `ProjectionV2Examples`, or
`ProjectionV2Fixtures` explicitly when needed.

The measured V2 production closure is four project modules—`ArtifactData`,
both validator cores, and this renderer—totalling 4,290,744 olean bytes and
665,363 generated-C bytes. Its setup contains no `Export`, `Scheduling`, or
`Tactics` dependency and no elevated recursion option.
-/
import Uwueave.Preo.ProjectionV2Core

namespace Uwueave.Preo.ProjectionV2

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

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


/-! ## Narrow fixture hooks -/

namespace FixtureHooks

def decimal (value : Nat) : String := rustDecimal value
def budget (value : BudgetArtifactEncoding) : String := renderBudget value

end FixtureHooks

end Uwueave.Preo.ProjectionV2
