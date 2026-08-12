/-
# Uwueave.Preo.ProjectionV1 — validated V1 Rust rendering

`ProjectionV1Core` owns the bounded, fail-closed data validator. This
production module adds deterministic Rust rendering from its private validated
boundary. Together they import only `ArtifactData`: the measured production
closure is three project modules, 3,354,088 olean bytes and 621,168 generated-C
bytes.

The historical transitive conveniences are now explicit opt-ins:
`ProjectionV1Diagnostics` restores the original `Repr` instance names,
`ProjectionV1Examples` imports proof-indexed `Export` examples, and
`ProjectionV1Fixtures` contains exact rendered-string regression theorems.
Thus a direct `import Uwueave.Preo.ProjectionV1` intentionally provides the
validator and renderer, not diagnostics or worked fixtures.

Every number remains a Lean `Nat`.  A later byte or generated-source adapter
must preserve that unbounded representation (for example as canonical decimal
text) rather than silently narrowing it to a machine integer. Neither
validation nor rendering reconstructs a proof, grants authority, or issues a
permit.
-/
import Uwueave.Preo.ProjectionV1Core

namespace Uwueave.Preo.ProjectionV1

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

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


/-! ## Narrow fixture hooks

These wrappers expose only renderer fragments used by the opt-in fixture
module. The compositional implementation remains private and production
callers still enter through `renderRustSource`. -/

namespace FixtureHooks

def stringLiteral (value : String) : String := rustStringLiteral value
def decimal (value : Nat) : String := rustDecimal value
def declaration (value : DeclarationArtifactEncoding) : String := renderDeclaration value
def fields (values : List FieldArtifactEncoding) : String := rustSlice renderField values
def invariants (values : List InvariantArtifactEncoding) : String :=
  rustSlice renderInvariant values
def futures (values : List FutureArtifactEncoding) : String := rustSlice renderFuture values
def demand (value : DemandArtifact) : String := renderDemand value
def obligation (value : ObligationArtifact) : String := renderObligation value
def session (value : SessionArtifactEncoding) : String := renderSession value
def profile (values : List (Currency × Nat)) : String :=
  rustSlice renderProfileEntry values
def plan (value : PlanArtifactEncoding) : String := renderPlan value

def projectionLines? (config : ValidationConfig)
    (projection : Projection) : Option (List String) :=
  match validate config projection with
  | .ok validated => some (rustProjectionLines validated)
  | .error _ => none

end FixtureHooks

end Uwueave.Preo.ProjectionV1
