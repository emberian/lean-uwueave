/-
# Uwueave.Preo.ProjectionV3 — deterministic V3 Rust DTO rendering

The data-only validator lives in `ProjectionV3Core`.  This production module
adds deterministic Rust source only.  It reuses the validated V2 renderer for
the unchanged base and emits a V3 extension DTO containing stable world,
query, result, and certificate rows.  Diagnostics, examples, and exact golden
strings are opt-in leaves.
-/
import Uwueave.Preo.ProjectionV3Core
import Uwueave.Preo.ProjectionV2

namespace Uwueave.Preo.ProjectionV3

open Uwueave.Preo.ArtifactV3

set_option autoImplicit false

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

private def renderHoleKind : HoleKind → String
  | .field => "UwueavePreoHoleKindV3::Field"
  | .opaque => "UwueavePreoHoleKindV3::Opaque"

private def renderHole (hole : HoleRow) : String :=
  "UwueavePreoHoleV3 { path_decimal: " ++ rustSlice rustDecimal hole.path ++
    ", field_id_decimal: " ++ rustDecimal hole.field.value ++
    ", kind: " ++ renderHoleKind hole.kind ++ " }"

private def renderAnalysis : AnalysisTag → String
  | .mergeSafe => "UwueavePreoAnalysisV3::MergeSafe"
  | .monotoneSafe => "UwueavePreoAnalysisV3::MonotoneSafe"

private def renderQuery (query : QueryRow) : String :=
  "UwueavePreoQueryV3 { id_decimal: " ++ rustDecimal query.id.value ++
    ", schema_id_decimal: " ++ rustDecimal query.schema.value ++
    ", result_id_decimal: " ++ rustDecimal query.result.value ++
    ", program_id_decimal: " ++ rustDecimal query.program.value ++
    ", reads_decimal: " ++ rustSlice (fun id => rustDecimal id.value) query.reads ++
    ", holes: " ++ rustSlice renderHole query.holes ++
    ", analyses: " ++ rustSlice renderAnalysis query.analyses ++ " }"

private def renderResolution : ResolutionRow → String
  | .preserveFork => "UwueavePreoResolutionV3::PreserveFork"
  | .named id => "UwueavePreoResolutionV3::Named(" ++ rustDecimal id.value ++ ")"

private def renderStatus : StatusShape → String
  | .exact => "UwueavePreoStatusV3::Exact"
  | .provisional => "UwueavePreoStatusV3::Provisional"
  | .forkedClosed => "UwueavePreoStatusV3::ForkedClosed"
  | .forkedOpen => "UwueavePreoStatusV3::ForkedOpen"
  | .absent => "UwueavePreoStatusV3::Absent"
  | .pending => "UwueavePreoStatusV3::Pending"

private def renderVisibility : VisibilityRow → String
  | .inspectable => "UwueavePreoVisibilityV3::Inspectable"
  | .opaque reason =>
      "UwueavePreoVisibilityV3::Opaque(" ++ rustDecimal reason.value ++ ")"

private def renderDisclosure : DisclosureRow → String
  | .shown => "UwueavePreoDisclosureV3::Shown"
  | .hidden reason =>
      "UwueavePreoDisclosureV3::Hidden(" ++ rustDecimal reason.value ++ ")"

private def renderOptionalDisclosure : Option DisclosureRow → String
  | none => "None"
  | some disclosure => "Some(" ++ renderDisclosure disclosure ++ ")"

private def renderResult (result : ResultRow) : String :=
  "UwueavePreoResultV3 { id_decimal: " ++ rustDecimal result.id.value ++
    ", query_id_decimal: " ++ rustDecimal result.query.value ++
    ", future_id_decimal: " ++ rustDecimal result.future.value ++
    ", resolution: " ++ renderResolution result.resolution ++
    ", surface_id_decimal: " ++ rustDecimal result.surface.value ++
    ", status: " ++ renderStatus result.status ++
    ", effect: " ++ rustSlice renderStatus result.effect ++
    ", visibility: " ++ renderVisibility result.visibility ++
    ", disclosure: " ++ renderOptionalDisclosure result.disclosure ++ " }"

private def renderCertificate (certificate : CertificateRow) : String :=
  "UwueavePreoCertificateV3 { id_decimal: " ++ rustDecimal certificate.id.value ++
    ", future_id_decimal: " ++ rustDecimal certificate.future.value ++
    ", world_id_decimal: " ++ rustDecimal certificate.world.value ++ " }"

private def rustTypeDeclarations : List String :=
  ["    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoHoleKindV3 { Field, Opaque }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoHoleV3 { pub path_decimal: &'static [&'static str], pub field_id_decimal: &'static str, pub kind: UwueavePreoHoleKindV3 }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoAnalysisV3 { MergeSafe, MonotoneSafe }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoQueryV3 { pub id_decimal: &'static str, pub schema_id_decimal: &'static str, pub result_id_decimal: &'static str, pub program_id_decimal: &'static str, pub reads_decimal: &'static [&'static str], pub holes: &'static [UwueavePreoHoleV3], pub analyses: &'static [UwueavePreoAnalysisV3] }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoResolutionV3 { PreserveFork, Named(&'static str) }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoStatusV3 { Exact, Provisional, ForkedClosed, ForkedOpen, Absent, Pending }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoVisibilityV3 { Inspectable, Opaque(&'static str) }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub enum UwueavePreoDisclosureV3 { Shown, Hidden(&'static str) }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoResultV3 { pub id_decimal: &'static str, pub query_id_decimal: &'static str, pub future_id_decimal: &'static str, pub resolution: UwueavePreoResolutionV3, pub surface_id_decimal: &'static str, pub status: UwueavePreoStatusV3, pub effect: &'static [UwueavePreoStatusV3], pub visibility: UwueavePreoVisibilityV3, pub disclosure: Option<UwueavePreoDisclosureV3> }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoCertificateV3 { pub id_decimal: &'static str, pub future_id_decimal: &'static str, pub world_id_decimal: &'static str }",
   "    #[derive(Clone, Copy, Debug, PartialEq, Eq)]",
   "    pub struct UwueavePreoProjectionV3 { pub schema: &'static str, pub schema_id_decimal: &'static str, pub base: &'static super::uwueave_preo_projection_v2::UwueavePreoProjectionV2, pub worlds_decimal: &'static [&'static str], pub queries: &'static [UwueavePreoQueryV3], pub results: &'static [UwueavePreoResultV3], pub certificates: &'static [UwueavePreoCertificateV3] }"]

private def rustLookupHelpers : List String :=
  ["    impl UwueavePreoProjectionV3 {",
   "        // Neutral DTO lookup only; callers must not treat a fabricated row as proof authority.",
   "        pub fn query_by_id(&self, id_decimal: &str) -> Option<&'static UwueavePreoQueryV3> { self.queries.iter().find(|row| row.id_decimal == id_decimal) }",
   "        pub fn result_by_id(&self, id_decimal: &str) -> Option<&'static UwueavePreoResultV3> { self.results.iter().find(|row| row.id_decimal == id_decimal) }",
   "        pub fn certificate_by_id(&self, id_decimal: &str) -> Option<&'static UwueavePreoCertificateV3> { self.certificates.iter().find(|row| row.id_decimal == id_decimal) }",
   "        pub fn result_for_query_row(&self, query: &UwueavePreoQueryV3) -> Option<&'static UwueavePreoResultV3> { self.result_by_id(query.result_id_decimal) }",
   "    }"]

private def rustProjectionLines (validated : ValidatedProjectionV3) : List String :=
  let encoding := validated.encoding
  ["    pub static UWUEAVE_PREO_PROJECTION_V3: UwueavePreoProjectionV3 =",
   "        UwueavePreoProjectionV3 {",
   "            schema: UWUEAVE_PREO_PROJECTION_V3_SCHEMA,",
   "            schema_id_decimal: " ++ rustDecimal encoding.schema.value ++ ",",
   "            base: &super::uwueave_preo_projection_v2::UWUEAVE_PREO_PROJECTION_V2,",
   "            worlds_decimal: " ++ rustSlice (fun id => rustDecimal id.value) encoding.worlds ++ ",",
   "            queries: " ++ rustSlice renderQuery encoding.queries ++ ",",
   "            results: " ++ rustSlice renderResult encoding.results ++ ",",
   "            certificates: " ++ rustSlice renderCertificate encoding.certificates ++ ",",
   "        };"]

def renderRustSource (validated : ValidatedProjectionV3) : String :=
  ProjectionV2.renderRustSource validated.validatedBase ++ "\n" ++
    (String.intercalate "\n" <|
      ["// @generated by Uwueave.Preo.ProjectionV3.renderRustSource; do not edit.",
       "// Validated typed-query coordination data only; no proof or permit API.",
       "", "pub mod uwueave_preo_projection_v3 {",
       "    pub const UWUEAVE_PREO_PROJECTION_V3_SCHEMA: &str = " ++
         rustStringLiteral schema ++ ";", ""] ++
      rustTypeDeclarations ++ [""] ++ rustLookupHelpers ++ [""] ++
      rustProjectionLines validated ++ ["}", ""])

def validateAndRender (config : ValidationConfig) (projection : Projection) :
    ValidationResult String :=
  (validate config projection).map renderRustSource

theorem renderRustSource_eq_of_encoding_eq
    {left right : ValidatedProjectionV3} (same : left.encoding = right.encoding) :
    renderRustSource left = renderRustSource right := by
  have baseSame : left.validatedBase.encoding = right.validatedBase.encoding := by
    exact left.base_exact.trans <|
      (congrArg ArtifactV3Encoding.base same).trans right.base_exact.symm
  simp only [renderRustSource]
  rw [ProjectionV2.renderRustSource_eq_of_encoding_eq baseSame]
  simp only [rustProjectionLines]
  rw [same]

theorem validateAndRender_error {config : ValidationConfig} {projection : Projection}
    {error : ValidationError} (refused : validate config projection = .error error) :
    validateAndRender config projection = .error error := by
  rw [validateAndRender, refused]
  rfl

namespace FixtureHooks

def decimal (value : Nat) : String := rustDecimal value
def query (value : QueryRow) : String := renderQuery value
def result (value : ResultRow) : String := renderResult value
def certificate (value : CertificateRow) : String := renderCertificate value

end FixtureHooks

end Uwueave.Preo.ProjectionV3
