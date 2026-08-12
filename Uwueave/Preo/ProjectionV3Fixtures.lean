/-
# Uwueave.Preo.ProjectionV3Fixtures — exact V3 renderer goldens

Exact row strings are intentionally small.  The full deterministic source is
compiled by the Rust fixture gate rather than repeated as a giant Lean string,
avoiding the max-recursion and proof-term blowups previously isolated from V1
and V2 production imports.
-/
import Uwueave.Preo.ProjectionV3Examples

namespace Uwueave.Preo.ProjectionV3.Examples

set_option maxRecDepth 4000 in

theorem query_rust_golden : FixtureHooks.query fullQuery =
    "UwueavePreoQueryV3 { id_decimal: \"1002\", schema_id_decimal: \"1000\", result_id_decimal: \"1003\", program_id_decimal: \"1004\", reads_decimal: &[\"402\"], holes: &[UwueavePreoHoleV3 { path_decimal: &[\"0\"], field_id_decimal: \"402\", kind: UwueavePreoHoleKindV3::Field }], analyses: &[UwueavePreoAnalysisV3::MergeSafe, UwueavePreoAnalysisV3::MonotoneSafe] }" := by
  rfl

set_option maxRecDepth 4000 in
theorem result_rust_golden : FixtureHooks.result fullResult =
    "UwueavePreoResultV3 { id_decimal: \"1003\", query_id_decimal: \"1002\", future_id_decimal: \"404\", resolution: UwueavePreoResolutionV3::PreserveFork, surface_id_decimal: \"1005\", status: UwueavePreoStatusV3::Exact, effect: &[UwueavePreoStatusV3::Exact], visibility: UwueavePreoVisibilityV3::Inspectable, disclosure: Some(UwueavePreoDisclosureV3::Shown) }" := by
  rfl

theorem certificate_rust_golden : FixtureHooks.certificate fullCertificate =
    "UwueavePreoCertificateV3 { id_decimal: \"1006\", future_id_decimal: \"404\", world_id_decimal: \"1001\" }" := by
  rfl

theorem full_renderer_accepts :
    (validateAndRender config fullProjection).isOk = true := by
  unfold validateAndRender
  cases accepted : validate config fullProjection with
  | error error =>
      have valid := full_validates
      rw [accepted] at valid
      contradiction
  | ok validated =>
      rfl

end Uwueave.Preo.ProjectionV3.Examples
