/-
# Uwueave.Preo.ProjectionV2Fixtures — exact V2 generated-source fixtures

The giant budget string equality and its sole `maxRecDepth 10000` allowance
are opt-in. Production imports never elaborate this proof term. This module
imports `ProjectionV2Examples` only to reuse the named zero-profile fixture,
so it is a regression-test surface rather than a production dependency.
-/
import Uwueave.Preo.ProjectionV2Examples

namespace Uwueave.Preo.ProjectionV2

open Uwueave.Preo.Artifact

set_option autoImplicit false

namespace Examples

set_option maxRecDepth 10000 in
theorem renderer_budget_is_v2 :
    FixtureHooks.budget ⟨411, 407, 408, zeroProfile, zeroProfile⟩ =
      "UwueavePreoBudgetV2 { id_decimal: \"411\", session_id_decimal: \"407\", plan_id_decimal: \"408\", limits: &[UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::PeerBarrier, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::ArbiterCut, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::NetworkRound, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::UserPrompt, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::Rollback, value_decimal: \"0\" }], realized_profile: &[UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::PeerBarrier, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::ArbiterCut, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::NetworkRound, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::UserPrompt, value_decimal: \"0\" }, UwueavePreoProfileEntryV2 { currency: UwueavePreoCurrencyV2::Rollback, value_decimal: \"0\" }] }" := by
  rfl

/-- Decimal output is deliberately wider than every Rust machine integer. -/
theorem unbounded_decimal_fixture :
    FixtureHooks.decimal (2 ^ 100) =
      "\"1267650600228229401496703205376\"" := by decide

end Examples

end Uwueave.Preo.ProjectionV2
