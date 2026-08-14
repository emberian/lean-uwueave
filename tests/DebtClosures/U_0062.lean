import Uwueave.Histories

open Uwueave

/-! The version, state, and operation carriers below live respectively in
`Type 0`, `Type 1`, and `Type 2`.  The conclusion crosses the full history-to-
`MergeModel.BaseDecision.Valid` bridge; it is not merely a type-formation
probe. -/
theorem debtClosure_U_0062 :
    ∀ (H : Histories.History Nat Type (ULift.{2} Type))
      (impl : Necessity.Impl Type (ULift.{2} Type))
      (_hrr : Histories.RunRealized H impl)
      (x y b₁ b₂ : Nat),
      Histories.CommonAncestor H.dag x y b₁ →
      Histories.MaximalCommonBase H.dag x y b₁ →
      Histories.MaximalCommonBase H.dag x y b₂ →
      H.state b₁ ≠ H.state b₂ →
      (MergeModel.BaseDecision.selected (H.state b₁)).Valid
          impl (H.state x) (H.state y) ∧
        (MergeModel.BaseDecision.ambiguous (H.state b₁) (H.state b₂)).Valid
          impl (H.state x) (H.state y) := by
  intro H impl hrr x y b₁ b₂ hcommon hmax₁ hmax₂ hstates
  exact ⟨Histories.selected_valid hrr hcommon,
    Histories.ambiguous_valid hrr hmax₁ hmax₂ hstates⟩
