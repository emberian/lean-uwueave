import Uwueave.Histories

open Uwueave

theorem debtClosure_U_0063 :
    (∀ (impl : Necessity.Impl Type (ULift.{2} Type))
      (base left right : Type),
      (MergeModel.BaseDecision.selected base).Valid impl left right ↔
        Ancestral.Reachable impl base left ∧
          Ancestral.Reachable impl base right) ∧
    (∀ (b₁ b₂ : Nat),
      (MergeModel.BaseDecision.ambiguous b₁ b₂).bases = [b₁, b₂]) ∧
    (∀ (state : ULift.{2} Type),
      (MergeModel.Decided.mk state (.selected state) state state).under =
        .selected state) := by
  exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ => rfl, fun _ => rfl⟩
