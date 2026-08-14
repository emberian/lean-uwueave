import Uwueave.HistoryBase

open Uwueave

theorem debtClosure_U_0068 :
    (∀ {H : Histories.History Nat Type (ULift.{2} Type)} {x y : Nat},
      (∀ b₁ b₂ b,
        HistoryBase.ValidInHistory H x y (.ambiguous b₁ b₂) →
          ¬ HistoryBase.ValidInHistory H x y (.selected b)) ∧
      (∀ b, HistoryBase.ValidInHistory H x y .unavailable →
        ¬ HistoryBase.ValidInHistory H x y (.selected b))) ∧
    (∀ (B : HistoryBase.BasedWorld Type Nat)
      {C : WorldFuture.WorldCert Type},
      WorldFuture.WorldCertSound C →
        HistoryBase.VersionCertSound B (fun v => C (B.world v))) := by
  exact ⟨@HistoryBase.validInHistory_exclusive Nat Type (ULift.{2} Type),
    HistoryBase.versionCertSound_of_worldCertSound⟩
