import Uwueave.HistoryPolicy

open Uwueave

theorem debtClosure_U_0077 :
    (∀ (P : HistoryPolicy.HistoryMerge Nat (Catalog.GSet Type)
        (ULift.{2} Type))
      (H : Histories.History Nat (Catalog.GSet Type) (ULift.{2} Type))
      (x y : Nat),
      (P.apply H x y).under = P.decisionAt H x y) ∧
    (∀ {P : HistoryPolicy.HistoryMerge Nat (Catalog.GSet Type)
        (ULift.{2} Type)},
      HistoryPolicy.RecordDetermined P →
        HistoryPolicy.HistoryConvergent P) := by
  exact ⟨HistoryPolicy.apply_under,
    HistoryPolicy.recordDetermined_converges⟩
