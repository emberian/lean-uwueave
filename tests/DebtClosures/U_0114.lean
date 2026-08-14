import Uwueave.FiniteThresholdSummary

open Uwueave
open Uwueave.FiniteThresholdSummary

universe u

theorem debtClosure_U_0114 :
    (∀ {alpha : Type u} [DecidableEq alpha]
      (U : FiniteUniverse alpha) (k : Nat),
      (U.classKeys k).Nodup ∧
        (∀ left right : Catalog.GSet alpha,
          CtxEquiv (U.threshold k) left right ↔
            U.classKey k left = U.classKey k right) ∧
        (∀ key, key ∈ U.classKeys k ↔
          ∃ state : Catalog.GSet alpha, U.classKey k state = key) ∧
        (U.classKeys k).length =
          if U.Degenerate k then 1
          else
            ((FiniteProductSearch.subsets U.values).filter
              (fun choice => decide (choice.length < k))).length + 1) ∧
    (finUniverse 2).thresholdClassCount 1 = 2 ∧
    (finUniverse 3).thresholdClassCount 2 = 5 ∧
    ((finUniverse 2).thresholdClassCount 1 =
        FiniteSummaryCodec.classCount FiniteSummaryCodec.Fixtures.membership ∧
      (finUniverse 3).thresholdClassCount 2 =
        FiniteSummaryCodec.classCount
          FiniteSummaryCodec.Fixtures.thresholdTwo) := by
  exact ⟨fun U k =>
      ⟨U.classKeys_nodup k, U.ctxEquiv_iff_classKey_eq k,
        U.mem_classKeys_iff k, U.classKeys_length_explicit k⟩,
    two_class_corollary,
    five_class_corollary,
    existing_counts_are_corollaries⟩
