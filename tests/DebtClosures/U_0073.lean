import Uwueave.HistoryBase

open Uwueave Uwueave.Ancestral Uwueave.Histories
open Uwueave.HistoryBase

/-! U-0073 reuses U-0069's exact classifier and treats the original lock/counter
pair as its positive and negative acceptance cases. -/

theorem debtClosure_U_0073 :
    ((MergeModel.BaseDecision.ambiguous (lvState .alice) (lvState .bob)).Valid
        lockImpl (lvState .m1) (lvState .m2)
      ∧ lockAM.merge3 (lvState .alice) (lvState .m1) (lvState .m2) =
        lockAM.merge3 (lvState .bob) (lvState .m1) (lvState .m2)
      ∧ (∀ b₁ b₂ : Nat,
        ¬ (MergeModel.BaseDecision.ambiguous b₁ b₂).Valid
          (spendOps 2).impl (ccState .mergeL) (ccState .mergeR))
      ∧ counterAM.merge3 (ccState .left) (ccState .mergeL) (ccState .mergeR) ≠
        counterAM.merge3 (ccState .right) (ccState .mergeL) (ccState .mergeR)) ∧
    lockAmbiguityClassifier.classify lockAmbiguityProbe = ⟨true, true⟩ ∧
    counterAmbiguityClassifier.classify counterAmbiguityProbe =
      ⟨false, false⟩ :=
  ⟨ambiguity_is_visible_where_it_is_free,
   ambiguity_classifier_acceptance_cases⟩

#print axioms debtClosure_U_0073
