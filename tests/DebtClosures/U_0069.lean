import Uwueave.HistoryBase

open Uwueave Uwueave.Ancestral Uwueave.Histories
open Uwueave.HistoryBase

/-! U-0069 closes only the explicitly covered lock and counter scopes.  The
evidence below requires both coverage proofs, both semantic iff theorems, and
the computed positive/negative verdicts. -/

theorem debtClosure_U_0069 :
    (∀ p, lockAmbiguityScope p ↔ p ∈ lockAmbiguityClassifier.probes) ∧
    (∀ p, counterAmbiguityScope p ↔
      p ∈ counterAmbiguityClassifier.probes) ∧
    (lockAmbiguityClassifier.classify lockAmbiguityProbe = ⟨true, true⟩ ↔
      StateAmbiguityVisible lockHistory lockImpl lockAmbiguityProbe ∧
        DerivedViewAgreement lockHistory lockAM (fun s : Ancestral.Lock => s)
          lockAmbiguityProbe) ∧
    (counterAmbiguityClassifier.classify counterAmbiguityProbe =
        ⟨false, false⟩ ↔
      ¬ StateAmbiguityVisible ccHistory (spendOps 2).impl counterAmbiguityProbe ∧
        ¬ DerivedViewAgreement ccHistory counterAM (fun n : Nat => n)
          counterAmbiguityProbe) ∧
    (lockAmbiguityClassifier.correlatesB lockAmbiguityProbe = true ↔
      (StateAmbiguityVisible lockHistory lockImpl lockAmbiguityProbe ↔
        DerivedViewAgreement lockHistory lockAM (fun s : Ancestral.Lock => s)
          lockAmbiguityProbe)) ∧
    (counterAmbiguityClassifier.correlatesB counterAmbiguityProbe = true ↔
      (StateAmbiguityVisible ccHistory (spendOps 2).impl counterAmbiguityProbe ↔
        DerivedViewAgreement ccHistory counterAM (fun n : Nat => n)
          counterAmbiguityProbe)) ∧
    lockAmbiguityClassifier.classify lockAmbiguityProbe = ⟨true, true⟩ ∧
    counterAmbiguityClassifier.classify counterAmbiguityProbe =
      ⟨false, false⟩ :=
  ⟨lockAmbiguityClassifier.covers, counterAmbiguityClassifier.covers,
   lock_ambiguity_classifier_iff, counter_ambiguity_classifier_iff,
   lockAmbiguityClassifier.correlatesB_eq_true_iff rfl,
   counterAmbiguityClassifier.correlatesB_eq_true_iff rfl,
   ambiguity_classifier_acceptance_cases⟩

#print axioms debtClosure_U_0069
