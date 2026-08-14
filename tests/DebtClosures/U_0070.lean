import Uwueave.HistoryBase

open Uwueave Uwueave.Histories

universe uV uS uOp

/-! History-level ambiguity is evidence of two distinct maximal common bases,
not a failed search.  It therefore rules out every lowest common base. -/

theorem debtClosure_U_0070 :
    (∀ {V : Type uV} {S : Type uS} {Op : Type uOp}
      {H : History V S Op} {x y first second : V},
      HistoryBase.ValidInHistory H x y (.ambiguous first second) →
        ¬ ∃ base, LowestCommonBase H.dag x y base) ∧
    ¬ ∃ base, LowestCommonBase ccDag .mergeL .mergeR base := by
  constructor
  · intro V S Op H x y first second ambiguous
    exact ambiguous_excludes_lowest ambiguous.1 ambiguous.2.1 ambiguous.2.2
  · exact cc_no_lowest
