import Uwueave.FiniteHistoryProtocol
import Uwueave.ResolvedHistoryGrowth

open Uwueave

universe uPayload uV uS uOp

theorem debtClosure_U_0066 :
    (∀ {Id Payload : Type} {V : Type uV} {S : Type uS} {Op : Type uOp}
      [DecidableEq Id] [DecidableEq Payload]
      {image : FiniteHistoryProtocol.RecordImage Id Payload V S Op}
      {target : List (HistoryRuntime.Event Id Payload)}
      {leftCapacity rightCapacity : Nat}
      {P : HistoryPolicy.HistoryMerge V S Op}
      (left : FiniteHistoryProtocol.SemanticReplica image target leftCapacity)
      (right : FiniteHistoryProtocol.SemanticReplica image target rightCapacity),
      HistoryPolicy.RecordDetermined P → ∀ version : V,
        HistoryPolicy.viewOf P left.history version =
          HistoryPolicy.viewOf P right.history version) ∧
    (∀ {Payload : Type uPayload} [DecidableEq Payload]
      (item : Payload) (rest : List Payload),
      FiniteHistoryProtocol.Covers (item :: item :: rest) (item :: rest)) ∧
    (ResolvedHistoryGrowth.lockParallelAppend.history.Coherent
        Ancestral.lockAM Ancestral.lockOps.impl ∧
      (¬ ∃ base, Histories.LowestCommonBase
        ResolvedHistoryGrowth.lockParallelAppend.history.dag
        ResolvedHistoryGrowth.lockMergeLeft
        ResolvedHistoryGrowth.lockMergeRight base) ∧
      ResolvedHistoryGrowth.lockSecondRound.appended.history.Coherent
        Ancestral.lockAM Ancestral.lockOps.impl ∧
      Ancestral.AtMostOne
        ResolvedHistoryGrowth.lockSecondRound.appended.admission.merged ∧
      ResolvedHistoryGrowth.lockSecondRound.appended.history.origin (.inr ()) =
        .merged (.inl ResolvedHistoryGrowth.lockBaseAlice)
          (.inl ResolvedHistoryGrowth.lockMergeLeft)
          (.inl ResolvedHistoryGrowth.lockMergeRight)) := by
  exact ⟨@FiniteHistoryProtocol.SemanticReplica.view_eq_of_recordDetermined,
    @FiniteHistoryProtocol.Covers.duplicate_head,
    ResolvedHistoryGrowth.lock_two_round_criss_cross_fixture⟩
