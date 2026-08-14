import Uwueave.FiniteProductClosure

open Uwueave
open Uwueave.Preo.Planning
open Uwueave.FiniteProductClosure

theorem debtClosure_U_0095 :
    (∀ (space : BoolQuotaSpace) (partition : BoolQuotaPartition space.budget),
      partition ∈ space.eligiblePartitions ↔ space.NonStarving partition) ∧
    (∀ (space : BoolQuotaSpace) (policy : BoolQuotaPolicy space),
      (synthesizePartition space policy).partition ∈ space.eligiblePartitions ∧
      space.NonStarving (synthesizePartition space policy).partition ∧
      ∀ other ∈ space.eligiblePartitions,
        policy.score (synthesizePartition space policy).partition ≤
          policy.score other) ∧
    (synthesizePartition fourTokenSpace
      (balancedPolicy fourTokenSpace)).partition.left.val = 2 ∧
    ∀ partition : BoolQuotaPartition tooSmallInput.budget,
      ¬ (0 < partition.allocation true ∧
        0 < partition.allocation false) := by
  exact ⟨BoolQuotaSpace.mem_eligiblePartitions_iff,
    fun space policy =>
      ⟨(synthesizePartition space policy).member,
        (synthesizePartition space policy).nonStarving,
        (synthesizePartition space policy).least⟩,
    four_token_balanced_selection,
    one_token_refusal_is_exhaustive⟩
