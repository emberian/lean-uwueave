import Uwueave.FiniteProductClosure

open Uwueave
open Uwueave.Preo.Planning
open Uwueave.FiniteProductClosure

theorem debtClosure_U_0100 :
    (∀ (space : BoolQuotaSpace) (partition : BoolQuotaPartition space.budget),
      partition ∈ space.eligiblePartitions ↔ space.NonStarving partition) ∧
    (∀ (space : BoolQuotaSpace) (idOffset : Nat)
      (partition : BoolQuotaPartition space.budget),
      space.NonStarving partition →
        partitionCandidate space idOffset partition ∈
          (eligibleCatalog space idOffset).entries) ∧
    (∀ (space : BoolQuotaSpace) (idOffset : Nat)
      (candidate : RepairSynthesis.Candidate (sharedBudgetPromise space.budget)),
      candidate ∈ (eligibleCatalog space idOffset).entries ↔
        ∃ partition : BoolQuotaPartition space.budget,
          space.NonStarving partition ∧
          partitionCandidate space idOffset partition = candidate) ∧
    (admitCatalog fourTokenInput 100).isReady = true ∧
    fourTokenCatalogResult.isFound = true ∧
    (fourTokenClosedScope.synthesizeCatalogCapped zeroValuation
      FiniteProductSearch.tinyLimits).refusalAxis? = some .products ∧
    (FiniteProductSearch.synthesizeProduct fixtureCoupledProblem).isFound = true := by
  exact ⟨BoolQuotaSpace.mem_eligiblePartitions_iff,
    partition_mem_eligibleCatalog,
    mem_eligibleCatalog_iff,
    four_token_catalog_is_admitted,
    four_token_catalog_finds_a_generated_repair,
    closed_catalog_resource_refusal_precedes_search,
    coupled_product_finds_a_compatible_pair⟩
