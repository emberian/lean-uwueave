import Uwueave.WorldFuture

open Uwueave

universe u

theorem debtClosure_U_0159 :
    (∀ spec : WorldFuture.FiniteDeliverySpec.Spec Holes.Val,
      WorldFuture.FiniteDeliverySpec.stateIndexedSafeB spec = true ↔
        WorldFuture.FiniteDeliverySpec.HasStateIndexedDeliveryWithin spec) ∧
    WorldFuture.FiniteDeliverySpec.stateIndexedSafeB
      WorldFuture.FiniteDeliverySpec.singletonQuiescedSpec = true ∧
    (∀ (spec : WorldFuture.FiniteDeliverySpec.Spec Holes.Val),
      WorldFuture.FiniteDeliverySpec.Covers spec →
        (WorldFuture.FiniteDeliverySpec.stateIndexedSafeB spec = true ↔
          ∃ F : Evidence.Future (Evidence.ResultEvidence Holes.Val),
            ∀ x y : WorldFuture.World Holes.Val,
              WorldFuture.DeliveryFuture x y ↔
                F (WorldFuture.observe x) (WorldFuture.observe y))) := by
  exact ⟨WorldFuture.FiniteDeliverySpec.stateIndexedSafeB_eq_true_iff,
    WorldFuture.FiniteDeliverySpec.singleton_quiesced_classifier_accepts,
    WorldFuture.FiniteDeliverySpec.stateIndexedSafeB_global_iff⟩
