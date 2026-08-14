import Uwueave.FiniteProductSearch

open Uwueave

universe u v

theorem debtClosure_U_0018 :
    (∀ {S : Type u} {Op : Type v} [MergeState S] [DecidableEq S]
        {scope : FiniteProductSearch.ProtocolScope S Op}
        {I : Invariant S} [DecidablePred I]
        (maximum : FiniteProductSearch.MaximumLiveClique scope I)
        (otherBase : S) (_hbase : otherBase ∈ scope.states.values)
        (otherWorlds : List S) (_hnodup : otherWorlds.Nodup)
        (_hsupported : ∀ value ∈ otherWorlds,
          value ∈ scope.states.values)
        (_hclique : CliqueLive.LiveClique scope.runModel I
          otherBase otherWorlds),
      otherWorlds.length ≤ maximum.worlds.length) ∧
    FiniteProductSearch.synthesizeMaximumLiveCliqueCapped
        FiniteProductSearch.slotProtocolScope LiveSegmented.atMostOne
        FiniteProductSearch.generousLimits =
      .ready (FiniteProductSearch.synthesizeMaximumLiveClique
        FiniteProductSearch.slotProtocolScope LiveSegmented.atMostOne) ∧
    FiniteProductSearch.slotScenarioCliqueMaximum? = some 2 := by
  exact
    ⟨fun maximum otherBase hbase otherWorlds hnodup hsupported hclique =>
      maximum.greatestSupported otherBase hbase otherWorlds hnodup
        hsupported hclique,
      rfl,
      FiniteProductSearch.slot_exact_maximum_scenario_clique_is_two⟩
