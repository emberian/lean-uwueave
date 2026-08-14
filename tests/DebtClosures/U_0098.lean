import Uwueave.MenuTotality

open Uwueave
open Uwueave.Catalog
open Uwueave.Segmented
open Uwueave.SeamColoring
open Uwueave.MenuTotality

universe u v w

theorem debtClosure_U_0098 :
    (∀ {S : Type u} {Seg : Type v} [MergeState S] [DecidableEq Seg]
      {I : Invariant S} {σ : S → Seg} {K : List S} {C : List Seg},
      SegmentedIConfluent σ I → Clique I K →
        (∀ x ∈ K, σ x ∈ C) → K.length ≤ C.length) ∧
    (∀ {S : Type u} {Seg : Type v} {Op : Type w}
      [MergeState S] [DecidableEq Seg] {σ : S → Seg} {I : Invariant S}
      {step : S → Op → S} {s : S}, SegmentedIConfluent σ I →
      ∀ ws : List (List Op), Clique I (ws.map (Cost.run step s)) →
        ws.length ≤ jointCost σ step s ws + 1) ∧
    (∀ {S : Type u} {Seg : Type v} {Op : Type w}
      [MergeState S] [DecidableEq Seg] {σ : S → Seg} {I : Invariant S}
      {step : S → Op → S} {s : S}, SegmentedIConfluent σ I →
      ∀ ws : List (List Op), Clique I (ws.map (Cost.run step s)) →
        ws.length - 1 ≤ jointCost σ step s ws) ∧
    (∀ (k : Nat) {Seg : Type v} [DecidableEq Seg] (σ : GSet Nat → Seg),
      SegmentedIConfluent σ atMostOne →
        k - 1 ≤ jointCost σ addStep emptySet (replicaStreams k)) ∧
    (∀ k : Nat,
      (∀ bs : List (List Nat), Cost.ClashBlocks atMostOne addStep emptySet bs →
          bs.length = 0) ∧
      ∀ {Seg : Type} [DecidableEq Seg] (σ : GSet Nat → Seg),
        SegmentedIConfluent σ atMostOne →
          k - 1 ≤ jointCost σ addStep emptySet (replicaStreams k)) := by
  exact
    ⟨fun hseg hK hC => clique_forces_colors hseg hK hC,
      fun hseg ws hK => clique_forces_joint_crossings hseg ws hK,
      fun hseg ws hK => clique_joint_floor hseg ws hK,
      fun k _ _ σ hseg => atMostOne_replica_floor k σ hseg,
      fun k => the_clique_floor_is_invisible_to_the_block_calculus k⟩
