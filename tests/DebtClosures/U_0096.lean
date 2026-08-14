import Uwueave.MenuTotality

open Uwueave
open Uwueave.Segmented
open Uwueave.MenuTotality

theorem debtClosure_U_0096 :
    (forall {S Seg : Type} [DecidableEq S] [MergeState S] [DecidableEq Seg]
      (I : Invariant S) [DecidablePred I]
      (V : List S) (hV : forall s : S, s ∈ V) (C : List Seg) (fallback : Seg),
      match minimumMenuSynthesis I V hV C fallback with
      | .found row =>
          SeamColoring.LeastSuch (SeamColoring.FiniteWidth I V C)
            (SeamColoring.usedColorCount V C row.minimum.seam)
      | .refused _ => forall σ, SeamColoring.UsesOnly V C σ →
          ¬ SegmentedIConfluent σ I) ∧
    pinMinimumMenuRow.entry.exit
        = Exits.Exit.seam Bool SeamColoring.pinMinimum.seam 0
      ∧ pinMinimumMenuRow.entry.exit.Applies Cost.pinInv
      ∧ SeamColoring.usedColorCount SeamColoring.pinStates [false, true]
          SeamColoring.pinMinimum.seam = 2
      ∧ SeamColoring.LeastSuch
          (SeamColoring.FiniteWidth Cost.pinInv SeamColoring.pinStates [false, true]) 2
      ∧ minimumCeilingMenu.prices = [0, 0, 2] := by
  exact ⟨fun I _ V hV C fallback => minimumMenuSynthesis_total I V hV C fallback,
    pin_minimum_menu_is_exact⟩
