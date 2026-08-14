import Uwueave.MenuTotality

open Uwueave
open Uwueave.MenuTotality

theorem debtClosure_U_0101 :
    (synth Cost.pinInv SeamColoring.pinStates SeamColoring.pinStates_complete).isSome
        = true ∧
    (Cost.emptyPin ≠ SeamColoring.pinF
      ∧ SeamColoring.greedySeamFor Cost.pinInv SeamColoring.pinStates Cost.emptyPin
          = SeamColoring.greedySeamFor Cost.pinInv SeamColoring.pinStates
              SeamColoring.pinF) ∧
    (Cost.crossings (SeamColoring.greedySeamFor Cost.pinInv SeamColoring.pinStates)
          Cost.pinStep Cost.emptyPin [false] = 0
      ∧ Cost.crossings (fun s : Cost.PinSet => s) Cost.pinStep Cost.emptyPin [false]
          = 1) := by
  exact ⟨synth_pin_isSome, pin_synth_is_non_trivial,
    pin_synth_beats_full_coordination⟩
