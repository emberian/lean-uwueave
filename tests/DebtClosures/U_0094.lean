import Uwueave.MenuTotality
import Uwueave.FiniteProductClosure

open Uwueave
open Uwueave.FiniteProductSearch
open Uwueave.FiniteProductClosure
open Uwueave.MenuTotality

theorem debtClosure_U_0094 :
    (MenuTotality.synth Cost.pinInv SeamColoring.pinStates
      SeamColoring.pinStates_complete).isSome = true ∧
    (Cost.emptyPin ≠ SeamColoring.pinF
      ∧ SeamColoring.greedySeamFor Cost.pinInv SeamColoring.pinStates Cost.emptyPin
          = SeamColoring.greedySeamFor Cost.pinInv SeamColoring.pinStates
              SeamColoring.pinF) ∧
    (Cost.crossings (SeamColoring.greedySeamFor Cost.pinInv SeamColoring.pinStates)
          Cost.pinStep Cost.emptyPin [false] = 0
      ∧ Cost.crossings (fun s : Cost.PinSet => s) Cost.pinStep Cost.emptyPin [false]
          = 1) ∧
    (fourTokenClosedScope.synthesizeCoupledCapped fixtureCoupling
      generousLimits).isReady = true ∧
    (synthesizeProduct fixtureCoupledProblem).isFound = true ∧
    (fourTokenClosedScope.synthesizeCoupledCapped fixtureCoupling
      tinyLimits).refusalAxis? = some .products ∧
    (synthesizeMinimumGlobalSeamCapped pinCarrier Cost.pinInv [false, true]
      false generousLimits).isReady = true ∧
    (match synthesizeMinimumGlobalSeamCapped pinCarrier Cost.pinInv [false, true]
        false generousLimits with
      | .ready result => result.isFound = true
      | .tooLarge .. => False) := by
  exact ⟨MenuTotality.synth_pin_isSome,
    MenuTotality.pin_synth_is_non_trivial,
    MenuTotality.pin_synth_beats_full_coordination,
    by decide,
    coupled_product_finds_a_compatible_pair,
    coupled_product_resource_refusal_precedes_enumeration,
    by decide,
    by
      change (synthesizeStrategy pinCarrier [false, true] false
        (fun strategy => Segmented.SegmentedIConfluent strategy Cost.pinInv)
        (fun strategy => decideGlobalSegmented pinCarrier strategy Cost.pinInv)).isFound
          = true
      decide⟩
