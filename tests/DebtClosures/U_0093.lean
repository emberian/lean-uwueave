import Uwueave.FiniteProductSearch

open Uwueave

theorem debtClosure_U_0093 :
    (FiniteProductSearch.synthesizeMinimumLiveSeamCapped
      FiniteProductSearch.slotProtocolScope LiveSegmented.atMostOne
      FiniteProductSearch.slotPalette 0
      FiniteProductSearch.generousLimits).isReady = true ∧
    LiveSegmented.LeastSuch
      (LiveSegmented.LiveWidth LiveSegmented.slotProtocol
        LiveSegmented.atMostOne) 2 ∧
    (FiniteProductSearch.synthesizeMinimumLiveSeamCapped
      FiniteProductSearch.slotProtocolScope LiveSegmented.atMostOne
      FiniteProductSearch.slotPalette 0
      FiniteProductSearch.tinyLimits).refusalAxis? =
        some FiniteProductSearch.LimitAxis.states := by
  exact ⟨FiniteProductSearch.slot_live_minimum_cap_is_admitted,
    FiniteProductSearch.slot_exact_width_certificates.1,
    by decide⟩
