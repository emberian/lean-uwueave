import Uwueave.RepairMenu

open Uwueave

universe v

theorem debtClosure_U_0046 :
    (∀ {S : Type} [MergeState S] {I : Invariant S}
        (c : MenuTotality.CertifiedSeam I) {Seg' : Type v}
        [DecidableEq Seg'] (tau : S → Seg')
        (_hTau : Segmented.SegmentedIConfluent tau I),
      c.toExit.price ≤
        SeamColoring.jointCost tau c.step c.start c.streams)
      ∧ (∀ {P : Repair.Promise} (Seg : Type) (sigma : P.State → Seg)
        (hSigma : Segmented.SegmentedIConfluent sigma P.inv)
        (floor : RepairMenu.SeamFloor P) {Seg' : Type v}
        [DecidableEq Seg'] (tau : P.State → Seg')
        (_hTau : Segmented.SegmentedIConfluent tau P.inv),
      (RepairMenu.seamRepair P Seg sigma hSigma floor).price.seamCrossings ≤
        SeamColoring.jointCost tau floor.step floor.start floor.streams)
      ∧ ((Exits.Exit.seam (S := Cost.PinSet) Bool
          (fun state => state false) 5).Applies Cost.pinInv
        ∧ ¬ ((Exits.Exit.seam (S := Cost.PinSet) Bool
            (fun state => state false) 5).price ≤
          Cost.crossings (fun state : Cost.PinSet => state false)
            Cost.pinStep Cost.emptyPin [true]))
      ∧ (MenuTotality.ceilingCertificate.floor = 1
        ∧ MenuTotality.ceilingCertificate.toExit.price = 1
        ∧ ∀ {Seg : Type} [DecidableEq Seg] (tau : Cost.PinSet → Seg),
          Segmented.SegmentedIConfluent tau Cost.pinInv →
            1 ≤ SeamColoring.jointCost tau Cost.pinStep Cost.emptyPin
              [[true], [false]]) := by
  exact ⟨MenuTotality.CertifiedSeam.floor_is_forced,
    RepairMenu.seamRepair_price_is_forced,
    MenuTotality.applies_certifies_no_floor,
    MenuTotality.ceiling_certificate_floor_is_forced⟩
