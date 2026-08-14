import Uwueave.ForkGrade

theorem debtClosure_U_0002 :
    (Uwueave.ForkGrade.liveOptimum Uwueave.ForkGrade.growSpace = 0 →
      ¬ Uwueave.ForkGrade.LiveClash Uwueave.ForkGrade.growInv
        Uwueave.Cost.pinStep Uwueave.ForkGrade.growScenario) ∧
    ((¬ Uwueave.ForkGrade.LiveClash Uwueave.ForkGrade.growInv
        Uwueave.Cost.pinStep Uwueave.ForkGrade.growScenario) →
      Uwueave.ForkGrade.liveOptimum Uwueave.ForkGrade.growSpace = 0) := by
  have hiff :=
    Uwueave.ForkGrade.liveScenario_optimum_eq_zero_iff_no_live_clash
      0 Uwueave.ForkGrade.growSpace (fun _ => Uwueave.ForkGrade.growSpace.head_mem)
  exact ⟨hiff.mp, hiff.mpr⟩
