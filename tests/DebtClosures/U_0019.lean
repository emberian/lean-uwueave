import Uwueave.CoordEffect
import Uwueave.Preo.ProtocolSurface

open scoped Uwueave.CoordEffect
open Uwueave
open Uwueave.CoordEffect
open Uwueave.Preo.ProtocolSurface

universe u v w z

theorem debtClosure_U_0019 :
    (NativeFixture.Session.crossings = 2 ∧
      NativeFixture.Session.obligations.length = 5) ∧
    Profile.subsumesB pinSpace pinTrueProfile
        (pinTrueProfile ⊗ pinFalseProfile) = true ∧
    Profile.subsumesB pinSpace
        (pinTrueProfile ⊗ pinFalseProfile) (Profile.zero _) = false ∧
    (∀ {X : Type u} (A : Admissible X) (required allowed : Profile X),
      Profile.subsumesB A required allowed = true →
        optimum A required ≤ optimum A allowed) ∧
    (∀ {S : Type u} {Seg : Type v} {T : Type w} {Op : Type z}
      [DecidableEq Seg] [DecidableEq T]
      {coarse : S → Seg} {fine : S → T},
      Uwueave.SeamAlgebra.Finer fine coarse →
        ∀ (step : S → Op → S) (work : List Op),
          (runProfile coarse step work).Subsumes
            (runProfile fine step work)) ∧
    (∀ {S : Type u} {Seg : Type v} {T : Type w} [MergeState S]
      {I : Invariant S} (coarse : Strategy I Seg) (fine : S → T)
      (hfiner : Uwueave.SeamAlgebra.Finer fine coarse.seam)
      (hstable : Uwueave.SeamAlgebra.SeamStableOn I fine),
      ∃ refined : Strategy I T,
        refined = refinedStrategy coarse fine hfiner hstable ∧
        refined.seam = fine) := by
  exact ⟨native_fixture_exact_shape,
    pin_true_subsumes_session_checked,
    pin_session_subsumes_zero_checked_false,
    fun A required allowed hchecked =>
      optimum_mono_of_subsumesOn A
        ((Profile.subsumesB_eq_true_iff A required allowed).1 hchecked),
    fun hfiner step work => runProfile_subsumes_of_finer hfiner step work,
    fun coarse fine hfiner hstable =>
      ⟨refinedStrategy coarse fine hfiner hstable, rfl, rfl⟩⟩

#check Uwueave.CoordEffect.runProfile_subsumes_of_finer
#check Uwueave.CoordEffect.refinedStrategy
#print axioms debtClosure_U_0019
