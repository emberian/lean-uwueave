import Uwueave.CoordEffect

open scoped Uwueave.CoordEffect

universe u

theorem debtClosure_U_0006 :
    (∀ {X : Type u} (A : Uwueave.CoordEffect.Admissible X)
        (P Q : Uwueave.CoordEffect.Profile X),
      Uwueave.CoordEffect.optimum A (P ⊗ Q) ≥
        Uwueave.CoordEffect.optimum A P + Uwueave.CoordEffect.optimum A Q) ∧
    (∀ {X : Type u} (A : Uwueave.CoordEffect.Admissible X)
        (P Q : Uwueave.CoordEffect.Profile X) {x : X},
      x ∈ A.toList →
      P x = Uwueave.CoordEffect.optimum A P →
      Q x = Uwueave.CoordEffect.optimum A Q →
      Uwueave.CoordEffect.optimum A (P ⊗ Q) =
        Uwueave.CoordEffect.optimum A P + Uwueave.CoordEffect.optimum A Q) ∧
    (Uwueave.CoordEffect.optimum Uwueave.CoordEffect.pinSpace
          Uwueave.CoordEffect.pinTrueProfile +
        Uwueave.CoordEffect.optimum Uwueave.CoordEffect.pinSpace
          Uwueave.CoordEffect.pinFalseProfile <
      Uwueave.CoordEffect.optimum Uwueave.CoordEffect.pinSpace
        (Uwueave.CoordEffect.pinTrueProfile ⊗ Uwueave.CoordEffect.pinFalseProfile)) := by
  exact
    ⟨fun A P Q => Uwueave.CoordEffect.opt_compose_ge_sum_opt A P Q,
      fun A P Q x hx hP hQ =>
        Uwueave.CoordEffect.opt_compose_eq_sum_opt_of_common_optimum
          A P Q hx hP hQ,
      Uwueave.CoordEffect.pin_opt_compose_strict⟩
