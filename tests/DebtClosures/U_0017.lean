import Uwueave.FiniteProductSearch

open Uwueave

universe u

theorem debtClosure_U_0017 :
    (∀ {α : Type u} [DecidableEq α]
        {carrier : FiniteProductSearch.Carrier α}
        {R : α → α → Bool}
        (maximum : FiniteProductSearch.MaximumClique carrier R)
        (_hsymmetric : ∀ {left right},
          R left right = true → R right left = true)
        (other : List α) (_hnodup : other.Nodup)
        (_hsupported : ∀ value ∈ other, value ∈ carrier.values)
        (_hclique : FiniteProductSearch.FiniteClique
          (fun left right => R left right = true) other),
      other.length ≤ maximum.vertices.length) ∧
    FiniteProductSearch.synthesizeMaximumCliqueCapped
        FiniteProductSearch.c5Carrier Uwueave.ClashGraph.c5Adjacent
        FiniteProductSearch.generousLimits =
      .ready FiniteProductSearch.c5CliqueResult ∧
    FiniteProductSearch.c5MaximumSize? = some 2 := by
  exact
    ⟨fun maximum hsymmetric other hnodup hsupported hclique =>
      maximum.greatestSupported hsymmetric other hnodup hsupported hclique,
      rfl,
      FiniteProductSearch.c5_maximum_clique_is_two⟩
