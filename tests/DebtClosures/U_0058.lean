import Uwueave.GluingExtensions

open Uwueave Uwueave.Catalog Uwueave.Gluing Uwueave.GluingExtensions

universe u v

/-- Independently reviewable keyed-family obligation, with opposite concrete
per-key verdicts. -/
theorem debtClosure_U_0058_keyed :
    (∀ {K : Type v} {S : Type u} [MergeState S]
      (family : KeyedFamily K S),
      (∀ key, Spanning (family key)) → Nonempty (KeyedVerdicts family)) ∧
    HoleVerdict.isGlued (exampleVerdicts false) = true ∧
    HoleVerdict.isGlued (exampleVerdicts true) = false := by
  exact ⟨fun family spanning => ⟨keyedVerdictsOfSpanning family spanning⟩,
    example_anchor_is_glued, example_exclusive_is_clash⟩

/-- Independently reviewable computed dual-H¹ obligation, with both classes
and a separating pair. -/
theorem debtClosure_U_0058_dualH1 :
    (∀ left right : TriangleCochain,
      Cohomologous left right ↔ dualH1 left = dualH1 right) ∧
    (∀ gauge : TriangleGauge, dualH1 (coboundary gauge) = false) ∧
    dualH1 trivialCochain = false ∧
    dualH1 obstructedCochain = true ∧
    ¬ Cohomologous trivialCochain obstructedCochain := by
  exact ⟨cohomologous_iff_dualH1_eq, coboundary_dualH1_zero,
    trivial_dualH1, obstructed_dualH1, two_distinct_dualH1_classes⟩

/-- Independently reviewable provenance obligation: both contributors survive,
the state projection is the old glue, and a concrete stranger is absent. -/
theorem debtClosure_U_0058_provenance :
    (∀ {Actor : Type v} [DecidableEq Actor]
      {S : Type u} [MergeState S] (x y : S)
      (left right : ProvenancedFill Actor S),
      (glueProvenanced x y left right).2 left.author = true ∧
      (glueProvenanced x y left right).2 right.author = true ∧
      (glueProvenanced x y left right).1 =
        (x ⊔ left.patch) ⊔ (y ⊔ right.patch)) ∧
    (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 0 = true ∧
    (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 1 = true ∧
    (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 2 = false := by
  exact ⟨fun x y left right =>
      ⟨glueProvenanced_observes_left x y left right,
        glueProvenanced_observes_right x y left right,
        glueProvenanced_state x y left right⟩,
    two_authors_and_no_stranger⟩

theorem debtClosure_U_0058 :
    ((∀ {K : Type v} {S : Type u} [MergeState S]
      (family : KeyedFamily K S),
      (∀ key, Spanning (family key)) → Nonempty (KeyedVerdicts family)) ∧
      HoleVerdict.isGlued (exampleVerdicts false) = true ∧
      HoleVerdict.isGlued (exampleVerdicts true) = false) ∧
    ((∀ left right : TriangleCochain,
      Cohomologous left right ↔ dualH1 left = dualH1 right) ∧
      (∀ gauge : TriangleGauge, dualH1 (coboundary gauge) = false) ∧
      dualH1 trivialCochain = false ∧
      dualH1 obstructedCochain = true ∧
      ¬ Cohomologous trivialCochain obstructedCochain) ∧
    ((∀ {Actor : Type v} [DecidableEq Actor]
      {S : Type u} [MergeState S] (x y : S)
      (left right : ProvenancedFill Actor S),
      (glueProvenanced x y left right).2 left.author = true ∧
      (glueProvenanced x y left right).2 right.author = true ∧
      (glueProvenanced x y left right).1 =
        (x ⊔ left.patch) ⊔ (y ⊔ right.patch)) ∧
      (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 0 = true ∧
      (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 1 = true ∧
      (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 2 = false) :=
  ⟨debtClosure_U_0058_keyed, debtClosure_U_0058_dualH1,
    debtClosure_U_0058_provenance⟩
