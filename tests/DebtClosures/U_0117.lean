import Uwueave.EndpointResidual

open Uwueave Uwueave.Ancestral Uwueave.Recoverable
open Uwueave.EndpointResidual

universe u v

theorem debtClosure_U_0117 :
    (∀ {S : Type u} {Op : Type v} [DecidableEq S]
      {g : Guarded S Op} {I : Invariant S} {tie : TieBreak S}
      (E : EndpointResidualSynthesis g I tie),
      ∃ M : AncestralMerge S,
        M = ancestralMerge E ∧ AncestralConfluent M g.impl I) ∧
    Reachable incrementOps.impl 0 2 ∧
    Reachable incrementOps.impl 0 3 ∧
    (ancestralMerge incrementEndpointSynthesis).merge3 0 2 3 = 5 ∧
    (incrementEndpointSynthesis.residual 0
      (natTie.pair 2 3).1 (natTie.pair 2 3).2).length = 3 ∧
    Nonempty (DeltaRecoveryOn cyclicOps) ∧
    ¬ Nonempty (FiniteRunDecoder cyclicOps) := by
  exact ⟨fun E => ⟨ancestralMerge E, rfl, ancestralConfluent E⟩,
    increment_multi_step_fixture.1,
    increment_multi_step_fixture.2.1,
    increment_multi_step_fixture.2.2.1,
    increment_multi_step_fixture.2.2.2,
    deltaRecoveryOn_insufficient_for_finite_runs⟩
