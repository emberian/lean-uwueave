import Uwueave.WovenOperational

open Uwueave Uwueave.Wellformed Uwueave.WovenOperational

theorem debtClosure_U_0147 :
    (forall {document : WovenDoc} {term : Term} {kind : Kind},
      Synth document term kind -> Checks document term kind) /\
    (forall {n root : Nat} {kind : Kind}
      (state : TypedTermState n root kind),
      WellFormed n root state.document) /\
    (forall {n root : Nat} {document : WovenDoc},
      WellFormed n root document ->
      forall {command : TermCommand} {term : Term},
        checkCommand document command = some term ->
        ∃ state : TypedTermState n root .node,
          state.document = document /\ state.term = term) /\
    checkCommand docX (.relocate 101 0 1) =
        some (.relocated 0 1 101) /\
    checkCommand docX (.relocate 101 0 12) = none := by
  exact ⟨synth_implies_check, typed_evaluation_preserves_wellFormed,
    every_accepted_edit_preserves_wellFormed,
    positive_relocation_fixture, rejected_relocation_fixture⟩
