import Uwueave.WovenOperational

open Uwueave Uwueave.Wellformed Uwueave.WovenOperational

theorem debtClosure_U_0149 :
    checkCommand docX (.crossTree 103 7 1) =
        some (.crossTree 7 1 103) /\
    (checkCommand docX (.relocate 101 0 0) =
        some (.relocated 0 0 101) /\
      checkCommand docX (.relocate 102 0 1) =
        some (.relocated 0 1 102)) /\
    mergeRelocations relocationLeft relocationRight =
        .hole .node [101, 102] /\
    render (mergeRelocations relocationLeft relocationRight) =
        .unresolved .node [101, 102] /\
    (forall {n root : Nat} (document : WovenDoc),
      WellFormed n root document -> forall term : Term,
        ∃ output : Rendered,
          render term = output /\ WellFormed n root document) /\
    (forall {n root : Nat} {document : WovenDoc},
      WellFormed n root document ->
      forall {term resolved : Term} {chosen : NodeId},
        resolve document term chosen = some resolved ->
        WellFormed n root document) /\
    (resolve docX (mergeRelocations relocationLeft relocationRight) 1 =
        some (.node 1) /\
      Checks docX (.node 1) .node /\
      WellFormed 5 9 docX) := by
  exact ⟨cross_tree_reference_fixture,
    conflicting_relocations_are_accepted,
    relocation_conflict_retains_provenance,
    conflict_render_retains_provenance,
    rendering_preserves_wellFormed,
    resolution_preserves_wellFormed,
    conflict_resolution_fixture⟩
