import Uwueave.TextOperational

open Uwueave Uwueave.TextSummary Uwueave.TextOperational

theorem debtClosure_U_0144 :
    (forall {bound : Nat} {state : TState} {ids : List Nat}
      (certificate : StabilityCertificate bound state ids)
      {future : TState}, certificate.Admitted future ->
        (forall id, id ∈ ids -> state.2 id = true) /\
        forall id, id ∈ ids -> namesId bound future id = false) /\
    (forall {bound : Nat} {state : TState} {ids : List Nat}
      (certificate : StabilityCertificate bound state ids)
      {future : TState}, certificate.Admitted future ->
        visible bound (collect state ids ⊔ future) =
          visible bound (state ⊔ future)) /\
    (namesId 5 noOps 1 = false /\
      visible 5 (collect deletedOne [1] ⊔ noOps) =
        visible 5 (deletedOne ⊔ noOps) /\
      visible 5 (collect deletedOne [1] ⊔ typedBMid) =
        visible 5 (deletedOne ⊔ typedBMid)) /\
    (forall {T : Type} (summary : TState -> T),
      (∃ post : List (Nat × Nat) -> T,
        forall state, summary state = post (garbageCollected 5 state)) ->
      ¬ Sufficient summary (text 5)) := by
  exact ⟨fun {bound} {state} {ids} certificate {future} admitted =>
      ⟨certificate.collected_ids_tombstoned,
        certificate.future_cannot_name_collected (future := future) admitted⟩,
    StabilityCertificate.visible_preserved, scoped_gc_fixture,
    unrestricted_gc_remains_unsound⟩
