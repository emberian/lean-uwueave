import Uwueave.TextOperational

open Uwueave Uwueave.TextSummary Uwueave.TextOperational

theorem debtClosure_U_0145 :
    (forall left right : FugueState, left ⊔ right = right ⊔ left) /\
    (forall state : FugueState, state ⊔ state = state) /\
    (forall (bound : Nat) (state : FugueState),
      fugueDocOrder bound state =
        Fugue.docOrder bound (TextSummary.toOpSet bound state)) /\
    (canonicalFugueText 4 (fugueALow ⊔ fugueBMid) =
        fugueText 4 (fugueALow ⊔ fugueBMid) /\
      canonicalFugueText 4 (fugueALow ⊔ fugueBMid) = [.a, .b]) := by
  exact ⟨fugue_state_merge_comm, fugue_state_merge_idem,
    materialized_docOrder_agrees_reference,
    canonical_fugue_witness_agrees⟩
