import Uwueave.TextOperational

open Uwueave Uwueave.TextSummary Uwueave.TextOperational

theorem debtClosure_U_0142 :
    (forall ops : List ContentInsert, CanonicalBatch ops -> CollisionFree ops ->
      CollisionFree ops /\
        forall operation, operation ∈ ops ->
          glyphAtId operation.id = operation.content) /\
    (forall anchor content, glyphAtId (contentId anchor content) = content) /\
    (forall ops : List ContentInsert, CanonicalBatch ops -> CollisionFree ops ->
      CollisionFree ops /\ forall operation, operation ∈ ops ->
        (project ops).1 (operation.id, operation.anchor) = true /\
        TextSummary.glyph operation.id = operation.content) /\
    (forall state operation,
      projectContent (applyContent state (.insert operation)) =
        (projectSeq (operation :: state.insertions), state.tombstones)) /\
    (project [collisionLeft] = project [collisionRight] /\
      collisionLeft.content ≠ collisionRight.content /\
      ¬ CollisionFree [collisionLeft, collisionRight]) := by
  exact ⟨collision_free_batch_projects_to_global_glyph,
    glyphAtId_contentId, collision_free_projection_agrees,
    projectContent_insert, collision_counterexample⟩
