import Uwueave.TimestampedEvidence

open Uwueave

theorem debtClosure_U_0156 :
    WorldFuture.renderW
        (TimestampedEvidence.project TimestampedEvidence.demoAfter) =
      Evidence.View.forkedClosed ∧
    Evidence.FreeTermination WorldFuture.DeliveryFuture WorldFuture.renderW
      (TimestampedEvidence.project TimestampedEvidence.demoAfter) :=
  TimestampedEvidence.demo_authenticated_progress_preserves_complete_render
