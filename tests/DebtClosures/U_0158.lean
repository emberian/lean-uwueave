import Uwueave.WorldFuture

open Uwueave

universe u

theorem debtClosure_U_0158 {alpha : Type u} [DecidableEq alpha] :
    (∀ roster : Catalog.GSet Evidence.Source,
      WorldFuture.Wf (WorldFuture.WorldMachine.initial alpha roster).world ∧
        WorldFuture.RosterKnown
          (WorldFuture.WorldMachine.initial alpha roster).world) ∧
    (∀ (current : WorldFuture.WorldMachine.SafeState alpha)
      (action : WorldFuture.WorldMachine.Action alpha),
      WorldFuture.Wf
          (WorldFuture.WorldMachine.runStep current action).world ∧
        WorldFuture.RosterKnown
          (WorldFuture.WorldMachine.runStep current action).world) ∧
    (∀ (current snapshot : WorldFuture.WorldMachine.SafeState alpha),
      WorldFuture.WorldMachine.step? current (.recover snapshot) = some snapshot ∧
        WorldFuture.Wf snapshot.world ∧
        WorldFuture.RosterKnown snapshot.world) ∧
    (∀ (current : WorldFuture.WorldMachine.SafeState alpha)
      (event : alpha × Evidence.Source),
      current.world.issued event = false →
        WorldFuture.WorldMachine.step? current (.deliver event) = none ∧
        WorldFuture.WorldMachine.runStep current (.deliver event) = current) := by
  refine ⟨WorldFuture.WorldMachine.initialization_preserves alpha,
    WorldFuture.WorldMachine.every_run_step_preserves,
    WorldFuture.WorldMachine.recovery_preserves, ?_⟩
  intro current event missing
  have rejected := WorldFuture.WorldMachine.unissued_delivery_is_rejected
    current event missing
  exact ⟨rejected,
    WorldFuture.WorldMachine.rejected_step_stutters current (.deliver event) rejected⟩
