/-
# Uwueave.TimestampedEvidence — authenticated progress over timestamped evidence

This is the timestamp-carrying successor to `Evidence.ResultEvidence`.
Candidate timestamps and a genuine source frontier are stored in the state;
the old evidence is an explicit erasure used only for its renderer. An
`AcceptedRuntimeProgress` consumes an `AuthenticatedFrontier.AuthenticatedAdvance`
and binds every decoded set and frontier to before/after runtime snapshots.

The main theorem is deliberately conditional in the two places a proof model
must be conditional: the signed progress envelope still relies on the caller's
`AuthenticIssuer` premise, and terminal progress requires a known roster and a
closed evidence projection. Under those conditions the authenticated lawful
advance freezes the complete rendered view, not only candidate values.
-/
import Uwueave.AuthenticatedWorldContext

namespace Uwueave.TimestampedEvidence

open Uwueave Uwueave.Catalog

abbrev CandidateEvent (alpha T : Type) :=
  AuthenticatedFrontier.CandidateEvent alpha T

/-- Timestamped materialized evidence. Unlike the legacy carrier, the
timestamp and source frontier are intrinsic fields. -/
structure State (alpha T : Type) [Frontier.PartialOrder T] where
  delivered : GSet (CandidateEvent alpha T)
  frontier : Frontier.SourceFrontier T
  obligations : GSet Evidence.Source
  certificates : GSet Evidence.Source

/-- Erase timestamps only at the compatibility boundary to the old renderer. -/
noncomputable def eraseState {alpha T : Type}
    [Frontier.PartialOrder T] (state : State alpha T) :
    Evidence.ResultEvidence alpha :=
  (AuthenticatedWorldContext.eraseTimestampSet state.delivered,
    state.obligations, state.certificates)

/-- A timestamped runtime snapshot retains the issued event pool and the
world context required by delivery semantics. -/
structure Runtime (alpha T : Type) [Frontier.PartialOrder T] where
  state : State alpha T
  issued : GSet (CandidateEvent alpha T)
  roster : GSet Evidence.Source
  sealed : GSet Evidence.Source
  epoch : Nat

/-- Compatibility projection to the established world-indexed future model. -/
noncomputable def project {alpha T : Type}
    [Frontier.PartialOrder T] (runtime : Runtime alpha T) :
    WorldFuture.World alpha where
  state := eraseState runtime.state
  issued := AuthenticatedWorldContext.eraseTimestampSet runtime.issued
  roster := runtime.roster
  sealed := runtime.sealed
  epoch := runtime.epoch

/-- Erasing a larger timestamped event set yields a larger attributed
candidate set. -/
theorem eraseTimestampSet_mono {alpha T : Type}
    {left right : GSet (CandidateEvent alpha T)} (h : left ⊑ right) :
    AuthenticatedWorldContext.eraseTimestampSet left ⊑
      AuthenticatedWorldContext.eraseTimestampSet right := by
  apply (Holes.gset_leq_iff_subset _ _).2
  intro erased herased
  rw [AuthenticatedWorldContext.eraseTimestampSet, Holes.mem_bindSet] at herased ⊢
  rcases herased with ⟨event, hevent, heq⟩
  exact ⟨event, (Holes.gset_leq_iff_subset _ _).1 h event hevent, heq⟩

/-- An authenticated progress record consumed by exact before/after runtime
snapshots. Authentication, genuine issuance and semantic lawfulness are carried
by `advance`; the equalities prevent a consumer from checking one decoded set
and mutating another. -/
structure AcceptedRuntimeProgress
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {authRoster : List Evidence.Source}
    {codec : AuthenticatedFrontier.ProgressCodec alpha T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress scheme keys
      keyRevocations authIssued received authRoster}
    (advance : AuthenticatedFrontier.AuthenticatedAdvance codec progress)
    (before after : Runtime alpha T) : Prop where
  progress_source_member : before.roster progress.source = true
  before_frontier_exact : before.state.frontier =
    codec.beforeOf progress.acceptedEvent.event
  after_frontier_exact : after.state.frontier =
    codec.afterOf progress.acceptedEvent.event
  issued_before_exact : before.issued = advance.issued
  issued_after_exact : after.issued = advance.issued
  delivered_before_exact : before.state.delivered = advance.deliveredBefore
  delivered_after_exact : after.state.delivered = advance.deliveredAfter
  world_delivery : WorldFuture.DeliveryFuture (project before) (project after)

/-- The post-progress conditions needed for a complete render contract. The
frontier must settle every issued timestamp; the other two renderer axes are
the explicit known-roster and closure conditions. -/
structure Terminal {alpha T : Type} [Frontier.PartialOrder T]
    (runtime : Runtime alpha T) : Prop where
  wf : WorldFuture.Wf (project runtime)
  rosterKnown : WorldFuture.RosterKnown (project runtime)
  closed : Evidence.Closed (WorldFuture.observe (project runtime))
  issuedSettled : ∀ event, runtime.issued event = true →
    Frontier.Settled runtime.state.frontier event.2 event.1.timestamp

/-- Lawful terminal progress has materialized every issued candidate after
timestamp erasure. This is where frontier lawfulness is load-bearing. -/
theorem delivered_eq_issued_after
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {authRoster : List Evidence.Source}
    {codec : AuthenticatedFrontier.ProgressCodec alpha T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress scheme keys
      keyRevocations authIssued received authRoster}
    {advance : AuthenticatedFrontier.AuthenticatedAdvance codec progress}
    {before after : Runtime alpha T}
    (accepted : AcceptedRuntimeProgress advance before after)
    (terminal : Terminal after) :
    WorldFuture.delivered (project after) = (project after).issued := by
  have htimestamped : advance.issued ⊑ advance.deliveredAfter := by
    apply (Holes.gset_leq_iff_subset _ _).2
    intro event hi
    apply advance.lawful.complete_after event hi
    rw [← accepted.after_frontier_exact]
    apply terminal.issuedSettled event
    rw [accepted.issued_after_exact]
    exact hi
  have herased := eraseTimestampSet_mono htimestamped
  have hforward : (project after).issued ⊑
      WorldFuture.delivered (project after) := by
    simpa [project, eraseState, accepted.issued_after_exact,
      accepted.delivered_after_exact] using herased
  have hbackward : WorldFuture.delivered (project after) ⊑
      (project after).issued :=
    Evidence.candidates_mono terminal.wf
  exact leq_antisymm hbackward hforward

/-- **Complete render stability from accepted authenticated progress.** The
lawful frontier advance saturates candidates; known roster plus wellformedness
prevents new obligations; closure plus monotone certificates preserves the
closure truth. `Evidence.render_congr` then freezes the whole five-way view. -/
theorem accepted_progress_preserves_render
    {alpha T : Type} [Frontier.PartialOrder T]
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {authIssued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    {authRoster : List Evidence.Source}
    {codec : AuthenticatedFrontier.ProgressCodec alpha T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress scheme keys
      keyRevocations authIssued received authRoster}
    {advance : AuthenticatedFrontier.AuthenticatedAdvance codec progress}
    {before after : Runtime alpha T}
    (accepted : AcceptedRuntimeProgress advance before after)
    (terminal : Terminal after) :
    Evidence.FreeTermination WorldFuture.DeliveryFuture
      (WorldFuture.renderW (α := alpha)) (project after) := by
  intro future hfuture
  have hsaturated := delivered_eq_issued_after accepted terminal
  have hbeforeFuture : WorldFuture.delivered (project after) ⊑
      WorldFuture.delivered future :=
    Evidence.candidates_mono hfuture.1.1
  have hfuturePool : WorldFuture.delivered future ⊑
      (project after).issued :=
    Evidence.candidates_mono hfuture.1.2.1
  have hcandidates : WorldFuture.delivered future =
      WorldFuture.delivered (project after) := by
    apply leq_antisymm
    · rw [hsaturated]
      exact hfuturePool
    · exact hbeforeFuture
  have hclosedFuture : Evidence.Closed (WorldFuture.observe future) := by
    intro source hsource
    have hroster : (project after).roster source = true :=
      (Holes.gset_leq_iff_subset _ _).1
        (Evidence.obligations_mono hfuture.1.2.1) source hsource
    have hknown : WorldFuture.frontier (project after) source = true :=
      (Holes.gset_leq_iff_subset _ _).1 terminal.rosterKnown source hroster
    have hcert := terminal.closed source hknown
    exact Evidence.certificates_grow hfuture.1.1 hcert
  apply Evidence.render_congr
  · exact Evidence.values_congr hcandidates
  · exact ⟨fun _ => terminal.closed, fun _ => hclosedFuture⟩

/-! ## Concrete authenticated terminal progress

The existing authenticated progress fixture delivers both timestamped
candidates. Here the runtime also materializes the roster-closing certificate,
so the resulting view is a closed fork and the theorem above proves it cannot
move under delivery. -/

def demoBeforeState : State Holes.Val Nat where
  delivered := AuthenticatedWorldContext.timestampedBefore
  frontier := AuthenticatedWorldContext.progressCodec.beforeOf
    AuthenticatedWorldContext.progressEvent
  obligations := Evidence.srcsAB
  certificates := Evidence.srcsA

def demoAfterState : State Holes.Val Nat where
  delivered := AuthenticatedWorldContext.timestampedAfter
  frontier := AuthenticatedWorldContext.progressCodec.afterOf
    AuthenticatedWorldContext.progressEvent
  obligations := Evidence.srcsAB
  certificates := Evidence.srcsAB

def demoBefore : Runtime Holes.Val Nat where
  state := demoBeforeState
  issued := AuthenticatedWorldContext.timestampedIssued
  roster := Evidence.srcsAB
  sealed := Evidence.srcsAB
  epoch := 1

def demoAfter : Runtime Holes.Val Nat where
  state := demoAfterState
  issued := AuthenticatedWorldContext.timestampedIssued
  roster := Evidence.srcsAB
  sealed := Evidence.srcsAB
  epoch := 1

def demoBeforeWorld : WorldFuture.World Holes.Val where
  state := Evidence.openW
  issued := Evidence.cand4749
  roster := Evidence.srcsAB
  sealed := Evidence.srcsAB
  epoch := 1

def demoAfterWorld : WorldFuture.World Holes.Val where
  state := Evidence.forkedClosedW
  issued := Evidence.cand4749
  roster := Evidence.srcsAB
  sealed := Evidence.srcsAB
  epoch := 1

theorem project_demoBefore : project demoBefore = demoBeforeWorld := by
  simp [project, demoBefore, demoBeforeState, demoBeforeWorld, eraseState,
    Evidence.openW, AuthenticatedWorldContext.erase_timestampedBefore,
    AuthenticatedWorldContext.erase_timestampedIssued]

theorem project_demoAfter : project demoAfter = demoAfterWorld := by
  simp [project, demoAfter, demoAfterState, demoAfterWorld, eraseState,
    Evidence.forkedClosedW, AuthenticatedWorldContext.timestampedAfter,
    AuthenticatedWorldContext.erase_timestampedIssued]

theorem demo_world_delivery :
    WorldFuture.DeliveryFuture demoBeforeWorld demoAfterWorld := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, rfl⟩
  · change Evidence.openW ⊑ Evidence.forkedClosedW
    apply Evidence.leq_of_components
    · apply (Holes.gset_leq_iff_subset _ _).2
      intro event hevent
      change Evidence.cand47 event = true at hevent
      change Evidence.cand4749 event = true
      exact decide_eq_true (Or.inl (of_decide_eq_true hevent))
    · exact leq_refl _
    · apply (Holes.gset_leq_iff_subset _ _).2
      intro source hsource
      change Evidence.srcsA source = true at hsource
      change Evidence.srcsAB source = true
      exact decide_eq_true (Or.inl (of_decide_eq_true hsource))
  · change Evidence.forkedClosedW ⊑ Evidence.forkedClosedW
    exact leq_refl _
  · intro event hbefore hafter
    change Evidence.cand47 event = false at hbefore
    change Evidence.cand4749 event = true at hafter
    have hafter' := of_decide_eq_true hafter
    rcases hafter' with h47 | h49
    · rw [h47] at hbefore
      exact False.elim (Bool.noConfusion hbefore)
    · subst event
      exact ⟨by decide, by decide⟩

def demoAccepted : AcceptedRuntimeProgress
    AuthenticatedWorldContext.authenticatedAdvance demoBefore demoAfter where
  progress_source_member := by decide
  before_frontier_exact := rfl
  after_frontier_exact := rfl
  issued_before_exact := rfl
  issued_after_exact := rfl
  delivered_before_exact := rfl
  delivered_after_exact := rfl
  world_delivery := by
    rw [project_demoBefore, project_demoAfter]
    exact demo_world_delivery

theorem demo_terminal : Terminal demoAfter := by
  constructor
  · rw [project_demoAfter]
    exact leq_refl _
  · rw [project_demoAfter]
    exact leq_refl _
  · rw [project_demoAfter]
    exact Evidence.closed_forkedClosedW
  · intro event _
    exact Frontier.complete_empty _

/-- Non-vacuous paid evidence: a genuinely authenticated and lawful progress
record reaches `forkedClosed`, and the entire rendered view is delivery-stable. -/
theorem demo_authenticated_progress_preserves_complete_render :
    WorldFuture.renderW (project demoAfter) = Evidence.View.forkedClosed ∧
      Evidence.FreeTermination WorldFuture.DeliveryFuture
        WorldFuture.renderW (project demoAfter) := by
  constructor
  · rw [project_demoAfter]
    exact Evidence.four_states_inhabited.2.2.1
  · exact accepted_progress_preserves_render demoAccepted demo_terminal

end Uwueave.TimestampedEvidence
