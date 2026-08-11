/-
# Uwueave.Temporal — infinite traces, action fairness, and honest delivery progress.

`Liveness.FairOn` is a finite covering condition: a completed finite schedule
contains every required delivery.  `WorldFuture.DeliveryFuture` is a relation:
it says which arrivals are permitted, but intentionally says none of them ever
happen.  This file supplies the missing temporal layer without identifying
either earlier notion with temporal fairness.

The generic core distinguishes the two standard scheduler assumptions:

* **weak fairness / justice** — an action enabled continuously from some point
  is eventually scheduled;
* **strong fairness / compassion** — an action enabled infinitely often is
  scheduled infinitely often.

Both are predicates of an infinite trace and an *action-labelled transition
relation*.  They are not properties of every execution.  In particular, the
constant `WorldFuture.wPending` trace below consists entirely of valid
reflexive delivery steps and is nevertheless refuted as weakly fair for the
real pending-to-delivered action.

The two adapters are deliberately narrow:

* `WorldAdapter.pendingDeliveryTrace` performs the concrete delivery already
  proved by `WorldFuture.delivery_wPending_wDelivered` and then stutters;
* `RenderAdapter.bobTrace` performs `RenderProgress.deliverBob47`, whose
  authenticity as an admitted delivery and whose exit from `pending` were
  already proved by `RenderProgress`.

No theorem turns event indices into wall-clock time, finite covering into
temporal fairness, or an arbitrary valid trace into a fair one.
-/
import Uwueave.WorldFuture
import Uwueave.RenderProgress

namespace Uwueave.Temporal

universe u v w

/-! ## 1. Generic infinite traces and temporal modalities -/

/-- An infinite trace of states.  `Nat` is an event index, not a clock. -/
abbrev Trace (State : Type u) := Nat → State

/-- Every adjacent pair in the trace is admitted by `Step`. -/
def Adjacent (Step : State → State → Prop) (trace : Trace State) : Prop :=
  ∀ n, Step (trace n) (trace (n + 1))

/-- A state predicate holds at some event index. -/
def Eventually (P : State → Prop) (trace : Trace State) : Prop :=
  ∃ n, P (trace n)

/-- A state predicate holds at every event index. -/
def Always (P : State → Prop) (trace : Trace State) : Prop :=
  ∀ n, P (trace n)

/-- An index predicate holds arbitrarily far along the trace. -/
def InfinitelyOftenAt (P : Nat → Prop) : Prop :=
  ∀ lower, ∃ n, lower ≤ n ∧ P n

/-- A state predicate holds arbitrarily far along the trace. -/
def InfinitelyOften (P : State → Prop) (trace : Trace State) : Prop :=
  InfinitelyOftenAt (fun n => P (trace n))

theorem always_imp_eventually {P : State → Prop} {trace : Trace State}
    (h : Always P trace) : Eventually P trace :=
  ⟨0, h 0⟩

/-! ## 2. Safety is induction over adjacent valid steps -/

/-- `I` is preserved by every admitted step. -/
def Preserves (Step : State → State → Prop) (I : State → Prop) : Prop :=
  ∀ {s t}, I s → Step s t → I t

/-- **Trace safety.** An initially true invariant preserved by each transition
holds always.  Fairness is neither needed nor used for safety. -/
theorem always_of_preserves {Step : State → State → Prop}
    {I : State → Prop} {trace : Trace State}
    (hadj : Adjacent Step trace) (hpres : Preserves Step I) (hzero : I (trace 0)) :
    Always I trace := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      exact hpres ih (by simpa [Nat.add_comm] using hadj n)

/-! ## 3. Enabledness, occurrence, weak fairness, and strong fairness -/

/-- An action is enabled when it has at least one outgoing labelled step. -/
def Enabled (Act : Action → State → State → Prop) (action : Action)
    (state : State) : Prop :=
  ∃ next, Act action state next

/-- Action `action` labels the transition leaving index `n`. -/
def OccursAt (Act : Action → State → State → Prop) (action : Action)
    (trace : Trace State) (n : Nat) : Prop :=
  Act action (trace n) (trace (n + 1))

/-- **Weak fairness / justice.** If an action stays enabled from an arbitrary
index onward, it occurs at or after that index. -/
def WeakFair (Act : Action → State → State → Prop)
    (trace : Trace State) : Prop :=
  ∀ action lower,
    (∀ n, lower ≤ n → Enabled Act action (trace n)) →
      ∃ n, lower ≤ n ∧ OccursAt Act action trace n

/-- **Strong fairness / compassion.** If an action is enabled infinitely often,
it occurs infinitely often. -/
def StrongFair (Act : Action → State → State → Prop)
    (trace : Trace State) : Prop :=
  ∀ action,
    InfinitelyOftenAt (fun n => Enabled Act action (trace n)) →
      InfinitelyOftenAt (fun n => OccursAt Act action trace n)

/-- The requested generic liveness rule: a continuously enabled action occurs
under weak fairness.  This conclusion is an event index, not a latency bound. -/
theorem continuously_enabled_eventually_occurs
    {Act : Action → State → State → Prop} {trace : Trace State}
    (hfair : WeakFair Act trace) (action : Action)
    (henabled : ∀ n, Enabled Act action (trace n)) :
    ∃ n, OccursAt Act action trace n := by
  obtain ⟨n, _, hn⟩ := hfair action 0 (fun n _ => henabled n)
  exact ⟨n, hn⟩

/-- Strong fairness implies weak fairness: continuous enabledness is a special
case of enabledness infinitely often. -/
theorem StrongFair.weakFair
    {Act : Action → State → State → Prop} {trace : Trace State}
    (hfair : StrongFair Act trace) : WeakFair Act trace := by
  intro action lower henabled
  have hio : InfinitelyOftenAt (fun n => Enabled Act action (trace n)) := by
    intro bound
    exact ⟨max lower bound, Nat.le_max_right _ _,
      henabled _ (Nat.le_max_left _ _)⟩
  obtain ⟨n, hbound, hn⟩ := hfair action hio lower
  exact ⟨n, hbound, hn⟩

/-- A useful "enabled until scheduled" premise.  It is weaker than saying the
action remains enabled after it has occurred, which genuine one-shot delivery
usually does not. -/
def EnabledUntilOccurs (Act : Action → State → State → Prop)
    (action : Action) (trace : Trace State) : Prop :=
  ∀ n, (∀ k, k < n → ¬ OccursAt Act action trace k) →
    Enabled Act action (trace n)

/-- Weak fairness plus persistent enabledness until scheduling forces a
one-shot action to occur. -/
theorem eventually_occurs_of_enabledUntil
    {Act : Action → State → State → Prop} {trace : Trace State}
    (hfair : WeakFair Act trace) (action : Action)
    (hpersist : EnabledUntilOccurs Act action trace) :
    ∃ n, OccursAt Act action trace n := by
  classical
  by_cases hsome : ∃ n, OccursAt Act action trace n
  · exact hsome
  · have hnever : ∀ n, ¬ OccursAt Act action trace n := by
      intro n hn
      exact hsome ⟨n, hn⟩
    exact continuously_enabled_eventually_occurs hfair action
      (fun n => hpersist n (fun k _ => hnever k))

/-! ## 4. Adapter: the concrete `WorldFuture` delivery -/

namespace WorldAdapter

open Uwueave.WorldFuture

/-- The real one-shot action that delivers bob's already-issued candidate. -/
def PendingDeliveryAction : Unit → World Holes.Val → World Holes.Val → Prop :=
  fun _ before after => before = wPending ∧ after = wDelivered

/-- Every occurrence of the labelled action is an admitted world delivery. -/
theorem pendingDeliveryAction_is_delivery {before after : World Holes.Val}
    (h : PendingDeliveryAction () before after) : DeliveryFuture before after := by
  rcases h with ⟨rfl, rfl⟩
  exact delivery_wPending_wDelivered

/-- Deliver once, then remain at the delivered world. -/
def pendingDeliveryTrace : Trace (World Holes.Val)
  | 0 => wPending
  | _ + 1 => wDelivered

/-- Every adjacent transition is a real `WorldFuture.DeliveryFuture`: the first
delivers bob and later transitions use wellformed reflexivity. -/
theorem pendingDeliveryTrace_adjacent :
    Adjacent DeliveryFuture pendingDeliveryTrace := by
  intro n
  cases n with
  | zero => exact delivery_wPending_wDelivered
  | succ n =>
      exact delivery_refl wf_wDelivered

theorem pendingDelivery_occurs_at_zero :
    OccursAt PendingDeliveryAction () pendingDeliveryTrace 0 :=
  ⟨rfl, rfl⟩

/-- The concrete delivery trace is weakly fair for its one action. -/
theorem pendingDeliveryTrace_weakFair :
    WeakFair PendingDeliveryAction pendingDeliveryTrace := by
  intro action lower henabled
  cases action
  cases lower with
  | zero => exact ⟨0, Nat.le_refl _, pendingDelivery_occurs_at_zero⟩
  | succ lower =>
      obtain ⟨next, hnext⟩ := henabled (lower + 1) (Nat.le_refl _)
      have hbefore : wDelivered = wPending := by
        simpa [pendingDeliveryTrace] using hnext.1
      have hstate : WorldFuture.observe wDelivered = WorldFuture.observe wPending :=
        congrArg WorldFuture.observe hbefore
      exact False.elim (by
        have hcand : Evidence.cand4749 = Evidence.cand47 := congrArg Prod.fst hstate
        have htrue : Evidence.cand4749 (49, Evidence.bob) = true := by decide
        have hfalse : Evidence.cand47 (49, Evidence.bob) = false := by decide
        rw [congrFun hcand (49, Evidence.bob), hfalse] at htrue
        exact Bool.noConfusion htrue)

/-- Fair scheduling reaches the delivered world (here at the transition's
target), expressed through the generic occurrence theorem. -/
theorem pendingDelivery_eventually_delivered
    (hfair : WeakFair PendingDeliveryAction pendingDeliveryTrace) :
    Eventually (fun w => w = wDelivered) pendingDeliveryTrace := by
  obtain ⟨n, hn⟩ := eventually_occurs_of_enabledUntil hfair () (by
    intro i hnone
    cases i with
    | zero => exact ⟨wDelivered, ⟨rfl, rfl⟩⟩
    | succ i =>
        exact False.elim (hnone 0 (Nat.zero_lt_succ i) pendingDelivery_occurs_at_zero))
  exact ⟨n + 1, hn.2⟩

/-- The constant pending run contains only valid reflexive delivery steps. -/
def starvedPendingTrace : Trace (World Holes.Val) := fun _ => wPending

theorem starvedPendingTrace_adjacent :
    Adjacent DeliveryFuture starvedPendingTrace :=
  fun _ => delivery_refl wf_wPending

theorem pendingAction_continuously_enabled_on_starved :
    ∀ n, Enabled PendingDeliveryAction () (starvedPendingTrace n) :=
  fun _ => ⟨wDelivered, rfl, rfl⟩

theorem pendingAction_never_occurs_on_starved :
    ∀ n, ¬ OccursAt PendingDeliveryAction () starvedPendingTrace n := by
  intro n h
  have hstate : WorldFuture.observe wPending = WorldFuture.observe wDelivered := by
    simpa [starvedPendingTrace] using congrArg WorldFuture.observe h.2
  have hcand : Evidence.cand47 = Evidence.cand4749 := congrArg Prod.fst hstate
  have hfalse : Evidence.cand47 (49, Evidence.bob) = false := by decide
  have htrue : Evidence.cand4749 (49, Evidence.bob) = true := by decide
  rw [congrFun hcand (49, Evidence.bob), htrue] at hfalse
  exact Bool.noConfusion hfalse

/-- **Starvation counterexample.** Valid steps do not imply fair steps: the
constant pending trace enables the genuine delivery forever and never takes it. -/
theorem starvedPendingTrace_not_weakFair :
    ¬ WeakFair PendingDeliveryAction starvedPendingTrace := by
  intro hfair
  obtain ⟨n, hn⟩ := continuously_enabled_eventually_occurs hfair ()
    pendingAction_continuously_enabled_on_starved
  exact pendingAction_never_occurs_on_starved n hn

end WorldAdapter

/-! ## 5. Adapter: `RenderProgress` delivery exits `pending` -/

namespace RenderAdapter

open Uwueave.RenderProgress
open Uwueave.RenderSix

abbrev EvidenceState := Evidence.ResultEvidence Holes.Val

/-- Bob's genuine delivery as an action-labelled transition. -/
def BobDeliveryAction : Unit → EvidenceState → EvidenceState → Prop :=
  fun _ before after =>
    before = ResultStatus.emptyOpenW ∧ after = before ⊔ deliverBob47

theorem bobDeliveryAction_is_genuine {before after : EvidenceState}
    (h : BobDeliveryAction () before after) :
    IsDelivery before deliverBob47
      ∧ Evidence.SealedFuture before after := by
  rcases h with ⟨rfl, rfl⟩
  exact ⟨deliverBob47_isDelivery,
    sealed_joinAll_of_deliveries ResultStatus.emptyOpenW [deliverBob47]
      (by
        intro delta hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        subst delta
        exact deliverBob47_isDelivery)⟩

/-- Deliver bob's response once, then stutter at the provisional result. -/
def bobTrace : Trace EvidenceState
  | 0 => ResultStatus.emptyOpenW
  | _ + 1 => ResultStatus.bobSpokeW

theorem bobDelivery_occurs_at_zero :
    OccursAt BobDeliveryAction () bobTrace 0 := by
  refine ⟨rfl, ?_⟩
  exact emptyOpenW_merge_deliverBob47.symm

theorem bobTrace_weakFair : WeakFair BobDeliveryAction bobTrace := by
  intro action lower henabled
  cases action
  cases lower with
  | zero => exact ⟨0, Nat.le_refl _, bobDelivery_occurs_at_zero⟩
  | succ lower =>
      obtain ⟨next, hnext⟩ := henabled (lower + 1) (Nat.le_refl _)
      have heq : ResultStatus.bobSpokeW = ResultStatus.emptyOpenW := by
        simpa [bobTrace] using hnext.1
      have hcand : ResultStatus.cand47bob = ResultStatus.candNone :=
        congrArg (fun e : EvidenceState => Evidence.candidates e) heq
      exact False.elim (by
        have htrue : ResultStatus.cand47bob (47, Evidence.bob) = true := by decide
        have hfalse : ResultStatus.candNone (47, Evidence.bob) = false := by decide
        rw [congrFun hcand (47, Evidence.bob), hfalse] at htrue
        exact Bool.noConfusion htrue)

/-- Occurring bob's delivery really leaves the `pending` status. -/
theorem bobDelivery_exits_pending {before after : EvidenceState}
    (h : BobDeliveryAction () before after) :
    ResultStatus.statusOf after ≠ ResultStatus.Status.pending := by
  rcases h with ⟨rfl, hafter⟩
  rw [emptyOpenW_merge_deliverBob47] at hafter
  subst after
  rw [RenderSix.statusOf_bobSpokeW]
  exact provisional_ne_pending 47

/-- **Temporal pending exit.** Under weak fairness, the concrete response that
is enabled until it is scheduled occurs and the scheduler's successor state no
longer renders `pending`. -/
theorem fair_bob_delivery_exits_pending
    (hfair : WeakFair BobDeliveryAction bobTrace) :
    ∃ n, OccursAt BobDeliveryAction () bobTrace n
      ∧ ResultStatus.statusOf (bobTrace (n + 1)) ≠ ResultStatus.Status.pending := by
  obtain ⟨n, hn⟩ := eventually_occurs_of_enabledUntil hfair () (by
    intro i hnone
    cases i with
    | zero =>
        exact ⟨ResultStatus.bobSpokeW, bobDelivery_occurs_at_zero⟩
    | succ i =>
        exact False.elim (hnone 0 (Nat.zero_lt_succ i) bobDelivery_occurs_at_zero))
  exact ⟨n, hn, bobDelivery_exits_pending hn⟩

theorem bobTrace_eventually_not_pending :
    Eventually (fun e =>
      ResultStatus.statusOf e ≠ ResultStatus.Status.pending) bobTrace := by
  obtain ⟨n, _, hexit⟩ := fair_bob_delivery_exits_pending bobTrace_weakFair
  exact ⟨n + 1, hexit⟩

end RenderAdapter

/-! ## 6. Boundary

The generic progress theorem closes the missing *formal vocabulary* for
infinite traces and scheduler fairness, and the two adapters show that the
vocabulary reaches real delivery and rendering witnesses.  It does not close
the deployment hypotheses: no network implementation is shown weakly fair,
and `Nat` indices count transitions rather than seconds.  In particular,
`WorldAdapter.starvedPendingTrace_not_weakFair` is the executable warning
against silently treating every valid trace as fair.
-/

end Uwueave.Temporal
