/-
# Uwueave.Scheduling — seam crossings are effects; meetings discharge coeffects.

`Cost.crossings` counts changes of one chosen seam along one replica's stream.
`CoordEffect.Profile` correctly keeps that count indexed by the strategy until a
whole session chooses one. `Budget.Plan` may therefore witness an upper bound on
**crossings**. None of those objects says who attends, which epoch or evidence a
coordination action concerns, whether two actions share a round, or even which
currency the action spends. Calling their `Nat` a meeting count was the hole.

This file builds the smallest scheduling layer that closes it without changing
the meaning of any existing judgement.

## Effects, coeffects, and schedules

  * A `Session` records the seam-crossing effect as a `Nat`. `ofCost` can make
    that number definitionally equal to `Cost.crossings`; it never re-counts.
  * An `Obligation` is a coeffect. Its `Demand` carries a currency, participant
    roster, scope, epoch, evidence key, round tag, and barrier tag. Its `Origin`
    says whether the demand came from one of this session's crossings or from an
    ambient mechanism. A crossing origin is a `Fin crossings`, so a dangling
    attribution cannot be constructed.
  * `Compatible` is deliberately conservative: all seven scheduling fields
    must agree. This is a sufficient coalescing rule, not a completeness claim.
    It is inhabited (`compatible_refl`) and every field is load-bearing in
    `compatibility_axes_are_load_bearing`.
  * A `Schedule` is a list of coordination actions plus a proof that every
    obligation is discharged by a compatible action. One action may discharge
    arbitrarily many compatible demands. `Plan` and `UpperBound` follow
    `Budget`'s discipline: acceptance is by an exhibited schedule and a proved
    upper bound, never by a lower bound or a crossing count.

The schedule keeps a **currency profile** `Currency → Nat`; it has no scalar
total. `peerMeetingCount` is only the `.peerBarrier` coordinate. An arbiter cut,
network round, prompt, or rollback is not renamed a peer meeting.

## The refutation, both directions

  * `crossings_can_exceed_meetings`: two crossings carrying the same demand
    coalesce into one peer meeting. The least meeting count is exactly 1.
  * `meetings_can_exceed_crossings`: an ambient peer barrier requires one
    meeting at crossing count 0. Again the optimum is exact.
  * `same_crossings_different_least_meetings`: two sessions both report zero
    crossings, yet their least meeting counts are 0 and 1.
    `no_crossing_count_determines_least_meetings` packages this as the explicit
    non-function.
  * `one_crossing_can_need_two_rounds`: one crossing emits two incompatible
    round tags, forcing exactly two peer meetings.

So there is no function from crossing count alone to least meeting count. The
counterexamples are schedules and universal lower bounds, not hand-assigned
numbers.

## Boundaries

  * ⟨TERMINAL for this model⟩ `Compatible` is equality of scheduling keys.
    A richer scheduler may union rosters or prove evidence subsumption, but it
    must replace this relation with a theorem-backed one. Nothing here claims
    the conservative schedule is globally minimal for a deployment.
  * ⟨TERMINAL⟩ `Choreo.sync` supplies a synchronous barrier semantics, but
    its constructor does not carry scope, epoch, evidence, round, or barrier
    tags. Extracting a `Demand` from arbitrary choreography syntax would invent
    those fields, so no such extraction is claimed. A caller must annotate the
    interpretation explicitly.
  * ⟨TERMINAL⟩ `Origin.ambient` is intentional: arbiter cuts, checkpoint
    barriers, and user prompts need not be caused by a seam crossing. Removing
    it would make `crossings = 0 → meetings = 0` true by construction rather
    than by the system.
  * ⚠ ⟨CONSISTENT BOUNDARY⟩ `CoordEffect.lean` now states the same qualified
    boundary this file proves: pointwise-added crossings are not a generic upper
    bound on schedule actions. `one_crossing_can_need_two_rounds` is the exact
    witness — one crossing, two forced peer meetings. An upper-bound reading
    needs an **at-most-one demand per crossing** interpretation; pure coalescing
    alone is not enough.
  * ⟨SCOPE U-0139⟩ Participants are declared, not proved online; there is no runtime
    liveness, deadlock-freedom, message-loss, or elapsed-time model, and no
    unbounded deployment-complete schedule-catalog generator. Finite catalog
    search does not establish any of those operational properties.
  * ⟨DONE downstream in `Uwueave.Preo.ProtocolSurface`⟩ **The native protocol
    syntax debt is closed.** The parser covers operation, sequential and
    parallel composition, nonempty finite choice, bounded repetition, and
    synchronization without an opaque `Protocol.Term` in the main fixture.
    Each command emits exact `N.Term`, `N.Elaboration`, `N.Session`, `N.Plan`,
    `N.Limits`, and `N.ProfileUpperBound` values. `NativeFixture` checks every
    constructor, all seven demand axes, and all five currencies; malformed
    crossing origins and unsupported nodes fail closed. The separate
    `preo_budget` command supplies a user-authored, plan-indexed five-currency
    budget witness rather than deriving one from a crossing scalar.
  * ⟨TERMINAL⟩ There is no transport from `Budget.ForcedFloor` to a meeting
    floor or five-currency acceptance. Floors are lower-bound evidence, not
    schedule constructors; `meeting_floor_does_not_entail_profile_acceptance`
    is the concrete obstruction.
-/
import Uwueave.CoordEffect

namespace Uwueave.Scheduling

open Uwueave

/-! ## §1. Demands: the coeffect a coordination action must discharge. -/

/-- Currencies remain separate. Only `peerBarrier` is counted as a peer
meeting; the other constructors are still schedule actions and remain visible
in `Schedule.profile`. -/
inductive Currency where
  | peerBarrier
  | arbiterCut
  | networkRound
  | userPrompt
  | rollback
  deriving DecidableEq, Repr

/-- The evidence a coordination demand is relative to. `none` is explicit: it
is different from silently omitting the evidence axis. -/
inductive EvidenceKey where
  | none
  | named (key : Nat)
  deriving DecidableEq, Repr

/-- **One scheduling demand.** Every field participates in `Compatible`.

`participants` is an ordered roster, matching `Choreo.denote`'s roster-shaped
barrier input. A deployment that treats roster permutation or duplication as
irrelevant owes a normalisation theorem before weakening compatibility. -/
structure Demand where
  currency : Currency
  participants : List Nat
  scope : Nat
  epoch : Nat
  evidence : EvidenceKey
  round : Nat
  barrier : Nat
  deriving DecidableEq, Repr

/-- A conservative, decidable coalescing rule: two demands may share one action
when every scheduling key agrees. This is written field-by-field so none of the
axes can disappear behind structure equality. -/
def Compatible (a b : Demand) : Prop :=
  a.currency = b.currency
    ∧ a.participants = b.participants
    ∧ a.scope = b.scope
    ∧ a.epoch = b.epoch
    ∧ a.evidence = b.evidence
    ∧ a.round = b.round
    ∧ a.barrier = b.barrier

theorem compatible_refl (d : Demand) : Compatible d d :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem compatible_symm {a b : Demand} (h : Compatible a b) : Compatible b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm,
   h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩

theorem compatible_trans {a b c : Demand}
    (hab : Compatible a b) (hbc : Compatible b c) : Compatible a c :=
  ⟨hab.1.trans hbc.1,
   hab.2.1.trans hbc.2.1,
   hab.2.2.1.trans hbc.2.2.1,
   hab.2.2.2.1.trans hbc.2.2.2.1,
   hab.2.2.2.2.1.trans hbc.2.2.2.2.1,
   hab.2.2.2.2.2.1.trans hbc.2.2.2.2.2.1,
   hab.2.2.2.2.2.2.trans hbc.2.2.2.2.2.2⟩

/-- At this first model, compatibility is exactly equality of demand keys. -/
theorem compatible_iff_eq {a b : Demand} : Compatible a b ↔ a = b := by
  constructor
  · intro h
    cases a with
    | mk ac ap as ae av ar ab =>
      cases b with
      | mk bc bp bs be bv br bb =>
        simp only [Compatible] at h
        rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rfl
  · intro h
    subst h
    exact compatible_refl _

/-! ### Every compatibility axis is inhabited and refutable. -/

def baseDemand : Demand where
  currency := .peerBarrier
  participants := [0, 1]
  scope := 7
  epoch := 3
  evidence := .named 11
  round := 0
  barrier := 5

/-- No field is display metadata: changing any one refutes compatibility. -/
theorem compatibility_axes_are_load_bearing :
    Compatible baseDemand baseDemand
      ∧ ¬ Compatible baseDemand { baseDemand with currency := .networkRound }
      ∧ ¬ Compatible baseDemand { baseDemand with participants := [0, 2] }
      ∧ ¬ Compatible baseDemand { baseDemand with scope := 8 }
      ∧ ¬ Compatible baseDemand { baseDemand with epoch := 4 }
      ∧ ¬ Compatible baseDemand { baseDemand with evidence := .named 12 }
      ∧ ¬ Compatible baseDemand { baseDemand with round := 1 }
      ∧ ¬ Compatible baseDemand { baseDemand with barrier := 6 } := by
  simp [Compatible, baseDemand]

/-! ## §2. Sessions: crossing effects with proof-carrying origins. -/

/-- A demand is either attributed to a particular seam crossing or to an
ambient mechanism. The `Fin` index prevents an attribution outside the
session's crossing count. -/
inductive Origin (crossings : Nat) where
  | crossing (index : Fin crossings)
  | ambient
  deriving DecidableEq, Repr

/-- One coeffect and its origin. -/
structure Obligation (crossings : Nat) where
  origin : Origin crossings
  demand : Demand
  deriving DecidableEq, Repr

/-- A session keeps the existing effect and the new coeffects separate. The
type of `obligations` depends on `crossings`, so the attribution is checked by
construction. -/
structure Session where
  crossings : Nat
  obligations : List (Obligation crossings)

/-- Attach scheduling obligations to the exact effect computed by
`Cost.crossings`. The caller supplies the semantic annotations; this function
only prevents their crossing indices from drifting from the computed count. -/
def ofCost {S Seg Op : Type} [DecidableEq Seg]
    (sigma : S → Seg) (step : S → Op → S) (start : S) (ops : List Op)
    (obligations : List (Obligation (Cost.crossings sigma step start ops))) : Session where
  crossings := Cost.crossings sigma step start ops
  obligations := obligations

@[simp] theorem ofCost_crossings {S Seg Op : Type} [DecidableEq Seg]
    (sigma : S → Seg) (step : S → Op → S) (start : S) (ops : List Op)
    (obligations : List (Obligation (Cost.crossings sigma step start ops))) :
    (ofCost sigma step start ops obligations).crossings =
      Cost.crossings sigma step start ops := rfl

/-- A strategy-indexed family of annotated sessions. This is the scheduling
counterpart of `CoordEffect.Profile`: the strategy is still chosen once for the
whole session rather than minimized independently per stream. -/
abbrev SessionProfile (X : Type) := X → Session

/-- Forget the coeffects and recover the old crossing profile. -/
def SessionProfile.crossingProfile {X : Type} (P : SessionProfile X) :
    CoordEffect.Profile X := fun x => (P x).crossings

/-! ### Pointwise composition, with origins reindexed rather than erased. -/

/-- Inject an origin from the left session into a composed crossing count.
Ambient origins remain ambient; crossing indices retain their numeric index. -/
def Origin.inl {m n : Nat} : Origin m → Origin (m + n)
  | .ambient => .ambient
  | .crossing i => .crossing ⟨i.val, by omega⟩

/-- Inject an origin from the right session. Crossing indices are shifted past
all left-session crossings; ambient origins again remain ambient. -/
def Origin.inr {m n : Nat} : Origin n → Origin (m + n)
  | .ambient => .ambient
  | .crossing i => .crossing ⟨m + i.val, by omega⟩

@[simp] theorem Origin.inl_ambient {m n : Nat} :
    Origin.inl (m := m) (n := n) .ambient = .ambient := rfl

@[simp] theorem Origin.inr_ambient {m n : Nat} :
    Origin.inr (m := m) (n := n) .ambient = .ambient := rfl

/-- Forget only the `Fin` proof, for auditing reindexing. -/
def Origin.index? {n : Nat} : Origin n → Option Nat
  | .crossing i => some i.val
  | .ambient => none

/-- Left crossing indices are preserved numerically. -/
@[simp] theorem Origin.index_inl {m n : Nat} (o : Origin m) :
    (o.inl (n := n)).index? = o.index? := by
  cases o <;> rfl

/-- Right crossing indices are shifted by the full left crossing count. -/
@[simp] theorem Origin.index_inr {m n : Nat} (o : Origin n) :
    (o.inr (m := m)).index? = o.index?.map (fun i => m + i) := by
  cases o <;> rfl

/-- Reindex a left coeffect without changing its demand. -/
def Obligation.inl {m n : Nat} (o : Obligation m) : Obligation (m + n) where
  origin := o.origin.inl
  demand := o.demand

/-- Reindex a right coeffect without changing its demand. -/
def Obligation.inr {m n : Nat} (o : Obligation n) : Obligation (m + n) where
  origin := o.origin.inr
  demand := o.demand

@[simp] theorem Obligation.inl_demand {m n : Nat} (o : Obligation m) :
    (o.inl (n := n)).demand = o.demand := rfl

@[simp] theorem Obligation.inr_demand {m n : Nat} (o : Obligation n) :
    (o.inr (m := m)).demand = o.demand := rfl

/-- **Compose effects and coeffects.** Crossing effects add; obligations append
after their origins are injected into the summed crossing space. Nothing is
minimized and no origin is forgotten. -/
def Session.comp (p q : Session) : Session where
  crossings := p.crossings + q.crossings
  obligations :=
    p.obligations.map (Obligation.inl (n := q.crossings))
      ++ q.obligations.map (Obligation.inr (m := p.crossings))

@[simp] theorem Session.comp_crossings (p q : Session) :
    (p.comp q).crossings = p.crossings + q.crossings := rfl

/-- Composition at a strategy profile is pointwise: both workloads are kept
under the same `x`. -/
def SessionProfile.comp {X : Type} (P Q : SessionProfile X) : SessionProfile X :=
  fun x => (P x).comp (Q x)

/-- Forgetting the coeffects recovers `CoordEffect`'s pointwise-additive
profile exactly. -/
theorem SessionProfile.crossingProfile_comp {X : Type} (P Q : SessionProfile X) :
    (P.comp Q).crossingProfile =
      CoordEffect.Profile.comp P.crossingProfile Q.crossingProfile := rfl

/-! ## §3. Schedule witnesses and witnessed upper bounds. -/

/-- A schedule is a list of coordination actions and a proof that every
coeffect is discharged. An action may cover several compatible obligations;
that is coalescing, stated in the type rather than inferred from a count. -/
structure Schedule (s : Session) where
  actions : List Demand
  covers : ∀ o ∈ s.obligations, ∃ a ∈ actions, Compatible a o.demand

/-- Actions in one currency. -/
def Schedule.actionsFor {s : Session} (p : Schedule s) (c : Currency) : List Demand :=
  p.actions.filter (fun d => d.currency == c)

/-- The schedule's multi-currency price. No total is defined. -/
def Schedule.profile {s : Session} (p : Schedule s) : Currency → Nat :=
  fun c => (p.actionsFor c).length

/-- Peer meetings are exactly the peer-barrier coordinate, not all actions. -/
def Schedule.peerMeetingCount {s : Session} (p : Schedule s) : Nat :=
  p.profile .peerBarrier

/-- The identity schedule: one action per obligation. This gives a general,
possibly loose upper-bound witness. -/
def identitySchedule (s : Session) : Schedule s where
  actions := s.obligations.map Obligation.demand
  covers := by
    intro o ho
    exact ⟨o.demand, List.mem_map.mpr ⟨o, ho, rfl⟩, compatible_refl _⟩

private theorem filter_length_le {A : Type} (p : A → Bool) :
    ∀ xs : List A, (xs.filter p).length ≤ xs.length := by
  intro xs
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      cases h : p x <;> simp [List.filter, h] <;> omega

/-- The identity schedule proves that peer meetings never exceed the number of
obligations. This is an upper bound, not a claim of optimality. -/
theorem identity_meeting_upper (s : Session) :
    (identitySchedule s).peerMeetingCount ≤ s.obligations.length := by
  unfold Schedule.peerMeetingCount Schedule.profile Schedule.actionsFor
  change ((s.obligations.map Obligation.demand).filter
    (fun d => d.currency == Currency.peerBarrier)).length ≤ s.obligations.length
  have h := filter_length_le (fun d : Demand => d.currency == Currency.peerBarrier)
    (s.obligations.map Obligation.demand)
  simpa using h

/-- A meeting plan is an exhibited schedule. Like `Budget.Plan`, its cost is
computed from the witness rather than supplied independently. -/
structure Plan (s : Session) where
  schedule : Schedule s

def Plan.meetings {s : Session} (p : Plan s) : Nat :=
  p.schedule.peerMeetingCount

def Plan.profile {s : Session} (p : Plan s) : Currency → Nat :=
  p.schedule.profile

/-- Acceptance of a meeting budget requires a schedule and a proof that its
computed peer-meeting coordinate fits. -/
structure UpperBound (s : Session) (budget : Nat) where
  plan : Plan s
  fits : plan.meetings ≤ budget

/-- A five-currency acceptance witness. One real schedule plan must satisfy
every coordinate; no scalar crossing count, peer-meeting floor, or independently
chosen per-currency plans can inhabit this structure. -/
structure ProfileUpperBound (s : Session) (limits : Currency → Nat) where
  plan : Plan s
  fits : ∀ c, plan.profile c ≤ limits c

/-- Construct a profile bound from an exhibited plan and pointwise evidence. -/
def Plan.profileUpperBound {s : Session} (plan : Plan s)
    (limits : Currency → Nat) (fits : ∀ c, plan.profile c ≤ limits c) :
    ProfileUpperBound s limits :=
  ⟨plan, fits⟩

/-- Every real plan witnesses its exact achieved currency profile. -/
def Plan.exactProfileUpperBound {s : Session} (plan : Plan s) :
    ProfileUpperBound s plan.profile :=
  plan.profileUpperBound plan.profile (fun _ => Nat.le_refl _)

/-- Recover the checked schedule carried by a profile acceptance. -/
def ProfileUpperBound.schedule {s : Session} {limits : Currency → Nat}
    (bound : ProfileUpperBound s limits) : Schedule s :=
  bound.plan.schedule

/-- Compatibility projection: a full profile acceptance implies the existing
peer-only upper bound. The reverse direction is intentionally absent because a
peer limit says nothing about the other four currencies. -/
def ProfileUpperBound.toUpperBound {s : Session} {limits : Currency → Nat}
    (bound : ProfileUpperBound s limits) : UpperBound s (limits .peerBarrier) where
  plan := bound.plan
  fits := bound.fits .peerBarrier

/-! ### Sound witnessed composition -/

/-- Append two real schedules for a composed session. This may miss possible
cross-session coalescing, but it is always a sound exhibited schedule. -/
def Schedule.comp {left right : Session} (p : Schedule left) (q : Schedule right) :
    Schedule (left.comp right) where
  actions := p.actions ++ q.actions
  covers := by
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ho
      obtain ⟨a, ha, hcompat⟩ := p.covers original horiginal
      exact ⟨a, List.mem_append.mpr (Or.inl ha), by simpa using hcompat⟩
    · obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ho
      obtain ⟨a, ha, hcompat⟩ := q.covers original horiginal
      exact ⟨a, List.mem_append.mpr (Or.inr ha), by simpa using hcompat⟩

/-- Appended schedules add every currency coordinate exactly. -/
theorem Schedule.profile_comp {left right : Session} (p : Schedule left)
    (q : Schedule right) (currency : Currency) :
    (p.comp q).profile currency = p.profile currency + q.profile currency := by
  simp [Schedule.comp, Schedule.profile, Schedule.actionsFor, List.filter_append]

def Plan.comp {left right : Session} (p : Plan left) (q : Plan right) :
    Plan (left.comp right) :=
  ⟨p.schedule.comp q.schedule⟩

theorem Plan.profile_comp {left right : Session} (p : Plan left) (q : Plan right)
    (currency : Currency) :
    (p.comp q).profile currency = p.profile currency + q.profile currency :=
  Schedule.profile_comp p.schedule q.schedule currency

/-- Pointwise limits compose only through the one appended real plan. This is
an achieved upper bound, not a claim that optimal profiles distribute. -/
def ProfileUpperBound.comp {left right : Session}
    {leftLimits rightLimits : Currency → Nat}
    (p : ProfileUpperBound left leftLimits)
    (q : ProfileUpperBound right rightLimits) :
    ProfileUpperBound (left.comp right) (fun c => leftLimits c + rightLimits c) where
  plan := p.plan.comp q.plan
  fits := by
    intro c
    rw [Plan.profile_comp]
    exact Nat.add_le_add (p.fits c) (q.fits c)

/-- The conservative one-action-per-obligation plan, exposed independently of
either scalar or profile bounds. -/
def identityPlan (s : Session) : Plan s :=
  ⟨identitySchedule s⟩

/-- Every session has an exact profile acceptance for the profile actually
spent by its conservative identity plan. -/
def identityProfileUpperBound (s : Session) :
    ProfileUpperBound s (identityPlan s).profile :=
  (identityPlan s).exactProfileUpperBound

/-- Every session has a witnessed, conservative upper bound: one peer meeting
per obligation. -/
def identityUpperBound (s : Session) : UpperBound s s.obligations.length where
  plan := identityPlan s
  fits := identity_meeting_upper s

/-- A least meeting count is both achieved and a lower bound on every schedule.
This is the standard against which the examples below are exact. -/
def LeastMeetings (s : Session) (n : Nat) : Prop :=
  (∃ p : Plan s, p.meetings = n) ∧ ∀ p : Plan s, n ≤ p.meetings

/-- A witnessed upper bound really bounds the least count. -/
theorem least_le_upper {s : Session} {least budget : Nat}
    (hl : LeastMeetings s least) (hu : UpperBound s budget) : least ≤ budget := by
  have hleast : least ≤ hu.plan.meetings := hl.2 hu.plan
  exact Nat.le_trans hleast hu.fits

/-! ### A composed profile chooses one strategy, after composition. -/

/-- A plan for a strategy-indexed problem. The strategy membership proof and
the schedule travel together; there is no pair of independently selected
strategies to reconcile afterward. -/
structure ProfilePlan {X : Type} (A : CoordEffect.Admissible X)
    (P : SessionProfile X) where
  strategy : X
  admissible : strategy ∈ A.toList
  schedule : Schedule (P strategy)

/-- Restrict a schedule for a composed session to its left coeffects. The same
actions are retained, and coverage follows through the checked left injection. -/
def Schedule.compLeft {p q : Session} (s : Schedule (p.comp q)) : Schedule p where
  actions := s.actions
  covers := by
    intro o ho
    have hm : o.inl (n := q.crossings) ∈
        p.obligations.map (Obligation.inl (n := q.crossings)) :=
      List.mem_map.mpr ⟨o, ho, rfl⟩
    have hc : o.inl (n := q.crossings) ∈ (p.comp q).obligations :=
      List.mem_append.mpr (Or.inl hm)
    obtain ⟨a, ha, hcompat⟩ := s.covers _ hc
    exact ⟨a, ha, hcompat⟩

/-- The right restriction, shifting crossing origins in the coverage proof. -/
def Schedule.compRight {p q : Session} (s : Schedule (p.comp q)) : Schedule q where
  actions := s.actions
  covers := by
    intro o ho
    have hm : o.inr (m := p.crossings) ∈
        q.obligations.map (Obligation.inr (m := p.crossings)) :=
      List.mem_map.mpr ⟨o, ho, rfl⟩
    have hc : o.inr (m := p.crossings) ∈ (p.comp q).obligations :=
      List.mem_append.mpr (Or.inr hm)
    obtain ⟨a, ha, hcompat⟩ := s.covers _ hc
    exact ⟨a, ha, hcompat⟩

/-- The left workload reads the composed plan at the composed plan's one
strategy. -/
def ProfilePlan.left {X : Type} {A : CoordEffect.Admissible X}
    {P Q : SessionProfile X} (p : ProfilePlan A (P.comp Q)) : ProfilePlan A P where
  strategy := p.strategy
  admissible := p.admissible
  schedule := p.schedule.compLeft

/-- The right workload reads the same strategy. -/
def ProfilePlan.right {X : Type} {A : CoordEffect.Admissible X}
    {P Q : SessionProfile X} (p : ProfilePlan A (P.comp Q)) : ProfilePlan A Q where
  strategy := p.strategy
  admissible := p.admissible
  schedule := p.schedule.compRight

/-- **Composed selection is shared, never independent.** Both restrictions of
one composed plan definitionally retain the single strategy chosen only after
the coeffects were composed pointwise. -/
theorem composed_plan_uses_one_strategy {X : Type} {A : CoordEffect.Admissible X}
    {P Q : SessionProfile X} (p : ProfilePlan A (P.comp Q)) :
    p.left.strategy = p.strategy ∧ p.right.strategy = p.strategy :=
  ⟨rfl, rfl⟩

/-! ### Coverage lemmas used by the exact examples. -/

/-- Coverage of an obligation forces an action in that obligation's currency.
This is the pointwise lower-bound fact used below; it does not collapse the
five coordinates to a scalar. -/
theorem Schedule.currency_action_of_covers {s : Session} (p : Schedule s)
    {o : Obligation s.crossings} (ho : o ∈ s.obligations) (currency : Currency)
    (hc : o.demand.currency = currency) :
    ∃ a ∈ p.actionsFor currency, Compatible a o.demand := by
  obtain ⟨a, ha, hcompat⟩ := p.covers o ho
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hcompat⟩
  have hcurrency : a.currency = currency := hcompat.1.trans hc
  simp [hcurrency]

theorem Schedule.peer_action_of_covers {s : Session} (p : Schedule s)
    {o : Obligation s.crossings} (ho : o ∈ s.obligations)
    (hc : o.demand.currency = .peerBarrier) :
    ∃ a ∈ p.actionsFor .peerBarrier, Compatible a o.demand := by
  exact p.currency_action_of_covers ho .peerBarrier hc

private theorem two_le_length_of_distinct_mem {A : Type} {xs : List A} {a b : A}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : 2 ≤ xs.length := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
      rw [List.mem_cons] at ha hb
      rcases ha with hax | ha
      · rcases hb with hbx | hb
        · exact absurd (hax.trans hbx.symm) hne
        · have hpos : 0 < xs.length := List.length_pos_of_mem hb
          simp
          omega
      · rcases hb with hbx | hb
        · have hpos : 0 < xs.length := List.length_pos_of_mem ha
          simp
          omega
        · have htail := ih ha hb
          simp
          omega

theorem one_peer_obligation_forces_one {s : Session}
    {o : Obligation s.crossings} (ho : o ∈ s.obligations)
    (hc : o.demand.currency = .peerBarrier) (p : Plan s) :
    1 ≤ p.meetings := by
  obtain ⟨a, ha, -⟩ := p.schedule.peer_action_of_covers ho hc
  exact List.length_pos_of_mem ha

/-- The corresponding lower bound for any of the five currencies. -/
theorem one_currency_obligation_forces_one {s : Session}
    {o : Obligation s.crossings} (ho : o ∈ s.obligations)
    (currency : Currency) (hc : o.demand.currency = currency) (p : Plan s) :
    1 ≤ p.profile currency := by
  obtain ⟨a, ha, -⟩ := p.schedule.currency_action_of_covers ho currency hc
  exact List.length_pos_of_mem ha

theorem two_incompatible_peer_obligations_force_two {s : Session}
    {o₁ o₂ : Obligation s.crossings}
    (h₁ : o₁ ∈ s.obligations) (h₂ : o₂ ∈ s.obligations)
    (hc₁ : o₁.demand.currency = .peerBarrier)
    (hc₂ : o₂.demand.currency = .peerBarrier)
    (hbad : ¬ Compatible o₁.demand o₂.demand) (p : Plan s) :
    2 ≤ p.meetings := by
  obtain ⟨a, ha, hca⟩ := p.schedule.peer_action_of_covers h₁ hc₁
  obtain ⟨b, hb, hcb⟩ := p.schedule.peer_action_of_covers h₂ hc₂
  have hne : a ≠ b := by
    intro hab
    apply hbad
    have haeq : a = o₁.demand := compatible_iff_eq.mp hca
    have hbeq : b = o₂.demand := compatible_iff_eq.mp hcb
    rw [← haeq, ← hbeq, hab]
    exact compatible_refl _
  exact two_le_length_of_distinct_mem ha hb hne

/-! ## §4. Concrete schedules: crossings do not determine meetings. -/

def sharedDemand : Demand := baseDemand

def secondRoundDemand : Demand := { baseDemand with round := 1 }

def networkDemand : Demand := { baseDemand with currency := .networkRound }

def arbiterDemand : Demand := { baseDemand with currency := .arbiterCut }

def promptDemand : Demand := { baseDemand with currency := .userPrompt }

def rollbackDemand : Demand := { baseDemand with currency := .rollback }

def sharedNeed₀ : Obligation 2 where
  origin := .crossing ⟨0, by decide⟩
  demand := sharedDemand

def sharedNeed₁ : Obligation 2 where
  origin := .crossing ⟨1, by decide⟩
  demand := sharedDemand

/-- Two seam crossings request the same barrier. -/
def coalescingSession : Session where
  crossings := 2
  obligations := [sharedNeed₀, sharedNeed₁]

/-- One action discharges both compatible coeffects. -/
def coalescedPlan : Plan coalescingSession where
  schedule := {
    actions := [sharedDemand]
    covers := by
      intro o ho
      change o ∈ [sharedNeed₀, sharedNeed₁] at ho
      rcases List.mem_cons.mp ho with h | h
      · subst o
        exact ⟨sharedDemand, by simp, compatible_refl _⟩
      · have h' : o = sharedNeed₁ := List.mem_singleton.mp h
        subst o
        exact ⟨sharedDemand, by simp, compatible_refl _⟩ }

theorem coalescing_least_is_one : LeastMeetings coalescingSession 1 := by
  constructor
  · exact ⟨coalescedPlan, rfl⟩
  · intro p
    exact one_peer_obligation_forces_one (o := sharedNeed₀)
      List.mem_cons_self rfl p

/-- **Crossings can exceed meetings.** This is coalescing, with both numbers
exact rather than merely bounded. -/
theorem crossings_can_exceed_meetings :
    coalescingSession.crossings = 2
      ∧ LeastMeetings coalescingSession 1
      ∧ 1 < coalescingSession.crossings :=
  ⟨rfl, coalescing_least_is_one, by decide⟩

/-- A peer barrier not caused by any seam crossing. -/
def ambientNeed : Obligation 0 where
  origin := .ambient
  demand := sharedDemand

def ambientBarrierSession : Session where
  crossings := 0
  obligations := [ambientNeed]

def ambientPlan : Plan ambientBarrierSession where
  schedule := {
    actions := [sharedDemand]
    covers := by
      intro o ho
      change o ∈ [ambientNeed] at ho
      have h : o = ambientNeed := List.mem_singleton.mp ho
      subst o
      exact ⟨sharedDemand, by simp, compatible_refl _⟩ }

theorem ambient_least_is_one : LeastMeetings ambientBarrierSession 1 := by
  constructor
  · exact ⟨ambientPlan, rfl⟩
  · intro p
    exact one_peer_obligation_forces_one (o := ambientNeed)
      List.mem_cons_self rfl p

/-- **Meetings can exceed crossings.** A checkpoint-style ambient barrier is a
real peer meeting at crossing count zero. -/
theorem meetings_can_exceed_crossings :
    ambientBarrierSession.crossings = 0
      ∧ LeastMeetings ambientBarrierSession 1
      ∧ ambientBarrierSession.crossings < 1 :=
  ⟨rfl, ambient_least_is_one, by decide⟩

def emptySession : Session where
  crossings := 0
  obligations := []

def emptyPlan : Plan emptySession where
  schedule := {
    actions := []
    covers := by intro o ho; cases ho }

theorem empty_least_is_zero : LeastMeetings emptySession 0 := by
  constructor
  · exact ⟨emptyPlan, rfl⟩
  · intro p
    exact Nat.zero_le _

/-- **The decisive refutation:** equal crossing counts, unequal exact meeting
counts. Hence no function of the crossing `Nat` alone can recover the least
meeting count for both sessions. -/
theorem same_crossings_different_least_meetings :
    emptySession.crossings = ambientBarrierSession.crossings
      ∧ LeastMeetings emptySession 0
      ∧ LeastMeetings ambientBarrierSession 1
      ∧ (0 : Nat) ≠ 1 :=
  ⟨rfl, empty_least_is_zero, ambient_least_is_one, by decide⟩

/-- **Crossing count does not determine the least meeting count.** This is the
explicit non-function form of the preceding witness: any proposed function
must send the same input `0` to both `0` and `1`. -/
theorem no_crossing_count_determines_least_meetings :
    ¬ ∃ f : Nat → Nat, ∀ (s : Session) (n : Nat),
      LeastMeetings s n → f s.crossings = n := by
  rintro ⟨f, h⟩
  have hzero := h emptySession 0 empty_least_is_zero
  have hone := h ambientBarrierSession 1 ambient_least_is_one
  change f 0 = 0 at hzero
  change f 0 = 1 at hone
  omega

/-- Nor does the least peer-meeting count determine the crossing count. The
same exact optimum `1` is realised by an ambient demand at zero crossings and
by two coalesced demands at two crossings. -/
theorem no_least_meeting_count_determines_crossings :
    ¬ ∃ f : Nat → Nat, ∀ (s : Session) (n : Nat),
      LeastMeetings s n → f n = s.crossings := by
  rintro ⟨f, h⟩
  have hambient := h ambientBarrierSession 1 ambient_least_is_one
  have hcoalesced := h coalescingSession 1 coalescing_least_is_one
  change f 1 = 0 at hambient
  change f 1 = 2 at hcoalesced
  omega

def roundNeed₀ : Obligation 1 where
  origin := .crossing ⟨0, by decide⟩
  demand := sharedDemand

def roundNeed₁ : Obligation 1 where
  origin := .crossing ⟨0, by decide⟩
  demand := secondRoundDemand

/-- One crossing may carry a two-round protocol. -/
def twoRoundSession : Session where
  crossings := 1
  obligations := [roundNeed₀, roundNeed₁]

def twoRoundPlan : Plan twoRoundSession where
  schedule := {
    actions := [sharedDemand, secondRoundDemand]
    covers := by
      intro o ho
      change o ∈ [roundNeed₀, roundNeed₁] at ho
      rcases List.mem_cons.mp ho with h | h
      · subst o
        exact ⟨sharedDemand, by simp, compatible_refl _⟩
      · have h' : o = roundNeed₁ := List.mem_singleton.mp h
        subst o
        exact ⟨secondRoundDemand, by simp, compatible_refl _⟩ }

theorem one_crossing_two_rounds_least : LeastMeetings twoRoundSession 2 := by
  constructor
  · exact ⟨twoRoundPlan, rfl⟩
  · intro p
    exact two_incompatible_peer_obligations_force_two
      (o₁ := roundNeed₀) (o₂ := roundNeed₁)
      List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) rfl rfl
      (by simp [Compatible, roundNeed₀, roundNeed₁, sharedDemand,
        secondRoundDemand, baseDemand]) p

/-- Round compatibility is operationally load-bearing: one crossing, exactly
two meetings. -/
theorem one_crossing_can_need_two_rounds :
    twoRoundSession.crossings = 1
      ∧ LeastMeetings twoRoundSession 2
      ∧ twoRoundSession.crossings < 2 :=
  ⟨rfl, one_crossing_two_rounds_least, by decide⟩

/-! ### Calibration against the existing effect counter. -/

/-- A stream operation which crosses the identity seam exactly once. -/
def advance (_state : Nat) (_op : Unit) : Nat := _state + 1

/-- The example crossing fields are not free-standing annotations: each is
realised by `Cost.crossings` on an explicit stream. The ambient session shares
the empty stream's zero effect while retaining its independent coeffect. -/
theorem examples_are_real_Cost_crossings :
    coalescingSession.crossings =
        Cost.crossings id advance 0 [(), ()]
      ∧ twoRoundSession.crossings =
        Cost.crossings id advance 0 [()]
      ∧ emptySession.crossings =
        Cost.crossings id advance 0 []
      ∧ ambientBarrierSession.crossings =
        Cost.crossings id advance 0 [] := by
  decide

/-! ## §5. A meeting scalar still cannot erase the other currencies. -/

def oneCrossingPeerSession : Session where
  crossings := 1
  obligations := [roundNeed₀]

def oneCrossingPeerPlan : Plan oneCrossingPeerSession where
  schedule := {
    actions := [sharedDemand]
    covers := by
      intro o ho
      change o ∈ [roundNeed₀] at ho
      have h : o = roundNeed₀ := List.mem_singleton.mp ho
      subst o
      exact ⟨sharedDemand, by simp, compatible_refl _⟩ }

def networkNeed : Obligation 1 where
  origin := .crossing ⟨0, by decide⟩
  demand := networkDemand

def mixedCurrencySession : Session where
  crossings := 1
  obligations := [roundNeed₀, networkNeed]

def mixedCurrencyPlan : Plan mixedCurrencySession where
  schedule := {
    actions := [sharedDemand, networkDemand]
    covers := by
      intro o ho
      change o ∈ [roundNeed₀, networkNeed] at ho
      rcases List.mem_cons.mp ho with h | h
      · subst o
        exact ⟨sharedDemand, by simp, compatible_refl _⟩
      · have h' : o = networkNeed := List.mem_singleton.mp h
        subst o
        exact ⟨networkDemand, by simp, compatible_refl _⟩ }

/-- Two witnessed plans can have the same crossing count and the same peer
meeting count while differing in another currency. A scalar `meetings` field
would therefore recreate `Repair.Price`'s rejected collapse. -/
theorem meetings_cannot_erase_currency :
    oneCrossingPeerSession.crossings = mixedCurrencySession.crossings
      ∧ oneCrossingPeerPlan.meetings = mixedCurrencyPlan.meetings
      ∧ oneCrossingPeerPlan.profile .networkRound = 0
      ∧ mixedCurrencyPlan.profile .networkRound = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §6. Five-currency acceptance and its non-constructibility bars. -/

/-- Merely asserting that a profile bound exists, while keeping its real plan
available through `Nonempty`. -/
def HasProfileUpperBound (s : Session) (limits : Currency → Nat) : Prop :=
  Nonempty (ProfileUpperBound s limits)

/-- A zero allowance in every currency. -/
def zeroLimits : Currency → Nat := fun _ => 0

/-- One peer barrier, and no expenditure in the other four currencies. -/
def peerOnlyLimits : Currency → Nat
  | .peerBarrier => 1
  | _ => 0

/-- Two peer barriers, and no expenditure in the other four currencies. -/
def twoPeerLimits : Currency → Nat
  | .peerBarrier => 2
  | _ => 0

/-- One action in each of the five currencies. -/
def oneEachLimits : Currency → Nat := fun _ => 1

def arbiterNeed : Obligation 0 where
  origin := .ambient
  demand := arbiterDemand

def networkAmbientNeed : Obligation 0 where
  origin := .ambient
  demand := networkDemand

def promptNeed : Obligation 0 where
  origin := .ambient
  demand := promptDemand

def rollbackNeed : Obligation 0 where
  origin := .ambient
  demand := rollbackDemand

/-- A single session which requires all five currencies. -/
def allCurrenciesSession : Session where
  crossings := 0
  obligations := [ambientNeed, arbiterNeed, networkAmbientNeed, promptNeed, rollbackNeed]

def allCurrenciesPlan : Plan allCurrenciesSession :=
  identityPlan allCurrenciesSession

/-- The all-currency example is accepted by one real plan, checked pointwise. -/
def allCurrenciesProfileUpperBound :
    ProfileUpperBound allCurrenciesSession oneEachLimits :=
  allCurrenciesPlan.profileUpperBound oneEachLimits (by
    intro currency
    cases currency <;> decide)

/-- All five coordinates of the checked plan are observable and exactly one. -/
theorem allCurrenciesProfileUpperBound_exercises_every_currency :
    allCurrenciesProfileUpperBound.plan.profile .peerBarrier = 1
      ∧ allCurrenciesProfileUpperBound.plan.profile .arbiterCut = 1
      ∧ allCurrenciesProfileUpperBound.plan.profile .networkRound = 1
      ∧ allCurrenciesProfileUpperBound.plan.profile .userPrompt = 1
      ∧ allCurrenciesProfileUpperBound.plan.profile .rollback = 1 := by
  decide

/-- The historical two-crossings-to-one-meeting example has a full profile
acceptance, not merely a scalar peer bound. -/
def coalescedProfileUpperBound :
    ProfileUpperBound coalescingSession peerOnlyLimits :=
  coalescedPlan.profileUpperBound peerOnlyLimits (by
    intro currency
    cases currency <;> decide)

/-- The historical one-crossing-to-two-rounds example likewise carries one
real plan whose peer coordinate is exactly two. -/
def twoRoundProfileUpperBound :
    ProfileUpperBound twoRoundSession twoPeerLimits :=
  twoRoundPlan.profileUpperBound twoPeerLimits (by
    intro currency
    cases currency <;> decide)

theorem crossing_meeting_examples_have_profile_bounds :
    coalescingSession.crossings = 2
      ∧ LeastMeetings coalescingSession 1
      ∧ coalescedProfileUpperBound.plan.profile .peerBarrier = 1
      ∧ twoRoundSession.crossings = 1
      ∧ LeastMeetings twoRoundSession 2
      ∧ twoRoundProfileUpperBound.plan.profile .peerBarrier = 2 :=
  ⟨rfl, coalescing_least_is_one, rfl, rfl, one_crossing_two_rounds_least, rfl⟩

def emptyZeroProfileUpperBound :
    ProfileUpperBound emptySession zeroLimits :=
  emptyPlan.profileUpperBound zeroLimits (by
    intro currency
    cases currency <;> decide)

/-- A zero-crossing session may fail the zero profile budget: the ambient peer
obligation forces a real peer action. -/
theorem ambient_has_no_zero_profile_bound :
    ¬ HasProfileUpperBound ambientBarrierSession zeroLimits := by
  rintro ⟨bound⟩
  have hlower : 1 ≤ bound.plan.profile .peerBarrier :=
    one_currency_obligation_forces_one (o := ambientNeed)
      List.mem_cons_self .peerBarrier rfl bound.plan
  have hupper := bound.fits .peerBarrier
  simp only [zeroLimits] at hupper
  omega

/-- **Crossings cannot construct profile acceptance.** Two sessions with the
same crossing count disagree on acceptance at the same five-currency limit. -/
theorem no_crossing_count_decides_profile_acceptance :
    ¬ ∃ accepts : Nat → Bool, ∀ s : Session,
      accepts s.crossings = true ↔ HasProfileUpperBound s zeroLimits := by
  rintro ⟨accepts, haccepts⟩
  have hempty : accepts emptySession.crossings = true :=
    (haccepts emptySession).2 ⟨emptyZeroProfileUpperBound⟩
  have hambient : accepts ambientBarrierSession.crossings = true := by
    simpa using hempty
  exact ambient_has_no_zero_profile_bound ((haccepts ambientBarrierSession).1 hambient)

theorem oneCrossingPeer_least_is_one :
    LeastMeetings oneCrossingPeerSession 1 := by
  constructor
  · exact ⟨oneCrossingPeerPlan, rfl⟩
  · intro plan
    exact one_peer_obligation_forces_one (o := roundNeed₀)
      List.mem_cons_self rfl plan

theorem mixedCurrency_least_is_one :
    LeastMeetings mixedCurrencySession 1 := by
  constructor
  · exact ⟨mixedCurrencyPlan, rfl⟩
  · intro plan
    exact one_peer_obligation_forces_one (o := roundNeed₀)
      List.mem_cons_self rfl plan

def oneCrossingPeerProfileUpperBound :
    ProfileUpperBound oneCrossingPeerSession peerOnlyLimits :=
  oneCrossingPeerPlan.profileUpperBound peerOnlyLimits (by
    intro currency
    cases currency <;> decide)

/-- A peer-only allowance cannot hide the required network action. -/
theorem mixedCurrency_has_no_peerOnly_profile_bound :
    ¬ HasProfileUpperBound mixedCurrencySession peerOnlyLimits := by
  rintro ⟨bound⟩
  have hlower : 1 ≤ bound.plan.profile .networkRound :=
    one_currency_obligation_forces_one (o := networkNeed)
      (List.mem_cons_of_mem _ List.mem_cons_self) .networkRound rfl bound.plan
  have hupper := bound.fits .networkRound
  simp only [peerOnlyLimits] at hupper
  omega

/-- **Least peer meetings cannot construct profile acceptance.** Both sessions
have exact least peer count one; only the first fits the same full profile. -/
theorem least_meetings_do_not_decide_profile_acceptance :
    LeastMeetings oneCrossingPeerSession 1
      ∧ LeastMeetings mixedCurrencySession 1
      ∧ HasProfileUpperBound oneCrossingPeerSession peerOnlyLimits
      ∧ ¬ HasProfileUpperBound mixedCurrencySession peerOnlyLimits :=
  ⟨oneCrossingPeer_least_is_one, mixedCurrency_least_is_one,
    ⟨oneCrossingPeerProfileUpperBound⟩, mixedCurrency_has_no_peerOnly_profile_bound⟩

/-- A peer-meeting floor is universal lower-bound evidence only. -/
def MeetingFloor (s : Session) (floor : Nat) : Prop :=
  ∀ plan : Plan s, floor ≤ plan.meetings

theorem LeastMeetings.toMeetingFloor {s : Session} {least : Nat}
    (h : LeastMeetings s least) : MeetingFloor s least :=
  h.2

/-- **A floor cannot construct profile acceptance.** This session has a proved
peer floor fitting the peer allowance, but fails the full allowance because of
its independently checked network coordinate. -/
theorem meeting_floor_does_not_entail_profile_acceptance :
    MeetingFloor mixedCurrencySession 1
      ∧ 1 ≤ peerOnlyLimits .peerBarrier
      ∧ ¬ HasProfileUpperBound mixedCurrencySession peerOnlyLimits :=
  ⟨mixedCurrency_least_is_one.toMeetingFloor, by decide,
    mixedCurrency_has_no_peerOnly_profile_bound⟩

end Uwueave.Scheduling
