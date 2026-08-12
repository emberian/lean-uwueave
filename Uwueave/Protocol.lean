/-
# Uwueave.Protocol — protocol/session AST with proof-carrying scheduling elaboration.

`Scheduling.lean` deliberately stops before syntax: a caller may construct a
fully annotated `Session`, but there is no language for composing operations,
parallel regions, choices, repetition, and synchronization. This module adds
that semantic language without weakening Scheduling's distinction between seam
crossings (effects) and coordination demands (coeffects).

The strategy parameter is global. `Term.denote` receives it once and passes the
same value through sequential and parallel composition, the chosen finite
branch, and every repetition. The resulting `Term.profile` is a
`Scheduling.SessionProfile`; composition is pointwise, never a sum of minima
from independently chosen strategies.

Elaboration is proof-carrying. `elaborate` returns a session tied by equality to
the AST semantics, a checked `Schedule`, and its proved identity-schedule bound.
The bundle exposes the corresponding `Scheduling.Plan` and `UpperBound` without
inventing a meeting count.

This module remains the parser-independent semantic layer. The downstream
`Uwueave.Preo.ProtocolSurface` command now parses native `.operation`, `.seq`,
`.parallel`, `.choice`, `.repeat`, and `.sync` forms and emits predictable
`N.Term`, `N.Elaboration`, `N.Session`, `N.Plan`, `N.Limits`, and
`N.ProfileUpperBound` values through this API. Its `NativeFixture` proves the
exact session shape, complete seven-axis demand stream, and five-currency
profile; `NativeCoalescing` and `NativeAmbient` replay both directions of the
crossings-versus-meetings refutation. Operation leaves here remain semantic
primitives: their crossing count may depend on the one global strategy, and
their typed origins cannot point outside that count.
-/
import Uwueave.Scheduling

namespace Uwueave.Protocol

open Uwueave
open Uwueave.Scheduling

/-! ## §1. Complete scheduling annotations and operation leaves -/

/-- Source-level scheduling annotation. Every compatibility axis from
`Scheduling.Demand` is retained explicitly; none is inferred or defaulted. -/
structure Annotation where
  currency : Currency
  participants : List Nat
  scope : Nat
  epoch : Nat
  evidence : EvidenceKey
  round : Nat
  barrier : Nat
  deriving DecidableEq, Repr

/-- Forget only the source wrapper. This is a field-for-field translation. -/
def Annotation.toDemand (a : Annotation) : Demand where
  currency := a.currency
  participants := a.participants
  scope := a.scope
  epoch := a.epoch
  evidence := a.evidence
  round := a.round
  barrier := a.barrier

/-- Audit theorem: elaboration retains all seven scheduling axes exactly. -/
theorem Annotation.axes_retained (a : Annotation) :
    a.toDemand.currency = a.currency
      ∧ a.toDemand.participants = a.participants
      ∧ a.toDemand.scope = a.scope
      ∧ a.toDemand.epoch = a.epoch
      ∧ a.toDemand.evidence = a.evidence
      ∧ a.toDemand.round = a.round
      ∧ a.toDemand.barrier = a.barrier :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Annotation.toDemand_injective : Function.Injective Annotation.toDemand := by
  intro a b h
  cases a
  cases b
  simp only [Annotation.toDemand, Demand.mk.injEq] at h
  simp_all

/-- An annotated operation need with a checked origin. The `Fin` inside
`Origin.crossing` prevents a leaf from attributing a demand to a nonexistent
crossing. Ambient operation needs remain possible. -/
structure Need (crossings : Nat) where
  origin : Origin crossings
  annotation : Annotation
  deriving DecidableEq, Repr

def Need.toObligation {n : Nat} (need : Need n) : Obligation n where
  origin := need.origin
  demand := need.annotation.toDemand

@[simp] theorem Need.toObligation_demand {n : Nat} (need : Need n) :
    need.toObligation.demand = need.annotation.toDemand := rfl

/-- A primitive protocol operation. `crossings` and the type of `needs` are
indexed by the same global strategy, so semantic annotations cannot drift from
the selected operation effect. `name` is an uninterpreted stable operation id. -/
structure Operation (Strategy : Type) where
  name : Nat
  crossings : Strategy → Nat
  needs : (strategy : Strategy) → List (Need (crossings strategy))

def Operation.toSession {Strategy : Type} (op : Operation Strategy)
    (strategy : Strategy) : Session where
  crossings := op.crossings strategy
  obligations := (op.needs strategy).map Need.toObligation

@[simp] theorem Operation.toSession_crossings {Strategy : Type}
    (op : Operation Strategy) (strategy : Strategy) :
    (op.toSession strategy).crossings = op.crossings strategy := rfl

/-! ## §2. The deep protocol AST -/

/- A nonempty finite branch collection. Keeping it nonempty makes choice total;
an out-of-range selector conservatively chooses the final branch. -/
mutual
  inductive Term (Strategy : Type) where
    | operation (op : Operation Strategy)
    | seq (left right : Term Strategy)
    | parallel (left right : Term Strategy)
    | choice (site : Nat) (select : Strategy → Nat) (branches : Branches Strategy)
    | repeat (bound : Nat) (body : Term Strategy)
    | sync (annotation : Annotation)

  inductive Branches (Strategy : Type) where
    | one (last : Term Strategy)
    | more (head : Term Strategy) (tail : Branches Strategy)
end

/-- The neutral scheduling session. -/
def nilSession : Session where
  crossings := 0
  obligations := []

/-- A synchronous protocol barrier is an ambient coeffect, not a seam crossing.
Its complete annotation becomes the one demand verbatim. -/
def syncSession (annotation : Annotation) : Session where
  crossings := 0
  obligations := [{ origin := .ambient, demand := annotation.toDemand }]

/-- Execute the same already-elaborated session to the syntactic bound. This is
exact bounded repetition: bound `n` composes exactly `n` copies. -/
def repeatSession (session : Session) : Nat → Session
  | 0 => nilSession
  | n + 1 => session.comp (repeatSession session n)

/- Denotational semantics and finite-branch lookup are mutually structural.
Every recursive call receives the exact same `strategy`; choice changes the AST
branch, never the strategy. -/
mutual
  def Term.denote {Strategy : Type} : Term Strategy → Strategy → Session
    | .operation op, strategy => op.toSession strategy
    | .seq left right, strategy =>
        (left.denote strategy).comp (right.denote strategy)
    | .parallel left right, strategy =>
        (left.denote strategy).comp (right.denote strategy)
    | .choice _ select branches, strategy =>
        branches.denoteAt (select strategy) strategy
    | .repeat bound body, strategy => repeatSession (body.denote strategy) bound
    | .sync annotation, _ => syncSession annotation

  def Branches.denoteAt {Strategy : Type} :
      Branches Strategy → Nat → Strategy → Session
    | .one last, _, strategy => last.denote strategy
    | .more head _, 0, strategy => head.denote strategy
    | .more _ tail, index + 1, strategy => tail.denoteAt index strategy
end

/-- Strategy-indexed semantics, in Scheduling's native pointwise shape. -/
def Term.profile {Strategy : Type} (term : Term Strategy) : SessionProfile Strategy :=
  fun strategy => term.denote strategy

/-! ## §3. Compositional laws -/

@[simp] theorem denote_operation {Strategy : Type} (op : Operation Strategy)
    (strategy : Strategy) :
    (Term.operation op).denote strategy = op.toSession strategy := rfl

@[simp] theorem denote_seq {Strategy : Type} (left right : Term Strategy)
    (strategy : Strategy) :
    (Term.seq left right).denote strategy =
      (left.denote strategy).comp (right.denote strategy) := rfl

@[simp] theorem denote_parallel {Strategy : Type} (left right : Term Strategy)
    (strategy : Strategy) :
    (Term.parallel left right).denote strategy =
      (left.denote strategy).comp (right.denote strategy) := rfl

@[simp] theorem denote_choice {Strategy : Type} (site : Nat)
    (select : Strategy → Nat) (branches : Branches Strategy) (strategy : Strategy) :
    (Term.choice site select branches).denote strategy =
      branches.denoteAt (select strategy) strategy := rfl

@[simp] theorem denote_repeat {Strategy : Type} (bound : Nat)
    (body : Term Strategy) (strategy : Strategy) :
    (Term.repeat bound body).denote strategy =
      repeatSession (body.denote strategy) bound := rfl

@[simp] theorem denote_sync {Strategy : Type} (annotation : Annotation)
    (strategy : Strategy) :
    (Term.sync (Strategy := Strategy) annotation).denote strategy =
      syncSession annotation := rfl

/-- Sequential composition is pointwise under one strategy. -/
theorem profile_seq {Strategy : Type} (left right : Term Strategy) :
    (Term.seq left right).profile = left.profile.comp right.profile := rfl

/-- Parallel composition uses the same pointwise law and the same one strategy;
parallelism does not authorize independent per-branch strategy selection. -/
theorem profile_parallel {Strategy : Type} (left right : Term Strategy) :
    (Term.parallel left right).profile = left.profile.comp right.profile := rfl

/-- Erase checked origins while retaining every elaborated demand. -/
def sessionDemands (session : Session) : List Demand :=
  session.obligations.map Obligation.demand

/-- Session composition appends demand streams; origin reindexing changes no
annotation. -/
theorem sessionDemands_comp (left right : Session) :
    sessionDemands (left.comp right) =
      sessionDemands left ++ sessionDemands right := by
  simp [sessionDemands, Session.comp, Function.comp_def]

theorem Operation.toSession_demands {Strategy : Type} (op : Operation Strategy)
    (strategy : Strategy) :
    sessionDemands (op.toSession strategy) =
      (op.needs strategy).map (fun need => need.annotation.toDemand) := by
  simp [sessionDemands, Operation.toSession, Need.toObligation]

/-- A sync contributes exactly its fully annotated demand. -/
@[simp] theorem syncSession_demands (annotation : Annotation) :
    sessionDemands (syncSession annotation) = [annotation.toDemand] := rfl

theorem denote_seq_demands {Strategy : Type} (left right : Term Strategy)
    (strategy : Strategy) :
    sessionDemands ((Term.seq left right).denote strategy) =
      sessionDemands (left.denote strategy) ++
        sessionDemands (right.denote strategy) :=
  sessionDemands_comp _ _

theorem denote_parallel_demands {Strategy : Type} (left right : Term Strategy)
    (strategy : Strategy) :
    sessionDemands ((Term.parallel left right).denote strategy) =
      sessionDemands (left.denote strategy) ++
        sessionDemands (right.denote strategy) :=
  sessionDemands_comp _ _

@[simp] theorem repeatSession_zero (session : Session) :
    repeatSession session 0 = nilSession := rfl

@[simp] theorem repeatSession_succ (session : Session) (n : Nat) :
    repeatSession session (n + 1) = session.comp (repeatSession session n) := rfl

/-- Crossing effects add through bounded repetition. -/
theorem repeatSession_crossings (session : Session) : ∀ n : Nat,
    (repeatSession session n).crossings = n * session.crossings
  | 0 => by simp [repeatSession, nilSession]
  | n + 1 => by
      simp [repeatSession, repeatSession_crossings, Nat.succ_mul, Nat.add_comm]

/-- Demand annotations repeat by append, without being collapsed into a scalar. -/
theorem repeatSession_demands_succ (session : Session) (n : Nat) :
    sessionDemands (repeatSession session (n + 1)) =
      sessionDemands session ++ sessionDemands (repeatSession session n) := by
  rw [repeatSession_succ, sessionDemands_comp]

/-- Sequential association preserves both observable effects and all demands. -/
theorem seq_associative_observables {Strategy : Type}
    (a b c : Term Strategy) (strategy : Strategy) :
    ((Term.seq (Term.seq a b) c).denote strategy).crossings =
        ((Term.seq a (Term.seq b c)).denote strategy).crossings
      ∧ sessionDemands ((Term.seq (Term.seq a b) c).denote strategy) =
        sessionDemands ((Term.seq a (Term.seq b c)).denote strategy) := by
  constructor
  · simp only [denote_seq, Session.comp_crossings]
    omega
  · simp only [denote_seq, sessionDemands_comp, List.append_assoc]

/-! ## §4. Proof-carrying elaboration and checked artifacts -/

/-- An elaboration result carries its semantic correctness, checked schedule,
and the proof needed to form a witnessed upper bound. -/
structure Elaboration {Strategy : Type} (term : Term Strategy)
    (strategy : Strategy) where
  session : Session
  sound : session = term.denote strategy
  schedule : Schedule session
  fits : schedule.peerMeetingCount ≤ session.obligations.length

/-- Conservative elaboration: retain every obligation and exhibit one action
per obligation. Coalescing may later replace this schedule with a smaller one. -/
def elaborate {Strategy : Type} (term : Term Strategy) (strategy : Strategy) :
    Elaboration term strategy where
  session := term.denote strategy
  sound := rfl
  schedule := identitySchedule (term.denote strategy)
  fits := identity_meeting_upper (term.denote strategy)

def Elaboration.plan {Strategy : Type} {term : Term Strategy}
    {strategy : Strategy} (result : Elaboration term strategy) : Plan result.session :=
  ⟨result.schedule⟩

def Elaboration.upperBound {Strategy : Type} {term : Term Strategy}
    {strategy : Strategy} (result : Elaboration term strategy) :
    UpperBound result.session result.session.obligations.length where
  plan := result.plan
  fits := result.fits

/-- Check a caller-supplied five-currency allowance against the one real plan
carried by this elaboration. -/
def Elaboration.profileUpperBound {Strategy : Type} {term : Term Strategy}
    {strategy : Strategy} (result : Elaboration term strategy)
    (limits : Currency → Nat)
    (fits : ∀ currency, result.plan.profile currency ≤ limits currency) :
    ProfileUpperBound result.session limits :=
  result.plan.profileUpperBound limits fits

/-- The elaboration always yields a full acceptance at the exact profile of
its checked plan. -/
def Elaboration.exactProfileUpperBound {Strategy : Type} {term : Term Strategy}
    {strategy : Strategy} (result : Elaboration term strategy) :
    ProfileUpperBound result.session result.plan.profile :=
  result.plan.exactProfileUpperBound

@[simp] theorem elaborate_session {Strategy : Type} (term : Term Strategy)
    (strategy : Strategy) :
    (elaborate term strategy).session = term.denote strategy := rfl

@[simp] theorem elaborate_plan_schedule {Strategy : Type} (term : Term Strategy)
    (strategy : Strategy) :
    (elaborate term strategy).plan.schedule =
      (elaborate term strategy).schedule := rfl

@[simp] theorem elaborate_upperBound_plan {Strategy : Type} (term : Term Strategy)
    (strategy : Strategy) :
    (elaborate term strategy).upperBound.plan =
      (elaborate term strategy).plan := rfl

@[simp] theorem elaborate_exactProfileUpperBound_plan {Strategy : Type}
    (term : Term Strategy) (strategy : Strategy) :
    (elaborate term strategy).exactProfileUpperBound.plan =
      (elaborate term strategy).plan := rfl

/-- Turn a checked elaboration into Scheduling's admissible profile plan. The
strategy and its membership proof travel with the schedule. -/
def elaborateProfilePlan {Strategy : Type} (admissible : CoordEffect.Admissible Strategy)
    (term : Term Strategy) (strategy : Strategy)
    (hstrategy : strategy ∈ admissible.toList) :
    ProfilePlan admissible term.profile where
  strategy := strategy
  admissible := hstrategy
  schedule := (elaborate term strategy).schedule

/-- Build a plan for a composed profile only after selecting one admissible
strategy for the whole composition. -/
def elaborateComposedProfilePlan {Strategy : Type}
    (admissible : CoordEffect.Admissible Strategy) (left right : Term Strategy)
    (strategy : Strategy) (hstrategy : strategy ∈ admissible.toList) :
    ProfilePlan admissible (left.profile.comp right.profile) where
  strategy := strategy
  admissible := hstrategy
  schedule := identitySchedule ((left.denote strategy).comp (right.denote strategy))

/-- Both projections of an elaborated composition retain the same selected
global strategy. -/
theorem elaborated_composition_uses_one_strategy {Strategy : Type}
    (admissible : CoordEffect.Admissible Strategy) (left right : Term Strategy)
    (strategy : Strategy) (hstrategy : strategy ∈ admissible.toList) :
    let plan := elaborateComposedProfilePlan admissible left right strategy hstrategy
    plan.left.strategy = strategy ∧ plan.right.strategy = strategy := by
  simp [elaborateComposedProfilePlan, ProfilePlan.left, ProfilePlan.right]

/-! ## §5. Exact AST counterexamples: crossings are still not meetings -/

def sharedAnnotation : Annotation where
  currency := .peerBarrier
  participants := [0, 1]
  scope := 7
  epoch := 3
  evidence := .named 11
  round := 0
  barrier := 5

def secondRoundAnnotation : Annotation := { sharedAnnotation with round := 1 }

/-- Two crossing-origin annotations with the same demand coalesce. -/
def coalescingOperation : Operation Unit where
  name := 100
  crossings := fun _ => 2
  needs := fun _ =>
    [ { origin := .crossing ⟨0, by omega⟩, annotation := sharedAnnotation },
      { origin := .crossing ⟨1, by omega⟩, annotation := sharedAnnotation } ]

def coalescingProtocol : Term Unit := .operation coalescingOperation

/-- A sync has no seam crossing but still has one peer-barrier demand. -/
def ambientProtocol : Term Unit := .sync sharedAnnotation

/-- Zero bounded repetitions give an obligation-free, zero-crossing protocol. -/
def emptyProtocol : Term Unit := .repeat 0 ambientProtocol

/-- One crossing may carry two incompatible synchronization rounds. -/
def twoRoundOperation : Operation Unit where
  name := 101
  crossings := fun _ => 1
  needs := fun _ =>
    [ { origin := .crossing ⟨0, by omega⟩, annotation := sharedAnnotation },
      { origin := .crossing ⟨0, by omega⟩, annotation := secondRoundAnnotation } ]

def twoRoundProtocol : Term Unit := .operation twoRoundOperation

/-- The AST coalescing example elaborates to Scheduling's exact witness. -/
theorem coalescingProtocol_denotes :
    coalescingProtocol.denote () = Scheduling.coalescingSession := rfl

/-- The AST sync example elaborates to Scheduling's exact ambient witness. -/
theorem ambientProtocol_denotes :
    ambientProtocol.denote () = Scheduling.ambientBarrierSession := rfl

theorem emptyProtocol_denotes :
    emptyProtocol.denote () = Scheduling.emptySession := rfl

theorem twoRoundProtocol_denotes :
    twoRoundProtocol.denote () = Scheduling.twoRoundSession := rfl

/-- Two AST crossings still need exactly one meeting: crossing count is not a
meeting count after elaboration. -/
theorem ast_crossings_can_exceed_meetings :
    (coalescingProtocol.denote ()).crossings = 2
      ∧ LeastMeetings (coalescingProtocol.denote ()) 1
      ∧ 1 < (coalescingProtocol.denote ()).crossings := by
  rw [coalescingProtocol_denotes]
  exact Scheduling.crossings_can_exceed_meetings

/-- An AST sync can need one meeting at zero crossings. -/
theorem ast_meetings_can_exceed_crossings :
    (ambientProtocol.denote ()).crossings = 0
      ∧ LeastMeetings (ambientProtocol.denote ()) 1
      ∧ (ambientProtocol.denote ()).crossings < 1 := by
  rw [ambientProtocol_denotes]
  exact Scheduling.meetings_can_exceed_crossings

/-- Equal elaborated crossing counts retain unequal exact meeting optima. -/
theorem ast_same_crossings_different_least_meetings :
    (emptyProtocol.denote ()).crossings = (ambientProtocol.denote ()).crossings
      ∧ LeastMeetings (emptyProtocol.denote ()) 0
      ∧ LeastMeetings (ambientProtocol.denote ()) 1
      ∧ (0 : Nat) ≠ 1 := by
  rw [emptyProtocol_denotes, ambientProtocol_denotes]
  exact Scheduling.same_crossings_different_least_meetings

/-- Consequently no scalar function of an elaborated AST's crossing count can
recover its exact least meeting count. -/
theorem no_ast_crossing_count_determines_least_meetings :
    ¬ ∃ f : Nat → Nat, ∀ (term : Term Unit) (n : Nat),
      LeastMeetings (term.denote ()) n →
        f (term.denote ()).crossings = n := by
  rintro ⟨f, h⟩
  have hzero := h emptyProtocol 0 (by
    rw [emptyProtocol_denotes]
    exact Scheduling.empty_least_is_zero)
  have hone := h ambientProtocol 1 (by
    rw [ambientProtocol_denotes]
    exact Scheduling.ambient_least_is_one)
  change f 0 = 0 at hzero
  change f 0 = 1 at hone
  omega

/-- The opposite direction also survives: one AST crossing can force exactly
two incompatible peer meetings. -/
theorem ast_one_crossing_can_need_two_rounds :
    (twoRoundProtocol.denote ()).crossings = 1
      ∧ LeastMeetings (twoRoundProtocol.denote ()) 2
      ∧ (twoRoundProtocol.denote ()).crossings < 2 := by
  rw [twoRoundProtocol_denotes]
  exact Scheduling.one_crossing_can_need_two_rounds

end Uwueave.Protocol
