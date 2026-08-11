/-
# Uwueave.Budget — a session budget checker that may only accept on a WITNESS.

`Cost.lean` answers "how often must I coordinate?" with a **lower** bound:
`coordination_forced` says a workload whose trajectory contains `n` clash pairs
costs at least `n` crossings under every seam in every universe. The obvious
next move is a checker: compare the floor against a session budget and report.

**That checker is unsound, and codex is the one who caught it** (second P0 of
his review of this library). The shape is

    Floor(spec, W)  ≤  Cost(plan, W)  ≤  Budget

and a *lower* bound only ever licenses the LEFT comparison. `floor ≤ budget`
says the rejection argument is unavailable; it says **nothing** about whether
any plan achieves a cost the budget can pay. Achievability is an upper bound,
and an upper bound in this model is not a proof about the specification — it is
an **exhibited seam** whose crossing count is *computed*. So:

  * `accepted` **carries a `Plan` and a proof `plan.cost ≤ budget`.** There is
    no constructor that accepts on the strength of a floor. That absence is the
    entire point of the file.
  * `rejected` carries a witnessed clash decomposition overrunning the budget,
    and rides `Cost.coordination_forced` to `rejected_sound`: **no plan fits, in
    any universe.**
  * `unresolved` carries a `SynthesisObligation` — the best floor we hold (under
    budget, so rejection is off) and the best plan we hold (over budget, so
    acceptance is not in hand) — together with `SynthesisObligation.bracket`,
    which says any plan that closes it has cost in `[knownFloor, budget]`. It
    names its obligation; it is not a shrug.

The asymmetry is not decoration: `lower_bound_does_not_license_acceptance`
**refutes** the licensing claim outright, on the budget workload of `Cost.lean`
§6. A clash decomposition of that workload into one coarse block forces a floor
of 1; the floor fits a budget of 1; and no plan in any universe costs ≤ 1,
because a *finer* decomposition of the same workload forces 3. A lower bound is
one member of a family, you only ever hold one, and no member of the family
licenses acceptance.

## What a `Plan` is here — and what it deliberately is not

`Cost.crossings` is a per-stream, per-seam quantity, so a plan in this model is
exactly a **seam choice with its validity proof**: `SegmentedIConfluent σ wl.I`.
`Plan.cost` is then `crossings`, computed against that seam — not an assumed
parameter, not a bound handed to the checker.

⚠ A plan is **not** allowed to re-block the workload, and that is a soundness
constraint rather than a simplification. `reblocking_escapes_the_floor` proves
why: `Cost.batchStep` runs the *same net behaviour* as the budget workload
(`run` of both is equal, by `rfl`) at a crossing count of 1, while every valid
seam on the unbatched workload pays at least 3. A `Plan` permitted to batch
would therefore "accept" at budget 2 a workload that `rejected` refuses at
budget 2 — the floor of a workload does not bound the cost of a *different*
blocking of it. Batching is a change of workload, and `Workload` is the thing
the verdict is indexed by.

## Non-claims, labelled

  * ⟨UNDONE⟩ **Crossings are not meetings.** Repeated from `Cost.lean` rather
    than inherited from it: a "coordination event" here is a seam crossing on
    one replica's stream. How many peers must attend, and whether two replicas
    crossing "the same" boundary hold one meeting or two, is not modelled. A
    budget in this file is a budget of *crossings*, and calling it a budget of
    meetings would be a category error.
  * ⟨TERMINAL for this file⟩ **The per-stream scope is inherited whole.**
    `Cost.no_seam_frees_both` proves the crossing measure undercounts a
    *concurrent* workload: two streams each free under a seam of their own, no
    single valid seam freeing both. Every `accepted` here is therefore an
    acceptance of **one replica's stream against one seam**, and a concurrent
    session's true cost is not bounded by it. This is not repairable inside this
    file's measure; it is the measure's domain of validity.
  * ⟨UNDONE⟩ **`unavoidableFloor` is not a function.** The floor is a supremum
    over clash decompositions, and nothing here computes it. `ForcedFloor wl n`
    says "`n` is *a* forced floor", witnessed by a decomposition; `rejected`
    carries that witness. Reading a `ForcedFloor` as "the" floor is exactly the
    error `lower_bound_does_not_license_acceptance` punishes.
  * ⟨UNDONE⟩ **Composition is sequential only.** `accepted_andThen` composes two
    accepted stretches *of one stream under one seam*, from `crossings_append`.
    Two **concurrent** accepted sessions under one budget need the profile
    discipline — a sibling lane is proving `opt_compose_ge_sum_opt` in
    `Uwueave/CoordEffect.lean`, and this file deliberately does not import it.
    The connection, in prose: an optimum over seams does not distribute over
    concurrent composition, because the seam is a *global* choice — which is
    precisely what `Cost.no_seam_frees_both` exhibits. So `cost(A ∥ B)` is not
    `cost A + cost B`, and a composed budget check needs a profile that survives
    the min-over-seams, not a sum of per-stream verdicts.
  * ⟨scope⟩ **`RunLegal`, not step-totality.** A `Workload` carries legality of
    the states its own run occupies, not `∀ s o, I s → I (step s o)`. The
    unlinked document below is why: `Cost.docStep`'s version bump does *not*
    preserve `twoFieldInv` from every legal state (that is the tightening
    migration's clash, `Seams.schema_tightening_not_iconfluent`) — it preserves
    it along *this* run, whose store is empty. Demanding the stronger field
    would have excluded the workload the file most needs.
  * ⟨scope⟩ **`[DecidableEq Seg]`**, inherited from `crossings`: a `Plan` carries
    its seam's decidable equality as a field, so "no plan in any universe" means
    no plan whose seam has decidable equality. Not vacuous (`Nat`, `Nat × Nat`
    seams both appear below).
-/
import Uwueave.Cost

namespace Uwueave.Budget

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Seams Uwueave.SeamAlgebra
open Uwueave.Cost

universe u v w

/-! ## §1. Workloads — a run whose occupied states are legal -/

/-- Every state the run of `w` from `s` occupies is legal. Stated along the
recursion of `Cost.run` rather than as `∀ s o, I s → I (step s o)`: the strong
form is false for the unlinked document of §6 (a version bump breaks
`twoFieldInv` from a *non-empty* store — the tightening clash), while the run
this file measures never occupies such a state. -/
def RunLegal {S : Type u} {Op : Type w} (I : Invariant S) (step : S → Op → S) :
    S → List Op → Prop
  | s, [] => I s
  | s, o :: rest => I s ∧ RunLegal I step (step s o) rest

/-- A legal run ends legal. -/
theorem runLegal_run {S : Type u} {Op : Type w} {I : Invariant S} {step : S → Op → S} :
    ∀ (s : S) (w : List Op), RunLegal I step s w → I (run step s w) := by
  intro s w
  induction w generalizing s with
  | nil => exact id
  | cons o rest ih => exact fun h => ih (step s o) h.2

/-- Legality composes along concatenation — the lemma `Workload.andThen` needs. -/
theorem runLegal_append {S : Type u} {Op : Type w} {I : Invariant S} {step : S → Op → S} :
    ∀ (s : S) (w₁ w₂ : List Op), RunLegal I step s w₁ →
      RunLegal I step (run step s w₁) w₂ → RunLegal I step s (w₁ ++ w₂) := by
  intro s w₁
  induction w₁ generalizing s with
  | nil => intro w₂ _ h₂; exact h₂
  | cons o rest ih => intro w₂ h₁ h₂; exact ⟨h₁.1, ih (step s o) w₂ h₁.2 h₂⟩

/-- **The thing a budget is a budget for.** An op stream from a start state
under a local transition, with the invariant it is supposed to maintain and a
proof that the run really does maintain it. The verdict type below is indexed by
one of these, which is what stops a "plan" from quietly re-blocking the workload
(see `reblocking_escapes_the_floor`). -/
structure Workload (S : Type u) (Op : Type w) [MergeState S] where
  /-- The invariant the session must maintain. -/
  I : Invariant S
  /-- The local transition: what one op does on one replica. -/
  step : S → Op → S
  /-- Where the session starts. -/
  start : S
  /-- The op stream. -/
  ops : List Op
  /-- Every state the run occupies is legal — so this is a real execution. -/
  legal : RunLegal I step start ops

/-! ## §2. Plans — a witnessed coordination strategy, and its ACHIEVED cost -/

/-- **A plan.** In this model a coordination strategy *is* a seam: a projection
the replicas hold fixed between coordination events, together with the proof
that holding it fixed is actually safe (`SegmentedIConfluent`, whose second
conjunct is what keeps a sync from teleporting across the boundary).

Nothing in a `Plan` is a cost claim: `Plan.cost` is computed from these fields
by `Cost.crossings`. That is the asymmetry this file exists for — a floor is a
theorem about the specification, an achieved cost is an evaluation of an
exhibited object. -/
structure Plan.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    (wl : Workload S Op) where
  /-- The seam's codomain. -/
  Seg : Type v'
  /-- Crossings branch on whether the seam moved, so the codomain is discrete. -/
  segDecEq : DecidableEq Seg
  /-- The seam itself. -/
  σ : S → Seg
  /-- The seam is valid for this workload's invariant: same-fiber merges
  preserve `I` and stay in the fiber. -/
  valid : SegmentedIConfluent σ wl.I

/-- **The achieved crossing count — computed, not assumed.** The number of ops
along the workload's own run at which the plan's seam changes value. -/
def Plan.cost.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} (P : Plan.{u', v', w'} wl) : Nat :=
  @crossings S P.Seg Op P.segDecEq P.σ wl.step wl.start wl.ops

/-- A plan's promise, discharged: between crossings, replicas in one fiber may
gossip freely and cannot leave the fiber behind each other's backs. -/
theorem Plan.gossipFree.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} (P : Plan.{u', v', w'} wl) {a b : S}
    (hσ : P.σ a = P.σ b) (ha : wl.I a) (hb : wl.I b) :
    wl.I (a ⊔ b) ∧ P.σ (a ⊔ b) = P.σ a :=
  P.valid a b hσ ha hb

/-! ## §3. Forced floors — the only thing a lower bound can be -/

/-- **`n` is a forced floor for this workload**: some decomposition of the
workload's own op stream into `n` clash blocks — each block's endpoints legal,
their merge illegal. By `Cost.coordination_forced` that is a lower bound under
*every* seam in *every* universe.

⚠ This is "`n` is **a** floor", not "`n` is **the** floor". The true floor is a
supremum over decompositions and nothing here computes it; one workload has
`ForcedFloor _ 1` and `ForcedFloor _ 3` at once (§5), which is exactly why a
held lower bound licenses no acceptance. -/
def ForcedFloor.{u', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    (wl : Workload S Op) (n : Nat) : Prop :=
  ∃ bs : List (List Op),
    ClashBlocks wl.I wl.step wl.start bs ∧ bs.flatten = wl.ops ∧ n = bs.length

/-- **The bridge, and the whole load-bearing use of `Cost.coordination_forced`.**
A forced floor bounds *every* plan's achieved cost from below — for every seam
type in every universe, because that is the form the floor was proved in. This
single lemma powers `rejected_sound`, the acceptance/rejection exclusion, and
the bracket that keeps `unresolved` honest. -/
theorem ForcedFloor.le_cost.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} {n : Nat} (h : ForcedFloor wl n) (P : Plan.{u', v', w'} wl) :
    n ≤ P.cost := by
  rcases h with ⟨bs, hcl, hflat, hn⟩
  have hb : bs.length ≤ @crossings S P.Seg Op P.segDecEq P.σ wl.step wl.start bs.flatten :=
    @coordination_forced S Op _ wl.I wl.step wl.start bs hcl P.Seg P.segDecEq P.σ P.valid
  rw [hflat] at hb
  show n ≤ @crossings S P.Seg Op P.segDecEq P.σ wl.step wl.start wl.ops
  omega

/-! ## §4. The verdict — three constructors, each carrying its evidence -/

/-- **What `unresolved` owes.** The evidence actually held when neither decisive
verdict is available: a forced floor that *fits* the budget (so `rejected` is
not constructible from it) and a valid plan that *overruns* it (so `accepted` is
not constructible from it).

What would have to be exhibited to close it is then precisely one of:

  * a `Plan` for this workload with `cost ≤ budget` — feeding
    `BudgetVerdict.accepted`; by `bracket` its cost must lie in
    `[knownFloor, budget]`, so the search interval is named, not open; or
  * an `n` with `ForcedFloor wl n` and `budget < n` — a *finer* clash
    decomposition than `floorForced`'s — feeding `BudgetVerdict.rejected`.

`notBoth` proves those two are mutually exclusive, so discharging the obligation
decides the verdict rather than producing a contradiction. -/
structure SynthesisObligation.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    (wl : Workload S Op) (budget : Nat) where
  /-- The best lower bound we hold. -/
  knownFloor : Nat
  /-- …and it really is forced, by a witnessed clash decomposition. -/
  floorForced : ForcedFloor wl knownFloor
  /-- …and it fits, so no rejection follows from it. -/
  floorFits : knownFloor ≤ budget
  /-- The cheapest plan we hold. -/
  best : Plan.{u', v', w'} wl
  /-- …and it overruns, so no acceptance follows from it. -/
  bestOverBudget : budget < best.cost

/-- **The budget verdict.** Three answers, each carrying the evidence that makes
it mean something. Note what is *absent*: there is no constructor taking
`floor ≤ budget` to an acceptance. -/
inductive BudgetVerdict.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    (wl : Workload S Op) (budget : Nat) where
  /-- **Accepted** — a witnessed plan, proved to fit. `upper` is a proof about a
  *computed* crossing count of an *exhibited* seam; nothing weaker is admitted
  here, which is the file's reason to exist. -/
  | accepted (plan : Plan.{u', v', w'} wl) (upper : plan.cost ≤ budget)
  /-- **Rejected** — a forced floor above the budget, witnessed by the clash
  decomposition that realises it. `rejected_sound` turns this into "no plan
  fits, in any universe", via `Cost.coordination_forced`. -/
  | rejected (n : Nat) (forced : ForcedFloor wl n) (over : budget < n)
  /-- **Unresolved** — the remaining synthesis obligation, with the floor and
  the plan that bracket it. Not a shrug: see `SynthesisObligation`. -/
  | unresolved (obl : SynthesisObligation.{u', v', w'} wl budget)

/-! ## §5. Soundness of both decisive verdicts -/

/-- **`accepted` means a real execution within budget.** Unpacked into the four
things "within budget" has to mean here:

  1. every state the run occupies is legal — it is an execution, not a schema;
  2. the seam it runs against is a real seam, so between crossings replicas may
     gossip and cannot silently leave the fiber;
  3. **no prefix of the run exceeds the budget** — the bound holds throughout,
     not only at the end; and
  4. **however the run is carved into seam-moving blocks, there are at most
     `budget` of them** — so the count is not an artefact of one blocking.

(1) and (2) are the `Workload`/`Plan` construction obligations, which is the
point: they were discharged before a verdict could be built. (3) and (4) are
`Cost.crossings_append` and `Cost.crossings_ge_length` doing work. -/
theorem accepted_sound.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} {budget : Nat} (P : Plan.{u', v', w'} wl)
    (h : P.cost ≤ budget) :
    RunLegal wl.I wl.step wl.start wl.ops
      ∧ (∀ a b : S, P.σ a = P.σ b → wl.I a → wl.I b →
          wl.I (a ⊔ b) ∧ P.σ (a ⊔ b) = P.σ a)
      ∧ (∀ pre suf : List Op, pre ++ suf = wl.ops →
          @crossings S P.Seg Op P.segDecEq P.σ wl.step wl.start pre ≤ budget)
      ∧ (∀ bs : List (List Op), bs.flatten = wl.ops →
          BlockChanges P.σ wl.step wl.start bs → bs.length ≤ budget) := by
  have hb : @crossings S P.Seg Op P.segDecEq P.σ wl.step wl.start wl.ops ≤ budget := h
  refine ⟨wl.legal, fun a b hσ ha hb' => P.gossipFree hσ ha hb', ?_, ?_⟩
  · intro pre suf hsplit
    have hap := @crossings_append S P.Seg Op P.segDecEq P.σ wl.step wl.start pre suf
    rw [hsplit] at hap
    omega
  · intro bs hflat hbc
    have hge := @crossings_ge_length S P.Seg Op P.segDecEq P.σ wl.step wl.start bs hbc
    rw [hflat] at hge
    omega

/-- **The sandwich, and the exclusion.** An accepted plan forces every floor
under the budget: `Floor ≤ Cost(plan) ≤ Budget`. So `accepted` and `rejected`
can never both be available for one workload at one budget — the trichotomy is
consistent, and it is `ForcedFloor.le_cost` that makes it so. -/
theorem accepted_floor_le_budget.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} {budget : Nat} (P : Plan.{u', v', w'} wl)
    (h : P.cost ≤ budget) : ∀ n : Nat, ForcedFloor wl n → n ≤ budget := by
  intro n hf
  have := hf.le_cost P
  omega

/-- **`rejected` means no plan fits — in any universe.** This is where
`Cost.coordination_forced` does its work: the floor was proved for every segment
type in every universe, so the refutation quantifies the same way. The theorem
is universe-polymorphic in the seam universe `v'`, which is the reading that
matters: no cleverness in choosing a seam, at any size, gets under the budget. -/
theorem rejected_sound.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} {budget n : Nat}
    (forced : ForcedFloor wl n) (over : budget < n) :
    ∀ P : Plan.{u', v', w'} wl, ¬ (P.cost ≤ budget) := by
  intro P hle
  have := forced.le_cost P
  omega

/-- Any plan that closes an obligation lands in the named interval: the
obligation bounds its own search space from both sides. This is what makes
`unresolved` a statement of work rather than an absence of one. -/
theorem SynthesisObligation.bracket.{u', v', t', w'} {S : Type u'} {Op : Type w'}
    [MergeState S] {wl : Workload S Op} {budget : Nat}
    (O : SynthesisObligation.{u', v', w'} wl budget) (P : Plan.{u', t', w'} wl)
    (h : P.cost ≤ budget) : O.knownFloor ≤ P.cost ∧ P.cost ≤ budget :=
  ⟨O.floorForced.le_cost P, h⟩

/-- The two ways to close an obligation are mutually exclusive: exhibiting a
plan that fits refutes the existence of a floor that overruns, and vice versa.
So the obligation is a genuine fork, not a pair of claims that could both land. -/
theorem SynthesisObligation.notBoth.{u', t', w'} {S : Type u'} {Op : Type w'}
    [MergeState S] {wl : Workload S Op} {budget : Nat}
    (P : Plan.{u', t', w'} wl) (hfit : P.cost ≤ budget)
    (n : Nat) (forced : ForcedFloor wl n) : ¬ (budget < n) := by
  have := forced.le_cost P
  omega

/-- The obligation's own reading: on the evidence held, neither decisive verdict
is constructible — the floor does not overrun and the plan does not fit. -/
theorem SynthesisObligation.gap.{u', v', w'} {S : Type u'} {Op : Type w'}
    [MergeState S] {wl : Workload S Op} {budget : Nat}
    (O : SynthesisObligation.{u', v', w'} wl budget) :
    ¬ (budget < O.knownFloor) ∧ ¬ (O.best.cost ≤ budget) := by
  have h1 := O.floorFits
  have h2 := O.bestOverBudget
  exact ⟨by omega, by omega⟩

/-! ## §6. The workloads — `Cost.lean` §6/§7/§8, as budget-checkable sessions -/

/-- The budget/re-allocation workload of `Cost.lean` §6: three re-divisions of a
shared budget of 10, from the whole budget on device `true`. Every allocation
along the run sums to 10 with nothing overspent, so the run is legal. -/
def budgetWorkload : Workload QuotaState Nat where
  I := BudgetInv 10
  step := reallocStep 10
  start := budgetStart
  ops := budgetW
  legal := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide)

/-- The same net re-division as **one** op — `Cost.lean` §8's batch. A different
workload, deliberately: see `reblocking_escapes_the_floor`. -/
def batchWorkload : Workload QuotaState Unit where
  I := BudgetInv 10
  step := batchStep
  start := budgetStart
  ops := batchW
  legal := by
    refine ⟨?_, ?_⟩ <;> (refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide)

/-- The unlinked two-field document of `Cost.lean` §7: two version bumps and two
re-allocations as four separate events. The run's store stays empty, which is
why the version bumps are legal here even though `docStep` does not preserve
`twoFieldInv` in general. -/
def unlinkedWorkload : Workload TwoFieldDoc DocOp where
  I := twoFieldInv
  step := docStep
  start := docStart
  ops := unlinkedW
  legal := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide),
             by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide⟩

/-! ### The plans, and their computed costs -/

/-- The allocation-share seam of `Cost.share_segmented`, as a plan for the
budget workload. -/
def budgetSharePlan : Plan budgetWorkload where
  Seg := Nat
  segDecEq := inferInstance
  σ := fun s => s.1 true
  valid := share_segmented 10

/-- Its achieved cost is three — `Cost.budget_cost_is_three`'s second conjunct,
which is a `decide` over the emitted count, cited rather than re-derived. -/
theorem budgetSharePlan_cost : budgetSharePlan.cost = 3 := budget_cost_is_three.{0}.2

/-- The same seam against the batched workload. -/
def batchSharePlan : Plan batchWorkload where
  Seg := Nat
  segDecEq := inferInstance
  σ := fun s => s.1 true
  valid := share_segmented 10

/-- Its achieved cost is one — `Cost.batched_cost_is_one`'s second conjunct. -/
theorem batchSharePlan_cost : batchSharePlan.cost = 1 := batched_cost_is_one.{0}.2

/-- The canonical `(version, share)` pair seam of `Cost.twoFieldShare_segmented`,
as a plan for the unlinked document. -/
def unlinkedPairPlan : Plan unlinkedWorkload where
  Seg := Nat × Nat
  segDecEq := inferInstance
  σ := fun p => (p.1.1, p.2.1 true)
  valid := twoFieldShare_segmented

/-- Its achieved cost is four — `Cost.linked_halves_the_crossings`'s first
conjunct. -/
theorem unlinkedPairPlan_cost : unlinkedPairPlan.cost = 4 :=
  linked_halves_the_crossings.1

/-! ### The forced floors -/

/-- **The sharp floor of the budget workload: three.** `Cost.budget_clashBlocks`
— each of the three re-divisions has legal endpoints whose merge busts the
budget. -/
theorem budget_forced_three : ForcedFloor budgetWorkload 3 :=
  ⟨budgetBlocks, budget_clashBlocks, budgetBlocks_flatten, rfl⟩

/-- **A coarse floor of the same workload: one.** The whole stream as a single
block — its two endpoints (the whole budget on `true`, then the 3/7 split) are
each legal and merge to 10+7, over budget. A perfectly valid lower bound, and a
useless one: §7 turns it into the refutation. -/
theorem budget_forced_one : ForcedFloor budgetWorkload 1 :=
  ⟨[budgetW], ⟨by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide,
               by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide,
               fun h => absurd h.2 (by decide), trivial⟩, rfl, rfl⟩

/-- **The unlinked document's floor: two** — `Cost.unlinked_clashBlocks`, the two
re-allocations. (`Cost.lean` §7 records as ⟨UNDONE⟩ whether it is the true
floor; §8 below is what that open question costs a checker.) -/
theorem unlinked_forced_two : ForcedFloor unlinkedWorkload 2 :=
  ⟨unlinkedBlocks, unlinked_clashBlocks, unlinkedBlocks_flatten, rfl⟩

/-! ## §7. ⚠ `floor ≤ budget` DOES NOT LICENSE ACCEPTANCE — the refutation

The claim a lower-bound-only checker must make in order to accept, and its
refutation on a workload this repo already owns. -/

/-- The licensing claim, stated so it can be refuted: *a forced floor at or
under the budget yields a plan that fits*. Restricted to `Type`-level workloads,
which only strengthens the refutation — the general claim implies this one.
Universe-polymorphic in the seam universe, so the refutation kills the claim at
every seam size at once. -/
def LowerBoundLicensesAcceptance.{v'} : Prop :=
  ∀ {S Op : Type} [MergeState S] (wl : Workload S Op) (n budget : Nat),
    ForcedFloor wl n → n ≤ budget → ∃ P : Plan.{0, v', 0} wl, P.cost ≤ budget

/-- **The theorem that makes the trichotomy honest.** The licensing claim is
false. Witness: the budget workload at budget 1. `budget_forced_one` is a real
forced floor and it fits the budget exactly — so the rejection argument is
genuinely unavailable — yet `budget_forced_three` puts every plan, in every
universe, at cost ≥ 3.

A lower bound is one member of a family of lower bounds; a checker holds one
member; and no member licenses acceptance, because acceptance is a claim about
achievability and a floor is a claim about the specification. `unresolved` is
therefore an occupied verdict rather than a placeholder — §8 occupies it on a
case where the gap is not even closable with what this repo knows. -/
theorem lower_bound_does_not_license_acceptance : ¬ LowerBoundLicensesAcceptance.{v} := by
  intro h
  rcases h budgetWorkload 1 1 budget_forced_one (Nat.le_refl 1) with ⟨P, hP⟩
  have := budget_forced_three.le_cost P
  omega

/-- ⚠ **Why a `Plan` may not re-block the workload.** The batched workload runs
the *same net behaviour* as the budget workload — `run` of the two is equal, by
`rfl` — at an achieved cost of 1, while every plan for the budget workload costs
more than 2. So if `Plan` were allowed to carry a re-blocking, `accepted` would
fire at budget 2 on exactly the workload `rejected` refuses at budget 2, and
`rejected_sound` would be false.

The floor of a workload bounds the plans *for that workload*. Batching is a
change of workload — `Cost.lean` §8's own reading: the intermediate allocations
stop being states anyone occupies — and the verdict type is indexed by the
workload for that reason. -/
theorem reblocking_escapes_the_floor.{v'} :
    run budgetWorkload.step budgetWorkload.start budgetWorkload.ops
        = run batchWorkload.step batchWorkload.start batchWorkload.ops
      ∧ batchSharePlan.cost = 1
      ∧ ∀ P : Plan.{0, v', 0} budgetWorkload, ¬ (P.cost ≤ 2) :=
  ⟨rfl, batchSharePlan_cost, rejected_sound budget_forced_three (by decide)⟩

/-! ## §8. Three verdicts on related inputs — the checker discriminates -/

/-- **REJECTED.** The budget workload at budget 2: three re-divisions are forced
and two is not enough. By `rejected_sound` this is not "we found no plan" — it
is "no plan exists, under any seam in any universe". -/
def budgetRejectedAtTwo : BudgetVerdict.{0, 0, 0} budgetWorkload 2 :=
  .rejected 3 budget_forced_three (by decide)

/-- The rejection's content, spelled out. -/
theorem budgetRejectedAtTwo_sound.{v'} :
    ∀ P : Plan.{0, v', 0} budgetWorkload, ¬ (P.cost ≤ 2) :=
  rejected_sound budget_forced_three (by decide)

/-- **ACCEPTED.** The *same workload* at budget 3, with a witnessed plan: the
allocation-share seam, whose achieved count is computed to be exactly 3. The
upper bound is the constructor's second argument — there is no route to this
value that does not exhibit the plan. -/
def budgetAcceptedAtThree : BudgetVerdict budgetWorkload 3 :=
  .accepted budgetSharePlan (Nat.le_of_eq budgetSharePlan_cost)

/-- **Why `unresolved` cannot be occupied by *this* workload at any budget.**
The budget workload's floor and its achievement meet at 3 (`Cost.lean` §6's
tightness), so every budget is decided: under 3 no plan fits in any universe,
at 3 or above a witnessed plan is in hand. A gap between floor and achievement
is what `unresolved` needs, and the unlinked document below is where this repo
actually has one. -/
theorem budgetWorkload_is_decided.{v'} (b : Nat) :
    (b < 3 → ∀ P : Plan.{0, v', 0} budgetWorkload, ¬ (P.cost ≤ b))
      ∧ (3 ≤ b → budgetSharePlan.cost ≤ b) :=
  ⟨fun hb => rejected_sound budget_forced_three hb,
   fun hb => by rw [budgetSharePlan_cost]; exact hb⟩

/-- **UNRESOLVED.** The unlinked document at budget 3. The floor we hold is 2
(`unlinked_forced_two`), which *fits* — so no rejection follows. The best plan
we hold is the canonical `(version, share)` pair seam, whose achieved count is 4
— so no acceptance follows either.

The obligation is exactly `Cost.lean` §7's own ⟨UNDONE⟩: a seam reading "does
the store hold a record the next version will forbid" plausibly reaches 2 on
this document, and nobody has proved it a valid seam. Exhibit it (cost ≤ 3) and
this becomes `accepted`; exhibit a three-block clash decomposition of
`unlinkedW` and it becomes `rejected`. `bracket` says the first must land in
`[2, 3]`. -/
def unlinkedObligationAtThree : SynthesisObligation unlinkedWorkload 3 where
  knownFloor := 2
  floorForced := unlinked_forced_two
  floorFits := by decide
  best := unlinkedPairPlan
  bestOverBudget := by rw [unlinkedPairPlan_cost]; decide

/-- The unresolved verdict itself. -/
def unlinkedUnresolvedAtThree : BudgetVerdict unlinkedWorkload 3 :=
  .unresolved unlinkedObligationAtThree

/-- **`unresolved` is genuinely occupied here**, and the statement says in what
sense: on the evidence this repo holds, neither decisive verdict is
constructible — and any plan that would close the gap has an achieved cost in
`[2, 3]`, for every seam universe. The obligation names its own search
interval. -/
theorem unlinked_at_three_is_open.{v'} :
    ¬ (3 < unlinkedObligationAtThree.knownFloor)
      ∧ ¬ (unlinkedPairPlan.cost ≤ 3)
      ∧ ∀ P : Plan.{0, v', 0} unlinkedWorkload, P.cost ≤ 3 → 2 ≤ P.cost ∧ P.cost ≤ 3 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [unlinkedPairPlan_cost]; decide
  · intro P h
    exact ⟨unlinked_forced_two.le_cost P, h⟩

/-- **ACCEPTED, on the batched workload at budget 1** — the fourth reading, and
the one that makes §7's re-blocking warning concrete: the same net behaviour
that is *rejected* at budget 2 unbatched is *accepted* at budget 1 batched.
Batching is a real engineering answer to a failed budget check; it is just not
something a `Plan` may do behind the checker's back. -/
def batchAcceptedAtOne : BudgetVerdict batchWorkload 1 :=
  .accepted batchSharePlan (Nat.le_of_eq batchSharePlan_cost)

/-- The end state of the budget session is legal — `RunLegal` read at the end,
on the workload the three verdicts above discriminate. -/
example : BudgetInv 10 (run (reallocStep 10) budgetStart budgetW) :=
  runLegal_run budgetStart budgetW budgetWorkload.legal

/-- ⚠ **The costs are evaluated, not asserted.** Each `Plan.cost` above reduces
to a numeral in the kernel — which is what "achieved" has to mean for an upper
bound to be evidence. (The floors do not reduce: they are theorems over every
seam in every universe. That is the asymmetry, visible in the proof style.) -/
example : (budgetSharePlan.cost, batchSharePlan.cost, unlinkedPairPlan.cost) = (3, 1, 4) := by
  decide

/-! ## §9. Sequential composition — as far as this file honestly reaches

Two accepted stretches **of one stream under one seam** compose at the summed
budget, from `Cost.crossings_append`. That is the whole of what composes here.
Concurrent composition of two accepted *sessions* is a different theorem and a
harder one — see the module docstring's ⟨UNDONE⟩ and the sibling
`Uwueave/CoordEffect.lean`, deliberately not imported. -/

/-- Extend a workload by a further stretch of ops whose run is also legal. -/
def Workload.andThen {S : Type u} {Op : Type w} [MergeState S]
    (wl : Workload S Op) (w₂ : List Op)
    (h₂ : RunLegal wl.I wl.step (run wl.step wl.start wl.ops) w₂) : Workload S Op where
  I := wl.I
  step := wl.step
  start := wl.start
  ops := wl.ops ++ w₂
  legal := runLegal_append wl.start wl.ops w₂ wl.legal h₂

/-- The same seam, now a plan for the extended workload. The seam's validity is
a fact about the invariant, and the extension does not change it. -/
def Plan.andThen.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} (P : Plan.{u', v', w'} wl) (w₂ : List Op)
    (h₂ : RunLegal wl.I wl.step (run wl.step wl.start wl.ops) w₂) :
    Plan.{u', v', w'} (wl.andThen w₂ h₂) where
  Seg := P.Seg
  segDecEq := P.segDecEq
  σ := P.σ
  valid := P.valid

/-- Cost is additive across the join: what the continuation costs is measured
from the state the first stretch left behind. `Cost.crossings_append`, at the
plan level. -/
theorem Plan.cost_andThen.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} (P : Plan.{u', v', w'} wl) (w₂ : List Op)
    (h₂ : RunLegal wl.I wl.step (run wl.step wl.start wl.ops) w₂) :
    (P.andThen w₂ h₂).cost
      = P.cost + @crossings S P.Seg Op P.segDecEq P.σ wl.step
          (run wl.step wl.start wl.ops) w₂ :=
  @crossings_append S P.Seg Op P.segDecEq P.σ wl.step wl.start wl.ops w₂

/-- **Two accepted stretches compose at the summed budget** — under one seam,
sequentially. This is the composition that `crossings`' additivity actually
gives, and it is strictly weaker than the concurrent statement a session
calculus wants. -/
theorem accepted_andThen.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} {b₁ b₂ : Nat} (P : Plan.{u', v', w'} wl) (h₁ : P.cost ≤ b₁)
    (w₂ : List Op) (h₂ : RunLegal wl.I wl.step (run wl.step wl.start wl.ops) w₂)
    (hc : @crossings S P.Seg Op P.segDecEq P.σ wl.step
            (run wl.step wl.start wl.ops) w₂ ≤ b₂) :
    (P.andThen w₂ h₂).cost ≤ b₁ + b₂ := by
  rw [P.cost_andThen w₂ h₂]
  omega

/-- …and the composed verdict, built the only way an acceptance may be built:
out of a plan and a proof. -/
def acceptedSeq.{u', v', w'} {S : Type u'} {Op : Type w'} [MergeState S]
    {wl : Workload S Op} {b₁ b₂ : Nat} (P : Plan.{u', v', w'} wl) (h₁ : P.cost ≤ b₁)
    (w₂ : List Op) (h₂ : RunLegal wl.I wl.step (run wl.step wl.start wl.ops) w₂)
    (hc : @crossings S P.Seg Op P.segDecEq P.σ wl.step
            (run wl.step wl.start wl.ops) w₂ ≤ b₂) :
    BudgetVerdict.{u', v', w'} (wl.andThen w₂ h₂) (b₁ + b₂) :=
  .accepted (P.andThen w₂ h₂) (accepted_andThen P h₁ w₂ h₂ hc)

end Uwueave.Budget
