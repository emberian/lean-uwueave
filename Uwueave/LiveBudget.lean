/-
# Uwueave.LiveBudget — a budget verdict may not say "no plan fits this protocol"
when what it proved is "no plan fits this lattice".

## The work order

`Budget.rejected_sound` is a true theorem: given a `Budget.ForcedFloor wl n` and
`budget < n`, no `Budget.Plan` for `wl` costs `≤ budget`, at every seam type in
every universe. `Bounds.ew_rejected_at_zero_over_unreachable_pair` runs that
theorem on a workload whose accused pair **no cut of the element-wide history
reaches**, and the resulting sentence — *no plan fits* — reads as a statement
about a deployment. It is not one. Codex, third review:

> `Budget.rejected_sound` is internally sound for the abstract workload supplied
> to it. The defect is the user-facing interpretation "no plan fits this deployed
> protocol" when the workload is not live. Split the output:
> **LIVE REJECTION** — no protocol-admissible plan fits this reachable workload.
> **CARRIER-GLOBAL LOWER BOUND** — the abstract lattice model charges this path;
> operational realizability not established.
> **UNRESOLVED** — provide a live-path witness or a reachability-completeness
> theorem.
> A carrier-global result can be promoted to a live result under a named theorem
> `ReachabilityComplete P`. Do NOT keep the present over-approximation as a hard
> compiler rejection with only a caveat — that would make the language capable of
> refusing a correct protocol for a state it proves cannot occur.

Both halves of the machinery already existed and nobody had joined them:
`Budget.lean` has the verdict and the forced floor; `LiveCost.lean` has the
model, the proof-carrying `Path`, the `ClashChain`, `LiveForcedFloor`, and
`Grounds` — the exact hypothesis under which an abstract floor becomes a live
one. This file is the join, at the level of the **verdict**.

## What is here

  * **§0–§1** the plan space. `PathSegmented` is `Segmented.SegmentedIConfluent`
    with the lattice-global quantifier `∀ x y : S` replaced by "over worlds a
    single execution could fork into" — `LiveSegmented.LiveSegmented`'s judgement,
    moved from `Cost.run` to `LiveCost.Path`, and §7 proves the two are **the same
    judgement** (`pathSegmented_iff_liveSegmented`, both directions). A `LivePlan`
    is a seam with that certificate.
  * **§2** the live floor bounds every **live** plan, not merely every
    carrier-global one — `ClashChain.length_le_crossings` re-proved against the
    weaker seam certificate, which is what lets `liveRejected` quantify over the
    **wider** space. §7's `slotLivePlan` proves the widening is not decoration:
    a live plan whose seam is refuted by `SegmentedIConfluent`.
  * **§3** `LiveRealization` — an execution of the model that starts where the
    abstract workload starts and **costs what it costs, under every seam**. This
    is the object a live verdict is about.
  * **§4** `ReachabilityComplete`, and the promotion. `Realization` bundles
    `LiveCost.Grounds` with a start world; `carrierGlobal_promotes` turns a
    `Budget.ForcedFloor` into a `LiveForcedFloor` over a realization, and
    `promote_to_live_rejection` does it at the verdict level.
  * **§5** `LiveBudgetVerdict`, its four soundness theorems, the report shapes in
    codex's words, and `claim_sound` — *whatever the report displays is a
    proposition the verdict proves*.
  * **§6** the two witnesses for the promotion hypothesis, and the headline.
    `totalModel` is reachability-complete for **every** workload, so promotion
    there is free and buys nothing (`LiveCost.totalModel_grounds_everything`, at
    the verdict level); `ewModel` refutes it, and refutes something stronger —
    the element-wide deployment has **no live realization at all**, so no verdict
    for it can be `liveRejected` or `accepted`. `ew_is_carrier_global_not_live`.
  * **§7** the bridge to `LiveSegmented`, and the strictness of the plan space.
  * **§8** the TRANSPORTS row.

## The headline

`Bounds.ewRejectedAtZero` is a `BudgetVerdict.rejected`: *no plan fits, in any
universe*. Here the same deployment lands in `carrierGlobalBound`, and it is not
a matter of labelling — `ew_no_live_realization` proves the `liveRejected` and
`accepted` constructors are **uninhabitable** for it, because their first field
is an execution starting at a state no world of the element-wide model observes.
The over-approximation is not kept behind a caveat; it is a different
constructor, with a different soundness theorem, saying a different thing.

## Non-claims, labelled

  * ⟨TERMINAL for this file⟩ **A model is still a hypothesis.** Everything here
    is relative to the `RunModel` the modeller supplies; nothing checks it is the
    protocol that runs. `LiveCost.lean`'s note, inherited verbatim, and it is why
    `ReachabilityComplete` is a *named* hypothesis rather than a check.
  * ⟨scope⟩ **`accepted` on a live plan is protocol-relative.** A `LivePlan`'s
    certificate is valid for the model it was issued against and dies if the op
    vocabulary grows (`LiveSegmented.lean`'s non-claim, inherited). A
    carrier-global `Strategy` gives a `LivePlan` (`LivePlan.ofStrategy`), so the
    robust acceptance is a special case of this one — but the verdict does not
    record which certificate was used, and a reader who needs the robust reading
    must look at the plan.
  * ⟨scope⟩ **`Realization` is a total grounding plus a start world.** Codex
    writes `ReachabilityComplete P step`; the extra field is forced by
    `RunModel.World` being permitted to be richer than `S`
    (`WorldFuture.delivery_futures_differ`), so "the model can perform `step`"
    does not by itself say *where the session starts*. The partial groundings
    `LiveCost.lean` names as undefined are undefined here too.
  * ⟨SCOPE U-0087⟩ **No completeness for the promotion.** `carrierGlobal_promotes` is
    one direction. Whether a live rejection always transports *back* to a
    carrier-global one is false in general and not stated: a live floor is proved
    against a live seam certificate, and §7's `slotLivePlan` is exactly a seam
    the carrier-global judgement refuses.
  * ⟨SCOPE U-0088⟩ **The abstract cost is a `List Op` cost.** `LiveRealization.
    cost_agrees` pins a live path to the abstract stream's crossing count. Two
    live paths realizing one workload therefore agree in cost, which is what
    `LiveObligation.notBoth` needs — but nothing here says a deployment has only
    one realization, and a model with several is not studied.
  * ⟨SCOPE U-0089⟩ **Crossings are not meetings**, inherited whole from `Cost.lean`.
-/
import Uwueave.LiveCost
import Uwueave.LiveSegmented

namespace Uwueave.LiveBudget

open Uwueave Uwueave.Catalog Uwueave.Segmented
open Uwueave.LiveCost
open Uwueave.CoordEffect (Strategy)

universe u v w z

/-! ## §0. Two facts about `Budget.RunLegal` the sibling files did not need

`Budget.runLegal_append` composes legality; the promotion needs to **split** it,
because a clash decomposition carves the stream and each block becomes a path of
its own. -/

/-- A legal run starts legal. -/
theorem runLegal_head {S : Type u} {Op : Type w} {I : Invariant S}
    {step : S → Op → S} (s : S) (os : List Op)
    (h : Budget.RunLegal I step s os) : I s := by
  cases os with
  | nil => exact h
  | cons o rest => exact h.1

/-- **Legality splits along concatenation** — the converse of
`Budget.runLegal_append`, and the lemma that lets a block decomposition of a
legal stream become a sequence of legal paths. -/
theorem runLegal_split {S : Type u} {Op : Type w} {I : Invariant S}
    {step : S → Op → S} :
    ∀ (s : S) (w₁ w₂ : List Op), Budget.RunLegal I step s (w₁ ++ w₂) →
      Budget.RunLegal I step s w₁
        ∧ Budget.RunLegal I step (Cost.run step s w₁) w₂ := by
  intro s w₁
  induction w₁ generalizing s with
  | nil => intro w₂ h; exact ⟨runLegal_head s w₂ h, h⟩
  | cons o rest ih =>
      intro w₂ h
      have h' : I s ∧ Budget.RunLegal I step (step s o) (rest ++ w₂) := h
      obtain ⟨h1, h2⟩ := ih (step s o) w₂ h'.2
      exact ⟨⟨h'.1, h1⟩, h2⟩

/-! ## §1. The plan space — protocol-relative seams

A `Budget.Plan` carries `SegmentedIConfluent`, which quantifies over **all** legal
states of the lattice. `LiveSegmented.lean` proves what that costs: on a carrier
whose protocol cannot produce one of three states, the least global seam needs
three coordination domains and the least live seam needs two, and the third
domain is charged for a pair no run produces.

So a *live* verdict must be indexed by the *live* plan space, or its rejection is
a rejection of the plans the lattice admits rather than of the plans the protocol
admits. That is the same substitution codex caught on the floor side, one organ
over. -/

/-- **Two worlds one execution could fork into.** `LiveSegmented.CoReachable`,
over `LiveCost.Path` rather than `Cost.run`: some world reaches both, so a replica
pair really can hold the two states at once and be asked to merge them. -/
def PathCoReachable {S : Type u} {Op : Type w} (P : RunModel S Op)
    (x y : P.World) : Prop :=
  ∃ base : P.World, Nonempty (Path P base x) ∧ Nonempty (Path P base y)

/-- An execution's two endpoints are co-reachable — take the first as the base.
This is what a `ClashChain` block hands the seam certificate. -/
theorem pathCoReachable_of_path {S : Type u} {Op : Type w} {P : RunModel S Op}
    {a b : P.World} (p : Path P a b) : PathCoReachable P a b :=
  ⟨a, ⟨Path.nil a⟩, ⟨p⟩⟩

/-- Co-reachability is symmetric. -/
theorem pathCoReachable_symm {S : Type u} {Op : Type w} {P : RunModel S Op}
    {x y : P.World} (h : PathCoReachable P x y) : PathCoReachable P y x := by
  obtain ⟨base, hx, hy⟩ := h
  exact ⟨base, hy, hx⟩

/-- **A protocol-relative seam.** `SegmentedIConfluent` with its lattice-global
quantifier replaced by co-reachability in the model: inside a fiber, merges of
states *one execution could fork into* preserve the invariant and stay in the
fiber. Nothing is asked about pairs no execution produces. -/
def PathSegmented {S : Type u} {Seg : Type v} {Op : Type w} [MergeState S]
    (P : RunModel S Op) (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ x y : P.World, PathCoReachable P x y →
    σ (P.observe x) = σ (P.observe y) → I (P.observe x) → I (P.observe y) →
    I (P.observe x ⊔ P.observe y) ∧ σ (P.observe x ⊔ P.observe y) = σ (P.observe x)

/-- **The carrier-global certificate is stronger** — it answers for every pair,
so in particular for co-reachable ones. One line, and it is the direction that
makes every old plan a live plan. -/
theorem pathSegmented_of_segmented {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] {P : RunModel S Op} {σ : S → Seg} {I : Invariant S}
    (h : SegmentedIConfluent σ I) : PathSegmented P σ I :=
  fun x y _ hσ hx hy => h (P.observe x) (P.observe y) hσ hx hy

/-- **A live plan.** A seam with a certificate valid for *this* model, carrying
its segment type's decidable equality as a field exactly as `Budget.Plan` does —
crossings branch on whether the seam moved. -/
structure LivePlan.{u', v', w', r'} {S : Type u'} {Op : Type w'} [MergeState S]
    (P : RunModel.{u', w', r'} S Op) (I : Invariant S) where
  /-- The seam's codomain. -/
  Seg : Type v'
  /-- Crossings branch on seam equality, so the codomain is discrete. -/
  segDecEq : DecidableEq Seg
  /-- The seam. -/
  seam : S → Seg
  /-- …valid for the executions this model admits. -/
  valid : PathSegmented P seam I

/-- **The achieved cost of an execution under a live plan** — computed, never
assumed: `LiveCost.Path.crossings` at the plan's own seam. -/
def LivePlan.cost {S : Type u} {Op : Type w} [MergeState S] {P : RunModel S Op}
    {I : Invariant S} (Q : LivePlan P I) {a b : P.World} (p : Path P a b) : Nat :=
  @Path.crossings S Q.Seg Op Q.segDecEq P Q.seam a b p

/-- Cost is additive along concatenation, at the plan level. -/
theorem LivePlan.cost_append {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {I : Invariant S} (Q : LivePlan P I) {a b c : P.World}
    (p : Path P a b) (q : Path P b c) :
    Q.cost (p.append q) = Q.cost p + Q.cost q :=
  @Path.crossings_append S Q.Seg Op Q.segDecEq P Q.seam a b c p q

/-- An execution ending in a different fiber than it started in pays at least
one crossing. -/
theorem LivePlan.one_le_cost_of_ne {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {I : Invariant S} (Q : LivePlan P I) {a b : P.World}
    (p : Path P a b) (h : Q.seam (P.observe b) ≠ Q.seam (P.observe a)) :
    1 ≤ Q.cost p :=
  @Path.one_le_crossings_of_sigma_ne S Q.Seg Op Q.segDecEq P Q.seam a b p h

/-- **Every carrier-global strategy is a live plan.** `CoordEffect.Strategy` —
what `LiveCost.live_rejected_sound` quantifies over — embeds, so a rejection
proved over live plans is a fortiori a rejection over strategies. -/
def LivePlan.ofStrategy.{u', v', w', r'} {S : Type u'} {Seg : Type v'} {Op : Type w'}
    [MergeState S] [inst : DecidableEq Seg] (P : RunModel.{u', w', r'} S Op)
    {I : Invariant S} (τ : Strategy I Seg) : LivePlan.{u', v', w', r'} P I where
  Seg := Seg
  segDecEq := inst
  seam := τ.seam
  valid := pathSegmented_of_segmented τ.valid

/-- **Every `Budget.Plan` is a live plan of every model** — the same embedding,
from the object the old verdict was indexed by. The seam and its decidable
equality are carried across unchanged, so the two costs are the same number. -/
def LivePlan.ofBudgetPlan.{u', v', w', r'} {S : Type u'} {Op : Type w'} [MergeState S]
    {awl : Budget.Workload S Op} (P : RunModel.{u', w', r'} S Op)
    (Q : Budget.Plan.{u', v', w'} awl) : LivePlan.{u', v', w', r'} P awl.I where
  Seg := Q.Seg
  segDecEq := Q.segDecEq
  seam := Q.σ
  valid := pathSegmented_of_segmented Q.valid

/-! ## §2. The live floor, over the wider plan space

`LiveCost.ClashChain.length_le_crossings` bounds every `SegmentedIConfluent`
seam. The same induction goes through against the *weaker* certificate, because
a block's accused pair is joined by the block's own path and is therefore
co-reachable — which is precisely the field `Cost.ClashBlocks` did not have. -/

/-- **THE LIVE LOWER BOUND, against a protocol-relative seam.** A carving into
`n` clash blocks costs at least `n` crossings under every *live* plan — a strictly
larger class of seams than `LiveCost.ClashChain.length_le_crossings` covers, so a
refusal built on it refuses more. -/
theorem clashChain_length_le_liveCost {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {I : Invariant S} (Q : LivePlan P I) :
    ∀ {a b : P.World} (ch : ClashChain I a b), ch.length ≤ Q.cost ch.flatten := by
  intro a b ch
  induction ch with
  | done a => exact Nat.zero_le _
  | block a b blk ha hb hclash rest ih =>
      have hne : Q.seam (P.observe b) ≠ Q.seam (P.observe a) := fun he =>
        hclash (Q.valid a b (pathCoReachable_of_path blk) he.symm ha hb).1
      have h1 := Q.one_le_cost_of_ne blk hne
      have happ := Q.cost_append blk rest.flatten
      show rest.length + 1 ≤ Q.cost (blk.append rest.flatten)
      omega

/-- A live forced floor bounds every live plan's achieved cost from below, at
every segment type in every universe. `LiveCost.LiveForcedFloor.le_cost` with the
seam certificate weakened. -/
theorem liveFloor_le_liveCost {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {wl : LiveWorkload P} {n : Nat}
    (h : LiveForcedFloor wl n) (Q : LivePlan P wl.I) : n ≤ Q.cost wl.path := by
  obtain ⟨ch, hflat, hn⟩ := h
  have hb := clashChain_length_le_liveCost Q ch
  rw [hflat] at hb
  omega

/-! ## §3. What a live verdict is about — a realization of the workload

A live rejection that named some unrelated execution would be worthless. A
`LiveRealization` is an execution of the model that **starts where the abstract
workload starts** and **costs what the abstract workload costs, under every
seam** — so the two are the same session priced two ways, and a statement about
one is a statement about the other. -/

/-- **The abstract workload, realized by the model.** Three obligations, and each
one is load-bearing: the path makes every occupied state a state the model's own
`Step` produced; `observes_start` pins the session to the workload's start;
`cost_agrees` pins the price. `LiveObligation.notBoth` is where the third earns
its keep. -/
structure LiveRealization.{u', v', w', r'} {S : Type u'} {Op : Type w'} [MergeState S]
    (P : RunModel.{u', w', r'} S Op) (awl : Budget.Workload S Op) where
  /-- The world the session starts at. -/
  start : P.World
  /-- …and where it ends. -/
  stop : P.World
  /-- The execution — proof-carrying, step by step. -/
  path : Path P start stop
  /-- Every world it occupies is legal for the workload's invariant. -/
  legal : path.Legal awl.I
  /-- It starts where the workload starts. -/
  observes_start : P.observe start = awl.start
  /-- …and it costs what the workload costs, under every seam in every universe.
  This is what makes a claim about the execution a claim about the session. -/
  cost_agrees : ∀ {Seg : Type v'} [inst : DecidableEq Seg] (σ : S → Seg),
    @Path.crossings S Seg Op inst P σ start stop path
      = @Cost.crossings S Seg Op inst σ awl.step awl.start awl.ops

/-- A realization is a `LiveCost.LiveWorkload` at the workload's own invariant —
so `LiveForcedFloor`, `live_rejected_sound` and the profile machinery apply to it
unchanged. -/
def LiveRealization.toLiveWorkload {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} (R : LiveRealization P awl) :
    LiveWorkload P where
  I := awl.I
  start := R.start
  stop := R.stop
  path := R.path
  legal := R.legal

/-- The achieved cost of the realized session under a live plan. The plan's
segment universe is the realization's own, which is what makes `cost_agrees`
applicable to it — a realization prices exactly the plans it can answer for. -/
def LiveRealization.cost.{u', v', w', r'} {S : Type u'} {Op : Type w'} [MergeState S]
    {P : RunModel.{u', w', r'} S Op} {awl : Budget.Workload S Op}
    (R : LiveRealization.{u', v', w', r'} P awl)
    (Q : LivePlan.{u', v', w', r'} P awl.I) : Nat :=
  Q.cost R.path

/-- **A realized session costs exactly what the abstract stream costs.** The
`cost_agrees` field, read at a live plan's own seam and decidable equality. -/
theorem LiveRealization.cost_eq_abstract.{u', v', w', r'} {S : Type u'} {Op : Type w'}
    [MergeState S] {P : RunModel.{u', w', r'} S Op} {awl : Budget.Workload S Op}
    (R : LiveRealization.{u', v', w', r'} P awl)
    (Q : LivePlan.{u', v', w', r'} P awl.I) :
    R.cost Q
      = @Cost.crossings S Q.Seg Op Q.segDecEq Q.seam awl.step awl.start awl.ops :=
  R.cost_agrees (Seg := Q.Seg) (inst := Q.segDecEq) Q.seam

/-- **Two realizations of one workload cost the same** — under every live plan.
The sense in which "the" live cost of a session is well defined even though the
execution that realizes it is not unique. -/
theorem LiveRealization.cost_indep.{u', v', w', r'} {S : Type u'} {Op : Type w'}
    [MergeState S] {P : RunModel.{u', w', r'} S Op} {awl : Budget.Workload S Op}
    (R R' : LiveRealization.{u', v', w', r'} P awl)
    (Q : LivePlan.{u', v', w', r'} P awl.I) : R.cost Q = R'.cost Q := by
  rw [R.cost_eq_abstract Q, R'.cost_eq_abstract Q]

/-! ## §4. `ReachabilityComplete`, and the promotion

Codex's promotion hypothesis, named. `LiveCost.Grounds P step` says the model can
perform the abstract transition at *every* world, observing exactly what it
computes — "every abstract transition the workload charges is realized by `P`".
A start world is the one extra field, forced by `World` being permitted to be
richer than the state (`WorldFuture.delivery_futures_differ`). -/

/-- **The promotion's hypothesis, as data.** A total grounding of the workload's
transition, plus the world the session starts at. -/
structure Realization {S : Type u} {Op : Type w} [MergeState S]
    (P : RunModel S Op) (awl : Budget.Workload S Op) where
  /-- The model performs the workload's transition at every world. -/
  grounds : Grounds P awl.step
  /-- The world the session starts at. -/
  startW : P.World
  /-- …and it observes the workload's start state. -/
  observes_start : P.observe startW = awl.start

/-- **`ReachabilityComplete P awl`** — codex's named theorem, the hypothesis under
which a carrier-global result may be promoted to a live one. Every transition the
abstract workload charges is realized by `P`, at a start world of the model. -/
def ReachabilityComplete {S : Type u} {Op : Type w} [MergeState S]
    (P : RunModel S Op) (awl : Budget.Workload S Op) : Prop :=
  Nonempty (Realization P awl)

/-- Reachability-completeness is `LiveCost.Groundable` plus a start world — so the
refutations `LiveCost.lean` already owns are refutations of it. -/
theorem groundable_of_reachabilityComplete {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op}
    (h : ReachabilityComplete P awl) : Groundable P awl.step := by
  obtain ⟨R⟩ := h
  exact ⟨R.grounds⟩

/-- **The carving of a legal stream is a legal execution.** Every world the
transported `ClashChain` occupies is legal, because every state the stream
occupies was — `Grounds.path_legal` block by block, glued by
`Path.legal_append` and split by `runLegal_split`. -/
theorem chain_flatten_legal {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {step : S → Op → S} (G : Grounds P step) (I : Invariant S) :
    ∀ (a : P.World) (bs : List (List Op))
      (h : Cost.ClashBlocks I step (P.observe a) bs),
      Budget.RunLegal I step (P.observe a) bs.flatten →
      ((G.chain I a bs h).flatten).Legal I := by
  intro a bs
  induction bs generalizing a with
  | nil => intro _ hleg; exact hleg
  | cons b bs ih =>
      intro h hleg
      have hb : Cost.ClashBlocks I step (P.observe (G.runW a b)) bs := by
        rw [G.observe_runW]; exact h.2.2.2
      have hsplit := runLegal_split (P.observe a) b bs.flatten hleg
      show ((G.path a b).append ((G.chain I (G.runW a b) bs hb).flatten)).Legal I
      refine (Path.legal_append (I := I) (G.path a b) _).mpr ⟨?_, ?_⟩
      · exact (G.path_legal I a b).mpr hsplit.1
      · refine ih (G.runW a b) hb ?_
        rw [G.observe_runW]
        exact hsplit.2

/-- The clash carving of the abstract decomposition, as an execution of the
model — `LiveCost.Grounds.chain`, started at the realization's own world. -/
def Realization.chainOf {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} (R : Realization P awl)
    (bs : List (List Op))
    (hcl : Cost.ClashBlocks awl.I awl.step awl.start bs) :
    ClashChain awl.I R.startW (R.grounds.runBlocks R.startW bs) :=
  R.grounds.chain awl.I R.startW bs (by rw [R.observes_start]; exact hcl)

/-- **The promotion, as data.** A clash decomposition of the abstract workload,
carried across the grounding into an execution of the model that realizes the
workload: legal throughout, starting where the workload starts, costing what it
costs. -/
def Realization.liveOfBlocks {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} (R : Realization P awl)
    (bs : List (List Op)) (hcl : Cost.ClashBlocks awl.I awl.step awl.start bs)
    (hflat : bs.flatten = awl.ops) : LiveRealization P awl where
  start := R.startW
  stop := R.grounds.runBlocks R.startW bs
  path := (R.chainOf bs hcl).flatten
  legal :=
    chain_flatten_legal R.grounds awl.I R.startW bs
      (by rw [R.observes_start]; exact hcl)
      (by rw [R.observes_start, hflat]; exact awl.legal)
  observes_start := R.observes_start
  cost_agrees := by
    intro Seg inst σ
    letI : DecidableEq Seg := inst
    have h := R.grounds.chain_crossings (Seg := Seg) awl.I σ R.startW bs
      (by rw [R.observes_start]; exact hcl)
    rw [← hflat, ← R.observes_start]
    exact h

/-- …and it carries the floor it was carved from, block for block. -/
theorem Realization.liveOfBlocks_forced {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} (R : Realization P awl)
    (bs : List (List Op)) (hcl : Cost.ClashBlocks awl.I awl.step awl.start bs)
    (hflat : bs.flatten = awl.ops) (n : Nat) (hn : n = bs.length) :
    LiveForcedFloor (R.liveOfBlocks bs hcl hflat).toLiveWorkload n :=
  ⟨R.chainOf bs hcl, rfl, by
    rw [hn]
    exact (R.grounds.chain_length awl.I R.startW bs _).symm⟩

/-- ⚠ **THE PROMOTION.** Under `ReachabilityComplete`, a carrier-global forced
floor **is** a live forced floor: some execution of the model realizes the
workload and is carved into the same number of coordination points.

This is the theorem codex asked for, and its shape is the whole point — the
promotion is not a relabelling, it produces the object the live verdict is
indexed by, and without the hypothesis that object need not exist at all
(§6's `ew_no_live_realization`). -/
theorem carrierGlobal_promotes {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {n : Nat}
    (hrc : ReachabilityComplete P awl) (floor : Budget.ForcedFloor awl n) :
    ∃ R : LiveRealization P awl, LiveForcedFloor R.toLiveWorkload n := by
  obtain ⟨R⟩ := hrc
  obtain ⟨bs, hcl, hflat, hn⟩ := floor
  exact ⟨R.liveOfBlocks bs hcl hflat, R.liveOfBlocks_forced bs hcl hflat n hn⟩

/-! ## §5. The verdict — four constructors, each with its own soundness theorem -/

/-- **What `unresolved` owes.** The evidence held when the carrier-global floor
does *not* overrun the budget: no rejection of either kind follows from it, and
no plan is in hand. Codex's two named closers, which
`LiveObligation.closedByReachability` and `LiveObligation.closedByLiveWitness`
discharge and `LiveObligation.notBoth` proves exclusive:

  * a **live-path witness** — a `LiveRealization` and a `LivePlan` fitting the
    budget, feeding `accepted`; or
  * a **reachability-completeness theorem** plus a finer clash decomposition
    overrunning the budget, feeding `liveRejected` through
    `carrierGlobal_promotes`. -/
structure LiveObligation {S : Type u} {Op : Type w} [MergeState S]
    (P : RunModel S Op) (awl : Budget.Workload S Op) (budget : Nat) where
  /-- The best carrier-global lower bound held. -/
  knownFloor : Nat
  /-- …and it really is forced, by a witnessed clash decomposition. -/
  floorForced : Budget.ForcedFloor awl knownFloor
  /-- …and it fits, so no rejection of either kind follows from it. -/
  floorFits : knownFloor ≤ budget

/-- **The live budget verdict.** Codex's split, as four constructors that cannot
be confused, because each carries different evidence:

  * `liveRejected` — a realization of the workload and a clash carving of *its
    own execution* overrunning the budget. No protocol-admissible plan fits.
  * `carrierGlobalBound` — a `Budget.ForcedFloor` overrunning the budget, and
    **nothing about the model**. The lattice charges the path; realizability is
    not established. This is the constructor `Bounds.ewRejectedAtZero` should
    have been.
  * `accepted` — a realization and a live plan whose *computed* crossing count
    fits. As in `Budget.lean`, there is no route to acceptance that does not
    exhibit a plan.
  * `unresolved` — the obligation above, with codex's two closers named. -/
inductive LiveBudgetVerdict.{u', v', w', r'} {S : Type u'} {Op : Type w'} [MergeState S]
    (P : RunModel.{u', w', r'} S Op) (awl : Budget.Workload S Op) (budget : Nat) where
  /-- **LIVE REJECTION.** -/
  | liveRejected (R : LiveRealization.{u', v', w', r'} P awl) (n : Nat)
      (forced : LiveForcedFloor R.toLiveWorkload n) (over : budget < n)
  /-- **CARRIER-GLOBAL LOWER BOUND** — no field mentions the model. -/
  | carrierGlobalBound (n : Nat) (forced : Budget.ForcedFloor awl n)
      (over : budget < n)
  /-- **ACCEPTED** — a witnessed live plan over a realization of the workload. -/
  | accepted (R : LiveRealization.{u', v', w', r'} P awl)
      (Q : LivePlan.{u', v', w', r'} P awl.I) (upper : R.cost Q ≤ budget)
  /-- **UNRESOLVED** — the named obligation. -/
  | unresolved (obl : LiveObligation P awl budget)

/-- The verdict is a live rejection. -/
def IsLiveRejection {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget : Nat} :
    LiveBudgetVerdict P awl budget → Prop
  | .liveRejected .. => True
  | _ => False

/-- The verdict is a carrier-global bound. -/
def IsCarrierGlobal {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget : Nat} :
    LiveBudgetVerdict P awl budget → Prop
  | .carrierGlobalBound .. => True
  | _ => False

/-- The verdict is an acceptance. -/
def IsAccepted {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget : Nat} :
    LiveBudgetVerdict P awl budget → Prop
  | .accepted .. => True
  | _ => False

/-! ### Soundness, constructor by constructor -/

/-- **`liveRejected` means no protocol-admissible plan fits.** The refusal
quantifies over **live** plans — every seam certified against the model, a class
containing every carrier-global seam (`LivePlan.ofStrategy`,
`LivePlan.ofBudgetPlan`) and, on some deployments, strictly more (§7) — at every
segment type in every universe. The pair it refuses over is one the model's own `Step` produced,
because a `ClashChain` block cannot be written without its path. -/
theorem liveRejected_sound.{u', v', w', r'} {S : Type u'} {Op : Type w'} [MergeState S]
    {P : RunModel.{u', w', r'} S Op} {awl : Budget.Workload S Op} {budget n : Nat}
    {R : LiveRealization.{u', v', w', r'} P awl}
    (forced : LiveForcedFloor R.toLiveWorkload n) (over : budget < n) :
    ∀ Q : LivePlan.{u', v', w', r'} P awl.I, ¬ (R.cost Q ≤ budget) := by
  intro Q hle
  have h1 : n ≤ R.cost Q := liveFloor_le_liveCost forced Q
  omega

/-- …and therefore over `CoordEffect.Strategy` too — the class
`LiveCost.live_rejected_sound` quantifies over, recovered as a corollary of the
wider statement. -/
theorem liveRejected_sound_strategy.{u', v', w', r'} {S : Type u'} {Seg : Type v'}
    {Op : Type w'} [MergeState S] [DecidableEq Seg] {P : RunModel.{u', w', r'} S Op}
    {awl : Budget.Workload S Op} {budget n : Nat}
    {R : LiveRealization.{u', v', w', r'} P awl}
    (forced : LiveForcedFloor R.toLiveWorkload n) (over : budget < n) :
    ∀ τ : Strategy awl.I Seg, ¬ (R.toLiveWorkload.cost τ ≤ budget) := by
  intro τ hle
  refine liveRejected_sound forced over (LivePlan.ofStrategy P τ) ?_
  exact hle

/-- **A live rejection is also a carrier-global one.** The realization costs what
the abstract stream costs, so every `Budget.Plan` overruns as well — the live
verdict is strictly more informative than the one it replaces, not a different
axis. -/
theorem liveRejected_refuses_budget_plans.{u', v', w', r'} {S : Type u'} {Op : Type w'}
    [MergeState S] {P : RunModel.{u', w', r'} S Op} {awl : Budget.Workload S Op}
    {budget n : Nat} {R : LiveRealization.{u', v', w', r'} P awl}
    (forced : LiveForcedFloor R.toLiveWorkload n) (over : budget < n) :
    ∀ Q : Budget.Plan.{u', v', w'} awl, ¬ (Q.cost ≤ budget) := by
  intro Q hle
  have hlive := liveRejected_sound forced over (LivePlan.ofBudgetPlan P Q)
  have heq := R.cost_eq_abstract (LivePlan.ofBudgetPlan P Q)
  exact hlive (by rw [heq]; exact hle)

/-- **`accepted` means a real execution of the model, within budget.** Unpacked
into the five things acceptance has to mean here:

  1. every world the execution occupies is legal — it is an execution of the
     model, not a schema;
  2. the seam is valid for the executions this model admits, so between crossings
     replicas that one execution could fork into may gossip and cannot silently
     leave the fiber;
  3. the achieved count fits the budget;
  4. **no prefix of the execution exceeds the budget** — the bound holds
     throughout, not only at the end; and
  5. the count is the abstract workload's count, so this is an acceptance of the
     session the checker was asked about. -/
theorem accepted_sound {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget : Nat}
    (R : LiveRealization P awl) (Q : LivePlan P awl.I) (upper : R.cost Q ≤ budget) :
    R.path.Legal awl.I
      ∧ (∀ x y : P.World, PathCoReachable P x y →
          Q.seam (P.observe x) = Q.seam (P.observe y) → awl.I (P.observe x) →
          awl.I (P.observe y) →
          awl.I (P.observe x ⊔ P.observe y)
            ∧ Q.seam (P.observe x ⊔ P.observe y) = Q.seam (P.observe x))
      ∧ R.cost Q ≤ budget
      ∧ (∀ (c : P.World) (p : Path P R.start c) (q : Path P c R.stop),
          p.append q = R.path → Q.cost p ≤ budget)
      ∧ R.cost Q
          = @Cost.crossings S Q.Seg Op Q.segDecEq Q.seam awl.step awl.start awl.ops := by
  refine ⟨R.legal, Q.valid, upper, ?_, R.cost_eq_abstract Q⟩
  intro c p q hsplit
  have happ : Q.cost p + Q.cost q = R.cost Q := by
    rw [← Q.cost_append p q, hsplit]
    rfl
  omega

/-- **The sandwich.** An accepted live plan puts every live floor under the
budget, so `accepted` and `liveRejected` can never both be available for one
deployment at one budget. -/
theorem accepted_live_floor_le_budget {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget : Nat}
    (R : LiveRealization P awl) (Q : LivePlan P awl.I) (upper : R.cost Q ≤ budget) :
    ∀ n : Nat, LiveForcedFloor R.toLiveWorkload n → n ≤ budget := by
  intro n hf
  have h1 : n ≤ R.cost Q := liveFloor_le_liveCost hf Q
  omega

/-- **`carrierGlobalBound` means what `Budget.rejected_sound` proved, and no
more:** no plan admitted by the *lattice* fits, at every seam type in every
universe. It says nothing about any protocol, and
`carrier_global_rejection_is_not_live` proves the missing sentence cannot be
added by argument. -/
theorem carrierGlobalBound_sound {S : Type u} {Op : Type w} [MergeState S]
    {awl : Budget.Workload S Op} {budget n : Nat}
    (forced : Budget.ForcedFloor awl n) (over : budget < n) :
    ∀ Q : Budget.Plan.{u, v, w} awl, ¬ (Q.cost ≤ budget) :=
  Budget.rejected_sound forced over

/-- The obligation's own reading: on the evidence held, the carrier-global floor
does not overrun, so neither rejection is constructible from it. -/
theorem LiveObligation.noRejection {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget : Nat}
    (O : LiveObligation P awl budget) : ¬ (budget < O.knownFloor) := by
  have := O.floorFits
  omega

/-- **Closer one — the reachability-completeness theorem.** With it, and a clash
decomposition finer than the one held, the obligation becomes a live rejection.
This is `carrierGlobal_promotes` at the verdict level. -/
theorem LiveObligation.closedByReachability {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget n : Nat}
    (_O : LiveObligation P awl budget) (hrc : ReachabilityComplete P awl)
    (forced : Budget.ForcedFloor awl n) (over : budget < n) :
    ∃ v : LiveBudgetVerdict P awl budget, IsLiveRejection v := by
  obtain ⟨R, hf⟩ := carrierGlobal_promotes hrc forced
  exact ⟨.liveRejected R n hf over, trivial⟩

/-- **Closer two — the live-path witness.** A realization and a live plan that
fits turn the obligation into an acceptance. -/
theorem LiveObligation.closedByLiveWitness.{u', v', w', r'} {S : Type u'} {Op : Type w'}
    [MergeState S] {P : RunModel.{u', w', r'} S Op} {awl : Budget.Workload S Op}
    {budget : Nat} (_O : LiveObligation P awl budget)
    (R : LiveRealization.{u', v', w', r'} P awl)
    (Q : LivePlan.{u', v', w', r'} P awl.I) (upper : R.cost Q ≤ budget) :
    ∃ v : LiveBudgetVerdict.{u', v', w', r'} P awl budget, IsAccepted v :=
  ⟨.accepted R Q upper, trivial⟩

/-- **The two closers are mutually exclusive**, so discharging the obligation
decides the verdict rather than producing a contradiction. The proof is where
`LiveRealization.cost_agrees` earns its keep: the promoted realization and the
witnessed one need not be the same execution, and they do not have to be — they
cost the same under every plan. -/
theorem LiveObligation.notBoth.{u', v', w', r'} {S : Type u'} {Op : Type w'}
    [MergeState S] {P : RunModel.{u', w', r'} S Op} {awl : Budget.Workload S Op}
    {budget n : Nat} (hrc : ReachabilityComplete P awl)
    (forced : Budget.ForcedFloor awl n) (over : budget < n)
    (R : LiveRealization.{u', v', w', r'} P awl)
    (Q : LivePlan.{u', v', w', r'} P awl.I) : ¬ (R.cost Q ≤ budget) := by
  intro hle
  obtain ⟨R', hf⟩ := carrierGlobal_promotes hrc forced
  have hbound := liveRejected_sound hf over Q
  have heq := R.cost_indep R' Q
  exact hbound (by rw [← heq]; exact hle)

/-! ### The report — codex's shapes, and the claim each one makes -/

/-- **The user-facing report.** Four shapes, carrying the numbers the operator
needs: the budget, and the floor or the achieved count. -/
inductive Report where
  /-- No protocol-admissible plan fits this reachable workload. -/
  | liveRejection (budget floor : Nat)
  /-- The abstract lattice model charges this path. -/
  | carrierGlobalBound (budget floor : Nat)
  /-- A protocol-admissible plan fits, at the exhibited count. -/
  | accepted (budget cost : Nat)
  /-- Neither, and the obligation is named. -/
  | unresolved (budget knownFloor : Nat)
  deriving Repr, DecidableEq

/-- **The renderer — total over the verdict.** Every constructor has a shape;
there is no fall-through and no `Option`. -/
def report {S : Type u} {Op : Type w} [MergeState S] {P : RunModel S Op}
    {awl : Budget.Workload S Op} {budget : Nat} :
    LiveBudgetVerdict P awl budget → Report
  | .liveRejected _ n _ _ => .liveRejection budget n
  | .carrierGlobalBound n _ _ => .carrierGlobalBound budget n
  | .accepted R Q _ => .accepted budget (R.cost Q)
  | .unresolved O => .unresolved budget O.knownFloor

/-- **The headline, in codex's words.** The carrier-global line is the one this
file exists for: it says what was proved (the lattice model charges this path)
and what was not (operational realizability). -/
def Report.headline : Report → String
  | .liveRejection .. =>
      "LIVE REJECTION — no protocol-admissible plan fits this reachable workload."
  | .carrierGlobalBound .. =>
      "CARRIER-GLOBAL LOWER BOUND — the abstract lattice model charges this path; \
operational realizability not established."
  | .accepted .. =>
      "ACCEPTED — a protocol-admissible plan fits this reachable workload, at the \
exhibited crossing count."
  | .unresolved .. =>
      "UNRESOLVED — provide a live-path witness or a reachability-completeness theorem."

/-- **The proposition each report shape asserts.** Not prose: the claim the
headline makes, as a `Prop`, so that `claim_sound` can prove it. Read the second
line especially — a carrier-global report claims something about
`Budget.Plan`s, which are the plans the *lattice* admits, and claims nothing
about any model. -/
def LiveBudgetVerdict.claim {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {awl : Budget.Workload S Op} {budget : Nat} :
    LiveBudgetVerdict P awl budget → Prop
  | .liveRejected R _ _ _ => ∀ Q : LivePlan P awl.I, ¬ (R.cost Q ≤ budget)
  | .carrierGlobalBound _ _ _ => ∀ Q : Budget.Plan.{u, v, w} awl, ¬ (Q.cost ≤ budget)
  | .accepted R Q _ =>
      R.path.Legal awl.I ∧ R.cost Q ≤ budget
        ∧ R.cost Q
            = @Cost.crossings S Q.Seg Op Q.segDecEq Q.seam awl.step awl.start awl.ops
  | .unresolved O => ¬ (budget < O.knownFloor)

/-- ⚠ **Whatever the report displays is a proposition the verdict proves.** Total
over the verdict, so there is no shape whose headline outruns its evidence — and
in particular the carrier-global headline is *not* discharged by a live theorem,
because its claim does not mention the model. -/
theorem claim_sound {S : Type u} {Op : Type w} [MergeState S] {P : RunModel S Op}
    {awl : Budget.Workload S Op} {budget : Nat}
    (v : LiveBudgetVerdict.{u, v, w} P awl budget) : v.claim := by
  cases v with
  | liveRejected R n forced over => exact liveRejected_sound forced over
  | carrierGlobalBound n forced over => exact carrierGlobalBound_sound forced over
  | accepted R Q upper => exact ⟨R.legal, upper, R.cost_eq_abstract Q⟩
  | unresolved O => exact O.noRejection

/-! ## §6. The two witnesses for the promotion hypothesis, and the headline -/

/-! ### `totalModel` — trivially complete, and therefore worth nothing

`LiveCost.totalModel_grounds_everything` says the total-state model grounds every
transition whatsoever. At the verdict level that reads: every abstract workload
is reachability-complete for its own total-state model, so the promotion is free
there — and a promotion that is free carries no information. The hypothesis has
teeth only against a model that refuses transitions. -/

/-- The total-state model realizes every workload: worlds are states, so the
start world *is* the start state. -/
def totalRealization {S : Type u} {Op : Type w} [MergeState S]
    (awl : Budget.Workload S Op) : Realization (totalModel awl.step) awl where
  grounds := totalGrounds awl.step
  startW := awl.start
  observes_start := rfl

/-- ⚠ **Promotion into the total-state model is free — and buys nothing.** Every
workload is reachability-complete for it, including
`Bounds.ewWorkload`, whose accused pair no history reaches. The verdict-level
reading of `LiveCost.totalModel_grounds_everything`: choosing this model is
choosing to believe every step, and the live verdict then says exactly what the
carrier-global one said. -/
theorem totalModel_reachability_complete {S : Type u} {Op : Type w} [MergeState S]
    (awl : Budget.Workload S Op) : ReachabilityComplete (totalModel awl.step) awl :=
  ⟨totalRealization awl⟩

/-- `Cost.lean` §6's budget workload, realized in the total-state model by the
carving `Cost.budget_clashBlocks`. -/
def budgetLiveRealization :
    LiveRealization (totalModel Budget.budgetWorkload.step) Budget.budgetWorkload :=
  (totalRealization Budget.budgetWorkload).liveOfBlocks Cost.budgetBlocks
    Cost.budget_clashBlocks Cost.budgetBlocks_flatten

/-- …carved into three coordination points. -/
theorem budgetLiveRealization_forced_three :
    LiveForcedFloor budgetLiveRealization.toLiveWorkload 3 :=
  (totalRealization Budget.budgetWorkload).liveOfBlocks_forced Cost.budgetBlocks
    Cost.budget_clashBlocks Cost.budgetBlocks_flatten 3 rfl

/-- **A LIVE REJECTION.** The budget workload at budget 2, promoted: three
re-divisions of a shared budget are forced along an execution the model performs,
and no live plan fits — a class containing every `Budget.Plan`
(`LivePlan.ofBudgetPlan`), and on some deployments strictly more (§7; not
measured for *this* model). -/
def budgetLiveRejectedAtTwo :
    LiveBudgetVerdict (totalModel Budget.budgetWorkload.step) Budget.budgetWorkload 2 :=
  .liveRejected budgetLiveRealization 3 budgetLiveRealization_forced_three (by decide)

/-- Its report — the live headline, with the floor that produced it. -/
theorem budgetLiveRejectedAtTwo_report :
    report budgetLiveRejectedAtTwo = .liveRejection 2 3 := rfl

/-- The share seam of `Cost.share_segmented`, as a live plan of the total-state
model — every carrier-global plan is one. -/
def budgetSharePlanLive :
    LivePlan (totalModel Budget.budgetWorkload.step) Budget.budgetWorkload.I :=
  LivePlan.ofBudgetPlan _ Budget.budgetSharePlan

/-- Its achieved cost on the realized execution is the abstract cost: three. -/
theorem budgetSharePlanLive_cost :
    budgetLiveRealization.cost budgetSharePlanLive = 3 := by
  rw [budgetLiveRealization.cost_eq_abstract budgetSharePlanLive]
  exact Budget.budgetSharePlan_cost

/-- **ACCEPTED** — the same deployment at budget 3, with the plan exhibited. -/
def budgetAcceptedAtThree :
    LiveBudgetVerdict (totalModel Budget.budgetWorkload.step) Budget.budgetWorkload 3 :=
  .accepted budgetLiveRealization budgetSharePlanLive
    (Nat.le_of_eq budgetSharePlanLive_cost)

/-- Its report. -/
theorem budgetAcceptedAtThree_report :
    report budgetAcceptedAtThree = .accepted 3 3 := by
  show Report.accepted 3 (budgetLiveRealization.cost budgetSharePlanLive) = .accepted 3 3
  rw [budgetSharePlanLive_cost]

/-! ### `ewModel` — the promotion is blocked, exactly where it should be

`Bounds.ew_rejected_at_zero_over_unreachable_pair` is the defect: a hard refusal
of every plan, over a pair no cut of the element-wide history reaches. Here the
same deployment cannot even be *stated* as a live one. -/

/-- The teleport workload of `Bounds` §7, over the causal model's own op alphabet.
`LiveCost.ewTeleport_is_ewStep` proves the re-alphabeting is not a change of
transition — `Bounds.ewStep` ignores its op — and the two workloads have the same
start, the same occupied states and the same floor. -/
def ewWorkloadOR4 : Budget.Workload (ORSet.ORSet Nat Nat) CausalReach.OR4 where
  I := fun s => ORSet.Present s 0
  step := ewTeleport
  start := CausalReach.ewClashR
  ops := [CausalReach.OR4.a1]
  legal := ⟨Bounds.ew_present_R, Bounds.ew_present_L⟩

/-- The re-alphabeted workload runs the transition `Bounds.ewWorkload` runs. -/
theorem ewWorkloadOR4_step (s : ORSet.ORSet Nat Nat) (o : CausalReach.OR4) :
    ewWorkloadOR4.step s o = Bounds.ewWorkload.step s () := rfl

/-- …and carries the same forced floor of one, from the same clash block. -/
theorem ewOR4_forced_floor_one : Budget.ForcedFloor ewWorkloadOR4 1 :=
  ⟨[[CausalReach.OR4.a1]],
   ⟨Bounds.ew_present_R, Bounds.ew_present_L, Bounds.ew_merge_not_present', trivial⟩,
   rfl, rfl⟩

/-- ⚠ **The element-wide deployment has no live realization at all.** A
`LiveRealization` must start at a world observing the workload's start state, and
`CausalReach.ew_clashR_unreachable` says no cut of the element-wide history
interprets to that state. So the `liveRejected` and `accepted` constructors are
uninhabitable here — not "unproved": there is no object to put in the field. -/
theorem ew_no_live_realization (R : LiveRealization ewModel ewWorkloadOR4) : False :=
  ewModel_never_observes_R ⟨R.start, R.observes_start⟩

/-- …and the promotion hypothesis is refuted, by the route `LiveCost` already
owns: the teleport takes every state to `ewClashL`, and no world observes it. -/
theorem ew_not_reachabilityComplete : ¬ ReachabilityComplete ewModel ewWorkloadOR4 :=
  fun h => ewTeleport_not_grounded (groundable_of_reachabilityComplete h)

/-- **No verdict for this deployment can be a live rejection or an acceptance** —
at any budget. Both constructors carry a realization, and there is none. -/
theorem ew_verdicts_are_never_live (budget : Nat)
    (v : LiveBudgetVerdict ewModel ewWorkloadOR4 budget) :
    ¬ IsLiveRejection v ∧ ¬ IsAccepted v := by
  cases v with
  | liveRejected R n forced over => exact ⟨fun _ => ew_no_live_realization R, id⟩
  | carrierGlobalBound n forced over => exact ⟨id, id⟩
  | accepted R Q upper => exact ⟨id, fun _ => ew_no_live_realization R⟩
  | unresolved O => exact ⟨id, id⟩

/-- **The honest verdict for the element-wide deployment.** -/
def ewCarrierGlobalAtZero : LiveBudgetVerdict ewModel ewWorkloadOR4 0 :=
  .carrierGlobalBound 1 ewOR4_forced_floor_one (by decide)

/-- Its report — the carrier-global headline, not the live one. -/
theorem ewCarrierGlobalAtZero_report :
    report ewCarrierGlobalAtZero = .carrierGlobalBound 0 1 := rfl

/-- ⚠ **THE HEADLINE — the `ew` workload lands in `carrierGlobalBound`, not
`liveRejected`.** Six conjuncts, and the first two are what `Bounds` proved:

  1. the forced floor of one is real, on the re-alphabeted workload, and
  2. `Bounds.ewWorkload` carries it too, so this is that defect and not a cousin;
  3. the carrier-global claim is true — no plan the *lattice* admits fits at
     budget zero, in any universe (`Budget.rejected_sound`, unchanged);
  4. and yet no execution of the element-wide model realizes the workload;
  5. so the promotion hypothesis fails; and
  6. **no verdict for this deployment can be a live rejection or an acceptance**,
     at any budget.

The over-approximation is not kept behind a caveat. `Bounds.ewRejectedAtZero`
says *no plan fits, in any universe*; `ewCarrierGlobalAtZero` says *the lattice
model charges this path, and realizability is not established* — and conjunct 6
is the proof that the stronger sentence is not available to be said. -/
theorem ew_is_carrier_global_not_live :
    Budget.ForcedFloor ewWorkloadOR4 1
      ∧ Budget.ForcedFloor Bounds.ewWorkload 1
      ∧ (∀ Q : Budget.Plan.{0, v, 0} ewWorkloadOR4, ¬ (Q.cost ≤ 0))
      ∧ (LiveRealization ewModel ewWorkloadOR4 → False)
      ∧ ¬ ReachabilityComplete ewModel ewWorkloadOR4
      ∧ (∀ (budget : Nat) (v : LiveBudgetVerdict ewModel ewWorkloadOR4 budget),
          ¬ IsLiveRejection v ∧ ¬ IsAccepted v) :=
  ⟨ewOR4_forced_floor_one, Bounds.ew_forced_floor_one,
   carrierGlobalBound_sound ewOR4_forced_floor_one (by decide),
   ew_no_live_realization, ew_not_reachabilityComplete, ew_verdicts_are_never_live⟩

/-- ⚠ **And the missing sentence cannot be supplied by argument.** The claim a
checker must make to keep the old reading — *a carrier-global rejection is a live
rejection* — restricted to `Type`-level deployments, which only strengthens the
refutation. -/
def CarrierGlobalRejectionIsLive.{v'} : Prop :=
  ∀ {S Op : Type} [MergeState S] (P : RunModel.{0, 0, 0} S Op)
    (awl : Budget.Workload S Op) (n : Nat),
    Budget.ForcedFloor awl n → ∃ R : LiveRealization.{0, v', 0, 0} P awl,
      LiveForcedFloor R.toLiveWorkload n

/-- **It is false**, at the element-wide deployment: the source judgement holds
(`ewOR4_forced_floor_one`) and the target object does not exist. This is the
theorem that makes `carrierGlobalBound` a constructor rather than a caveat. -/
theorem carrier_global_rejection_is_not_live : ¬ CarrierGlobalRejectionIsLive.{v} := by
  intro h
  obtain ⟨R, _⟩ := h ewModel ewWorkloadOR4 1 ewOR4_forced_floor_one
  exact ew_no_live_realization R

/-! ## §7. The bridge to `LiveSegmented`, and the width of the plan space

`LiveSegmented.lean` states the protocol-relative seam judgement over its own run
model — a total `step : W → Op → W` with an `observe`. `PathSegmented` states it
over `LiveCost.Path`. Its docstring names the merge point and asks that the two
not be "left to agree by coincidence": `pathSegmented_iff_liveSegmented` is that
agreement, proved in both directions over the induced model, so the live plan
space this file's verdict quantifies over *is* the space that file optimises. -/

/-- A `LiveSegmented.RunModel` as a `LiveCost.RunModel`: worlds and observation
carried across, and a step of the total transition as the `Step` relation. -/
def ofTotalStep {W : Type u} {Op : Type w} {S : Type v}
    (P : LiveSegmented.RunModel W Op S) : RunModel S Op where
  World := W
  observe := P.observe
  Step := fun a o b => P.step a o = b

/-- **A path of the induced model is a run of the protocol.** The two
reachability notions agree in the direction that matters: a proof-carrying
execution yields the op stream that produces it. -/
theorem reachable_of_path {W : Type u} {Op : Type w} {S : Type v}
    (P : LiveSegmented.RunModel W Op S) :
    ∀ {a b : (ofTotalStep P).World},
      Path (ofTotalStep P) a b → LiveSegmented.Reachable P a b := by
  intro a b p
  induction p with
  | nil a => exact ⟨[], rfl⟩
  | cons a b op h t ih => exact LiveSegmented.reachable_trans ⟨[op], h⟩ ih

/-- **…and a run of the protocol is a path of the induced model.** The other
direction, so the two reachability notions are the same relation and not merely
comparable ones. -/
theorem path_of_exec {W : Type u} {Op : Type w} {S : Type v}
    (P : LiveSegmented.RunModel W Op S) :
    ∀ (a : W) (ops : List Op), Nonempty (Path (ofTotalStep P) a (P.exec a ops)) := by
  intro a ops
  induction ops generalizing a with
  | nil => exact ⟨Path.nil (P := ofTotalStep P) a⟩
  | cons o ops ih =>
      obtain ⟨t⟩ := ih (P.step a o)
      exact ⟨Path.cons (P := ofTotalStep P) a (P.step a o) o rfl t⟩

/-- **`LiveSegmented`'s certificate and `PathSegmented` are the same judgement.**
Not "comparable", not "morally the same": an `Iff`, over the model induced by a
total protocol step. So the live plan space of this file's verdict is exactly the
seam space the sibling file optimises over, and §4's width result there is a
statement about the plans admitted here. -/
theorem pathSegmented_iff_liveSegmented {W : Type u} {Op : Type w} {S : Type v}
    {Seg : Type z} [MergeState S] (P : LiveSegmented.RunModel W Op S)
    (σ : S → Seg) (I : Invariant S) :
    PathSegmented (ofTotalStep P) σ I ↔ LiveSegmented.LiveSegmented P σ I := by
  constructor
  · intro h base x y hco hσ hx hy
    obtain ⟨⟨ops₁, h₁⟩, ⟨ops₂, h₂⟩⟩ := hco
    obtain ⟨px⟩ := path_of_exec P base ops₁
    obtain ⟨py⟩ := path_of_exec P base ops₂
    rw [h₁] at px
    rw [h₂] at py
    exact h x y ⟨base, ⟨px⟩, ⟨py⟩⟩ hσ hx hy
  · intro h x y hco hσ hx hy
    obtain ⟨base, ⟨px⟩, ⟨py⟩⟩ := hco
    exact h base x y ⟨reachable_of_path P px, reachable_of_path P py⟩ hσ hx hy

/-- The direction the plan space needs, as a lemma of its own. -/
theorem pathSegmented_of_liveSegmented {W : Type u} {Op : Type w} {S : Type v}
    {Seg : Type z} [MergeState S] {P : LiveSegmented.RunModel W Op S}
    {σ : S → Seg} {I : Invariant S} (h : LiveSegmented.LiveSegmented P σ I) :
    PathSegmented (ofTotalStep P) σ I :=
  (pathSegmented_iff_liveSegmented P σ I).mpr h

/-- The two-domain live seam of `LiveSegmented` §3, as a live plan of the induced
model. -/
def slotLivePlan :
    LivePlan (ofTotalStep LiveSegmented.slotProtocol) LiveSegmented.atMostOne where
  Seg := Fin 2
  segDecEq := inferInstance
  seam := LiveSegmented.sigmaLive
  valid := pathSegmented_of_liveSegmented LiveSegmented.sigmaLive_liveSegmented

/-- ⚠ **The live plan space is strictly wider than the carrier-global one**, and
that is why `liveRejected` quantifying over `LivePlan` is a strictly stronger
refusal than `Budget.rejected_sound`'s. `slotLivePlan` is a plan of the model
whose seam `SegmentedIConfluent` **refuses** — `LiveSegmented.
no_global_seam_into_fin_two`, whose refusal is charged at a pair the protocol
cannot produce (`the_third_domain_is_charged_for_an_unreachable_pair`).

So the widening is not decoration: there is a deployment where a live rejection
must clear a seam no `Budget.Plan` may carry. -/
theorem live_plan_space_is_strictly_wider :
    PathSegmented (ofTotalStep LiveSegmented.slotProtocol) LiveSegmented.sigmaLive
        LiveSegmented.atMostOne
      ∧ ¬ SegmentedIConfluent LiveSegmented.sigmaLive LiveSegmented.atMostOne :=
  ⟨slotLivePlan.valid,
   LiveSegmented.no_global_seam_into_fin_two LiveSegmented.sigmaLive⟩

/-! ## §8. The TRANSPORTS row

**Carrier-global verdict → live verdict** ⚠ — the verdict-level twin of
`docs/TRANSPORTS.md` row 10.

  * *source judgement* — `LiveBudgetVerdict.carrierGlobalBound n forced over`:
    a `Budget.ForcedFloor awl n` with `budget < n`, whose claim
    (`carrierGlobalBound_sound`) is about `Budget.Plan`s, i.e. about the seams
    the **lattice** admits.
  * *target judgement* — `LiveBudgetVerdict.liveRejected R n forced over`: a
    realization of the workload by an execution of the model, carved into `n`
    coordination points, refusing every **live** plan (`liveRejected_sound`).
  * *transport* — `carrierGlobal_promotes`, and
    `LiveObligation.closedByReachability` at the verdict level.
  * *needs* — **`ReachabilityComplete P awl`**: `LiveCost.Grounds P awl.step`
    plus a start world observing `awl.start`.
  * *without it* — `carrier_global_rejection_is_not_live` refutes the
    unconditional claim outright, at `ewModel` / `ewWorkloadOR4`:
    `ewOR4_forced_floor_one` is a genuine source judgement,
    `ew_not_reachabilityComplete` refutes the hypothesis, and
    `ew_no_live_realization` proves the target object does not exist — the
    deployment has no live realization at any budget
    (`ew_verdicts_are_never_live`).
  * ⚠ *and the honest note*, inherited from row 10:
    `totalModel_reachability_complete` — every workload is reachability-complete
    for its own total-state model, so promoting there is free and buys nothing.
    The hypothesis has teeth only against a model that refuses transitions. -/

/-- **The readings, side by side.** The same shape of workload, three verdicts:
the budget session is refused live at budget 2; it is accepted live at budget 3
with the plan exhibited; and the element-wide session — which `Bounds` refuses at
budget 0 *in any universe* — cannot be refused live at all. -/
example :
    report budgetLiveRejectedAtTwo = .liveRejection 2 3
      ∧ report budgetAcceptedAtThree = .accepted 3 3
      ∧ report ewCarrierGlobalAtZero = .carrierGlobalBound 0 1
      ∧ ∀ (b : Nat) (v : LiveBudgetVerdict ewModel ewWorkloadOR4 b),
          ¬ IsLiveRejection v :=
  ⟨budgetLiveRejectedAtTwo_report, budgetAcceptedAtThree_report,
   ewCarrierGlobalAtZero_report, fun b v => (ew_verdicts_are_never_live b v).1⟩

/-- The headlines are the words codex wrote, pinned to the constructors. -/
example :
    (report budgetLiveRejectedAtTwo).headline
        = "LIVE REJECTION — no protocol-admissible plan fits this reachable workload."
      ∧ (report ewCarrierGlobalAtZero).headline
        = "CARRIER-GLOBAL LOWER BOUND — the abstract lattice model charges this path; \
operational realizability not established." :=
  ⟨rfl, rfl⟩

end Uwueave.LiveBudget
