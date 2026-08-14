/-
# Uwueave.LiveCost — a coordination floor may only accuse a pair some execution
actually connects.

## The hole this file closes

`Bounds.lean` §7 proves it against itself. `ewWorkload` is a perfectly legal
`Budget.Workload`; it carries a genuine `Budget.ForcedFloor _ 1`; and
`Bounds.ew_rejected_at_zero_over_unreachable_pair` runs that floor through
`Budget.rejected_sound` to the verdict **"no plan fits, in any universe"** — over
the pair `CausalReach.ewClashL` / `ewClashR`, which `CausalReach.
ew_clashL_unreachable` and `ew_clashR_unreachable` prove **no cut of the
element-wide history reaches**. The checker refuses a session on the strength of
a state nothing produces.

The mechanism is small and total. `Cost.lean` prices a `step : S → Op → S` and a
`List Op`: a total order of ops with **no happens-before**. `Budget.RunLegal`
checks the occupied states are *legal*. Nothing checks they are *reachable*,
because the cost model has no history to check them against —
`Bounds.clashBlocks_accuse_only_occupied` says a floor accuses only states the
run passes through, and that is exactly as sound as the `step` it was handed.
`Bounds.ewStep` is a one-op teleport into the unreachable state, and the theory
accepts it.

## Codex's prescription, which this file executes

> Index workloads by **proof-carrying operational paths**, but parameterize
> `Cost` over an ABSTRACT execution model rather than importing `CausalReach`
> directly.

and, explicitly, that the cheap repair is **too weak**:

> a side condition `Reachable s ∧ Reachable (run step s b)` does not say the two
> states are reachable *in that order*, *in one coherent history*, *co-reachable
> from the same ancestor*, or *related by happens-before*.

So the object is a `Path`: an inductive chain of `RunModel.Step`s whose
concatenation (`Path.append`) and prefix/suffix decomposition
(`Path.legal_append`) are **structural** — consequences of the constructor, not
side conditions anyone can forget to propagate. A `ClashChain` carves a path into
blocks, and a block cannot be written down without exhibiting the `Path` joining
the two states it accuses (`ClashChain.accused_are_connected`). That is the
repair: `ew_pair_refuses_a_live_accusation` is not a check that fires, it is a
shape that cannot be built.

`World` is a field of the model and is permitted to be strictly richer than `S`.
That is not generality for its own sake: `WorldFuture.delivery_futures_differ`
exhibits two worlds with *equal* materialized state whose futures differ, because
the issued pool differs — so a repair that added a field to the state carrier
would be repairing the wrong object, and
`WorldFuture.delivery_future_is_not_state_indexed` proves no state-level relation
can do this job at all.

## What is here

  * **§1** `RunModel`, `Path` (proof-carrying, inductive), `Path.append`,
    `Path.crossings`, `Path.Legal`, and the two counting lemmas.
  * **§2** `LiveWorkload`, `ClashChain`, `LiveForcedFloor`, the live lower bound
    (`ClashChain.length_le_crossings`) and `live_rejected_sound` — `Budget`'s
    refusal, now unable to name a pair no path connects. `LiveFork` and
    `LiveFork.charges` are the concurrent half, which is where a delivery
    model's bound actually lives.
  * **§3** **three adapters**, each exhibited rather than named: the total-state
    machine `Cost.run` (`totalModel`), under which the old theory is a special
    case (`pathOfOps_crossings`, `liveOfWorkload`); the causal cuts of
    `CausalReach` (`causalModel`); and `Necessity.Impl` (`implModel`), under
    which a `Necessity.ReachableClash` *is* a `LiveFork`.
  * **§4** the three separation witnesses (below).
  * **§5** the transport theorem `cost_floor_becomes_live` and its
    counterexample.
  * **§6** profiles survive unchanged: `CoordEffect.Profile`, `⊗`, `optimum`,
    `Strategy` re-used verbatim over path costs.

## The separation — the three witnesses

  1. `orset_tag_scoped_clash_is_live` — the tag-scoped OR-Set clash, in the
     causal model over `CausalReach.or4H`: both clash states are worlds, and they
     are joined to a **common ancestor cut** by two real delivery paths. Every
     valid seam charges the pair at least one crossing, and
     `orset_live_bound_inhabited` instantiates that at a concrete seam so the
     bound is a number rather than an empty quantifier.
  2. `ew_pair_refuses_a_live_accusation` — the element-wide pair, in the causal
     model over `CausalReach.ewH`: **no world observes either state**, hence no
     `ClashChain` block and no `LiveFork` can accuse them, hence the teleport is
     not grounded there. The old floor (`Bounds.ew_forced_floor_one`) is quoted
     alongside, so the separation is visible in one statement: `ForcedFloor` yes,
     live accusation no.
  3. `budget_live_floor_is_three` — `Cost.lean` §6's budget workload, through the
     total-state adapter, still forces three coordination events under every seam
     in every universe, at the same crossing count. The repair costs the old
     results nothing.

⚠ **Witness 1 is a fork, not a sequential floor, and that is the honest shape.**
Two states related by *delivery* are lattice-comparable, and comparable states do
not clash — `Cost.clashBlocks_nil_of_inflationary`, re-proved here at the path
level as `ClashChain.length_eq_zero_of_inflationary`. The coordination the OR-Set
clash forces is between two branches of one history, which is what `LiveFork` is
and what `Bounds` §6 already found at the session level. ⟨scope⟩ We do **not**
prove that the tag-scoped delivery model's sequential live floor is zero: that
needs `or4Interp` to be inflationary along a delivery step, which is not proved
here — only the general theorem that would consume it.

## ⚠ A SECOND HOLE EXISTS AND IS NOT FIXED HERE

`SegmentedIConfluent` is **lattice-global**: it quantifies over all legal states,
so an unreachable clash still shrinks the space of admissible seams even when it
raises no floor. `Bounds.latticeOnly_clash_still_separated` proves exactly that,
at exactly the pair witness 2 refuses — every valid seam for presence must put
`ewClashL` and `ewClashR` in different fibers. So a *plan*'s achievable cost is
still charged for a pair no history produces, even though its *floor* no longer
is. That hole is a sibling lane's — `Uwueave/LiveSegmented.lean` — and this file
neither fixes it nor imports that file.

## Non-claims, labelled

  * ⟨TERMINAL for this file⟩ **A model is a hypothesis, not a fact about the
    world.** `RunModel` is supplied by the modeller; nothing here says a given
    model is the protocol's. What the parameterization buys is that the
    modeller's choice is now *load-bearing and visible*:
    `totalModel_grounds_everything` says the total-state model grounds every
    transition whatsoever, so a floor transported there is exactly as strong as
    `Cost.lean`'s and no stronger, while the causal model refuses the teleport.
    The file makes the choice a hypothesis with a theorem attached; it does not
    make the choice for you.
  * ⟨scope⟩ **`Grounds` is a total simulation.** The transport hypothesis asks
    for a `lift : World → Op → World` defined at *every* world and op. That is
    what a total `step` deserves, and it is what fails in a delivery model, where
    an op can be delivered only once. A partial grounding — enough to carry one
    particular stream — would transport more workloads and is not defined here.
  * ⟨SCOPE U-0090⟩ **Crossings are not meetings**, inherited whole from `Cost.lean` and
    `CoordEffect.lean`. Every `Nat` here is a seam crossing along one replica's
    path.
  * ⟨scope⟩ **`[DecidableEq Seg]`** on every seam, inherited from
    `Cost.crossings`. Not vacuous: `Bounds.id_segmented` and `Bounds.orsetDecEq`
    instantiate the OR-Set bound at a concrete seam.
  * ⟨SCOPE U-0091⟩ **No liveness, no delivery schedule, no time.** A `Path` says a
    sequence of steps *may* happen, never that it will. `Liveness.lean` owns that
    axis and is not composed with this one.
-/
import Uwueave.Bounds

namespace Uwueave.LiveCost

open Uwueave Uwueave.Catalog Uwueave.Segmented
open Uwueave.CoordEffect

universe u v w x

/-! ## §1. The abstract execution model, and proof-carrying paths -/

/-- **An abstract execution model.** A type of `World`s — replica situations, in
whatever detail the modeller needs — a projection `observe` onto the merge-state
carrier the invariant is written against, and a `Step` relation saying which op
takes which world to which.

⚠ `World` is deliberately allowed to be **strictly richer** than `S`.
`WorldFuture.delivery_futures_differ` is the reason: two replicas can have equal
materialized state and different futures, because what has been *issued* differs.
A repair that added a field to `S` would be repairing the wrong object. -/
structure RunModel.{us, uo, ur} (S : Type us) (Op : Type uo) where
  /-- The worlds — replica situations, richer than the state if need be. -/
  World : Type ur
  /-- What a world materializes: the state the invariant is written against. -/
  observe : World → S
  /-- Which op takes which world to which. Not a function: a model may leave an
  op undefined at a world (a delivery cannot happen twice) or admit several
  successors. -/
  Step : World → Op → World → Prop

/-- **A proof-carrying operational path.** Not "these two states are each
reachable" — a `Path P a b` is a *chain of `P.Step`s* joining `a` to `b`. Two
worlds are related by one exactly when a single coherent execution goes from the
first to the second, in that order.

This is codex's point about the cheap repair: `Reachable s ∧ Reachable t` says
nothing about order, about being co-reachable from a common ancestor, or about
happens-before. A path says all three by construction, and `Path.append` /
`Path.legal_append` make concatenation and prefix-closure **structural** rather
than side conditions someone must remember to propagate. -/
inductive Path.{us, uo, ur} {S : Type us} {Op : Type uo}
    (P : RunModel.{us, uo, ur} S Op) : P.World → P.World → Type (max uo ur) where
  /-- The empty execution: a world reaches itself. -/
  | nil (a : P.World) : Path P a a
  /-- One step of the model, then the rest of the execution. -/
  | cons (a b : P.World) {c : P.World} (op : Op) (h : P.Step a op b)
      (t : Path P b c) : Path P a c

/-- **Concatenation is structural.** Two executions that meet at a world compose
into one execution. -/
def Path.append {S : Type u} {Op : Type w} {P : RunModel S Op} :
    {a b c : P.World} → Path P a b → Path P b c → Path P a c
  | _, _, _, .nil _, q => q
  | _, _, _, .cons a b op h t, q => .cons a b op h (t.append q)

/-- **The quantity, over a path.** The number of steps of the execution at which
the seam value `σ` changes — `Cost.crossings`, freed from the assumption that a
workload is a total order of ops with no history. -/
def Path.crossings {S : Type u} {Seg : Type v} {Op : Type w} [DecidableEq Seg]
    {P : RunModel S Op} (σ : S → Seg) : {a b : P.World} → Path P a b → Nat
  | _, _, .nil _ => 0
  | _, _, .cons a b _ _ t =>
      (if σ (P.observe b) = σ (P.observe a) then 0 else 1) + Path.crossings σ t

/-- The empty execution costs nothing. -/
@[simp] theorem Path.crossings_nil {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {P : RunModel S Op} (σ : S → Seg) (a : P.World) :
    (Path.nil (P := P) a).crossings σ = 0 := rfl

/-- **Cost is additive along concatenation** — `Cost.crossings_append` at the
path level, and the reason a `ClashChain`'s blocks may be counted one at a
time. -/
theorem Path.crossings_append {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {P : RunModel S Op} (σ : S → Seg) :
    ∀ {a b c : P.World} (p : Path P a b) (q : Path P b c),
      (p.append q).crossings σ = p.crossings σ + q.crossings σ := by
  intro a b c p
  induction p with
  | nil a =>
      intro q
      show q.crossings σ = 0 + q.crossings σ
      omega
  | cons a b op h t ih =>
      intro q
      show (if σ (P.observe b) = σ (P.observe a) then 0 else 1)
          + (t.append q).crossings σ
        = ((if σ (P.observe b) = σ (P.observe a) then 0 else 1) + t.crossings σ)
          + q.crossings σ
      rw [ih q]
      omega

/-- **A free execution never leaves its fiber.** Zero crossings means the seam
value at the end is the seam value at the start. -/
theorem Path.sigma_const_of_crossings_eq_zero {S : Type u} {Seg : Type v}
    {Op : Type w} [DecidableEq Seg] {P : RunModel S Op} (σ : S → Seg) :
    ∀ {a b : P.World} (p : Path P a b), p.crossings σ = 0 →
      σ (P.observe b) = σ (P.observe a) := by
  intro a b p
  induction p with
  | nil a => intro _; rfl
  | cons a b op h t ih =>
      intro h0
      have h0' : (if σ (P.observe b) = σ (P.observe a) then 0 else 1)
          + t.crossings σ = 0 := h0
      by_cases hc : σ (P.observe b) = σ (P.observe a)
      · rw [if_pos hc] at h0'
        exact (ih (by omega)).trans hc
      · rw [if_neg hc] at h0'
        exact absurd h0' (by omega)

/-- The contrapositive, in the form the block calculus consumes: an execution
that ends in a different fiber than it started in costs at least one crossing. -/
theorem Path.one_le_crossings_of_sigma_ne {S : Type u} {Seg : Type v}
    {Op : Type w} [DecidableEq Seg] {P : RunModel S Op} (σ : S → Seg)
    {a b : P.World} (p : Path P a b) (h : σ (P.observe b) ≠ σ (P.observe a)) :
    1 ≤ p.crossings σ :=
  Nat.pos_of_ne_zero fun hz => h (Path.sigma_const_of_crossings_eq_zero σ p hz)

/-- **Every world the execution occupies is legal.** `Budget.RunLegal` along a
path — and, unlike `RunLegal`, every world it ranges over is one the model's own
`Step` relation produced. -/
def Path.Legal {S : Type u} {Op : Type w} {P : RunModel S Op} (I : Invariant S) :
    {a b : P.World} → Path P a b → Prop
  | _, _, .nil a => I (P.observe a)
  | _, _, .cons a _ _ _ t => I (P.observe a) ∧ Path.Legal I t

/-- A legal execution starts legal. -/
theorem Path.Legal.head {S : Type u} {Op : Type w} {P : RunModel S Op}
    {I : Invariant S} {a b : P.World} {p : Path P a b} (h : p.Legal I) :
    I (P.observe a) := by
  cases p with
  | nil a => exact h
  | cons a b op hs t => exact h.1

/-- A legal execution ends legal. -/
theorem Path.Legal.last {S : Type u} {Op : Type w} {P : RunModel S Op}
    {I : Invariant S} : ∀ {a b : P.World} (p : Path P a b), p.Legal I →
      I (P.observe b) := by
  intro a b p
  induction p with
  | nil a => exact id
  | cons a b op hs t ih => exact fun hl => ih hl.2

/-- **Legality is closed under concatenation, and under taking prefixes and
suffixes** — the same iff, in both directions, and structural. This is the
prefix-closure codex asks for: a property of the constructor rather than an
obligation on whoever assembles a workload. -/
theorem Path.legal_append {S : Type u} {Op : Type w} {P : RunModel S Op}
    {I : Invariant S} :
    ∀ {a b c : P.World} (p : Path P a b) (q : Path P b c),
      (p.append q).Legal I ↔ (p.Legal I ∧ q.Legal I) := by
  intro a b c p
  induction p with
  | nil a =>
      intro q
      exact ⟨fun h => ⟨h.head, h⟩, fun h => h.2⟩
  | cons a b op hs t ih =>
      intro q
      constructor
      · intro hl
        exact ⟨⟨hl.1, ((ih q).mp hl.2).1⟩, ((ih q).mp hl.2).2⟩
      · intro hl
        exact ⟨hl.1.1, (ih q).mpr ⟨hl.1.2, hl.2⟩⟩

/-! ## §2. Live workloads, live floors, and the refusal that replaces a check -/

/-- **The thing a live budget is a budget for.** A start world, a stop world, and
an *execution of the model* joining them — with the proof that every world it
occupies is legal.

The difference from `Budget.Workload` is the whole point of the file: a
`Workload` carries a `List Op` and a legality proof, and *any* `step` at all may
have produced its states. A `LiveWorkload` carries a `Path`, so every state it
occupies was produced by the model's own `Step`. -/
structure LiveWorkload {S : Type u} {Op : Type w} [MergeState S]
    (P : RunModel S Op) where
  /-- The invariant the session must maintain. -/
  I : Invariant S
  /-- Where the session starts. -/
  start : P.World
  /-- Where it ends. -/
  stop : P.World
  /-- The execution itself — proof-carrying, step by step. -/
  path : Path P start stop
  /-- Every world it occupies is legal. -/
  legal : path.Legal I

/-- **The achieved cost of a live workload under a plan.** A plan is
`CoordEffect.Strategy` — a seam bundled with its `SegmentedIConfluent` proof —
re-used unchanged, because a strategy never cared where the trajectory came
from. -/
def LiveWorkload.cost {S : Type u} {Seg : Type v} {Op : Type w} [MergeState S]
    [DecidableEq Seg] {P : RunModel S Op} (wl : LiveWorkload P)
    (τ : Strategy wl.I Seg) : Nat :=
  wl.path.crossings τ.seam

/-- **A clash carving of an execution.** Each block is a *real path of the model*
whose two endpoints are each legal and whose merge is not.

⚠ Compare `Cost.ClashBlocks`, whose blocks are `List Op` and whose accused pair
is whatever the supplied `step` computes. Here a block **cannot be written down**
without exhibiting the execution that joins the pair it accuses — which is
precisely what `Bounds.ewStep` could not have supplied. -/
inductive ClashChain.{us, uo, ur} {S : Type us} {Op : Type uo} [MergeState S]
    {P : RunModel.{us, uo, ur} S Op} (I : Invariant S) :
    P.World → P.World → Type (max uo ur) where
  /-- No further coordination points. -/
  | done (a : P.World) : ClashChain I a a
  /-- A block: an execution from `a` to `b`, both legal, merging illegally. -/
  | block (a b : P.World) {c : P.World} (blk : Path P a b)
      (ha : I (P.observe a)) (hb : I (P.observe b))
      (hclash : ¬ I (P.observe a ⊔ P.observe b))
      (rest : ClashChain I b c) : ClashChain I a c

/-- How many coordination points the carving names. -/
def ClashChain.length {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {I : Invariant S} :
    {a b : P.World} → ClashChain I a b → Nat
  | _, _, .done _ => 0
  | _, _, .block _ _ _ _ _ _ rest => rest.length + 1

/-- The execution a carving carves. -/
def ClashChain.flatten {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {I : Invariant S} :
    {a b : P.World} → ClashChain I a b → Path P a b
  | _, _, .done a => .nil a
  | _, _, .block _ _ blk _ _ _ rest => blk.append rest.flatten

/-- The pairs a carving accuses. -/
def ClashChain.Accuses {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {I : Invariant S} :
    {a b : P.World} → ClashChain I a b → P.World → P.World → Prop
  | _, _, .done _, _, _ => False
  | _, _, .block a b _ _ _ _ rest, x, y => (x = a ∧ y = b) ∨ rest.Accuses x y

/-- **Every accused pair is joined by an execution of the model.** Not "both are
reachable" — a single `Path` from the first to the second, so the pair is
ordered, co-reachable from a common ancestor (the first), and related by the
model's own happens-before.

This is the theorem with no counterpart in `Cost.lean`, and it is discharged by
the constructor rather than by an argument: there is nowhere to put an accusation
that lacks its path. The refusal direction needs no lemma at all — an accusation
names *worlds*, so a state no world observes cannot appear in one, which is
exactly how §4's witness 2 discharges itself. -/
theorem ClashChain.accused_are_connected {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {I : Invariant S} :
    ∀ {a b : P.World} (ch : ClashChain I a b) {x y : P.World}, ch.Accuses x y →
      Nonempty (Path P x y) ∧ I (P.observe x) ∧ I (P.observe y)
        ∧ ¬ I (P.observe x ⊔ P.observe y) := by
  intro a b ch
  induction ch with
  | done a => intro x y h; exact (h : False).elim
  | block a b blk ha hb hclash rest ih =>
      intro x y h
      have h' : (x = a ∧ y = b) ∨ rest.Accuses x y := h
      rcases h' with ⟨rfl, rfl⟩ | h''
      · exact ⟨⟨blk⟩, ha, hb, hclash⟩
      · exact ih h''

/-- **THE LIVE LOWER BOUND.** A carving into `n` clash blocks costs at least `n`
crossings under the given seam — and the seam is universally quantified at every
use site below, so at every segment type in every universe.

`Cost.coordination_lower_bound`'s argument, verbatim: a valid seam certifies
same-fiber merges, so a clashing pair cannot share a fiber, so each block moves
the seam at least once, and `Path.crossings_append` adds them up. What changed is
the hypothesis — each block now carries the execution that produced its pair. -/
theorem ClashChain.length_le_crossings {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} {I : Invariant S}
    {σ : S → Seg} (hseg : SegmentedIConfluent σ I) :
    ∀ {a b : P.World} (ch : ClashChain I a b),
      ch.length ≤ (ch.flatten).crossings σ := by
  intro a b ch
  induction ch with
  | done a => exact Nat.zero_le _
  | block a b blk ha hb hclash rest ih =>
      have hne : σ (P.observe b) ≠ σ (P.observe a) :=
        (Bounds.valid_seam_separates_clash hseg ha hb hclash).symm
      have h1 : 1 ≤ blk.crossings σ := Path.one_le_crossings_of_sigma_ne σ blk hne
      show rest.length + 1 ≤ (blk.append rest.flatten).crossings σ
      rw [Path.crossings_append]
      omega

/-- **`n` is a live forced floor for this workload**: a clash carving of the
workload's *own execution* into `n` blocks. `Budget.ForcedFloor` with the one
field that was missing — the blocks are paths of the model. -/
def LiveForcedFloor {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} (wl : LiveWorkload P) (n : Nat) : Prop :=
  ∃ ch : ClashChain wl.I wl.start wl.stop, ch.flatten = wl.path ∧ n = ch.length

/-- A live floor bounds every plan's achieved cost from below, at every segment
type in every universe — `Budget.ForcedFloor.le_cost`, over paths. -/
theorem LiveForcedFloor.le_cost {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} {wl : LiveWorkload P}
    {n : Nat} (h : LiveForcedFloor wl n) (τ : Strategy wl.I Seg) :
    n ≤ wl.cost τ := by
  obtain ⟨ch, hflat, hn⟩ := h
  have hb := ClashChain.length_le_crossings (σ := τ.seam) τ.valid ch
  rw [hflat] at hb
  show n ≤ wl.path.crossings τ.seam
  omega

/-- **`rejected` means no plan fits — and now the pair it refuses over is one
some execution of the model actually produces.** The statement is
`Budget.rejected_sound`'s; the hypothesis is the one that previously had no field
to live in. -/
theorem live_rejected_sound {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} {wl : LiveWorkload P}
    {budget n : Nat} (forced : LiveForcedFloor wl n) (over : budget < n) :
    ∀ τ : Strategy wl.I Seg, ¬ (wl.cost τ ≤ budget) := by
  intro τ hle
  have := forced.le_cost τ
  omega

/-! ### The concurrent half — a fork is two executions from ONE world

`Bounds` §4 proves the per-stream floor is blind to a fork and §6 recovers the
charge at the session level. Both survive the move to paths, and the fork is the
shape a *delivery* model needs: two states related by delivery are
lattice-comparable, and comparable states never clash. -/

/-- **A live fork.** One base world, two executions of the model leaving it, and
two legal endpoints whose merge is illegal. This is `Necessity.ReachableClash`
with the implementation replaced by an arbitrary model — and it is why codex's
"reachable ∧ reachable" is too weak: a fork says the two are reachable *from the
same ancestor, in one coherent history*. -/
structure LiveFork {S : Type u} {Op : Type w} [MergeState S]
    (P : RunModel S Op) (I : Invariant S) where
  /-- The common ancestor. -/
  base : P.World
  /-- One branch's endpoint. -/
  x : P.World
  /-- The other branch's endpoint. -/
  y : P.World
  /-- The execution reaching `x`. -/
  px : Path P base x
  /-- The execution reaching `y`. -/
  py : Path P base y
  /-- `x` is legal. -/
  hx : I (P.observe x)
  /-- `y` is legal. -/
  hy : I (P.observe y)
  /-- …and their merge is not. -/
  hbad : ¬ I (P.observe x ⊔ P.observe y)

/-- **A live fork charges the pair, under every valid seam.** If both branches
were free, both endpoints would sit in the base's fiber, hence in each other's,
and a valid seam would certify their merge — which the fork forbids.
`Bounds.fork_clash_charges_the_pair`, over paths. -/
theorem LiveFork.charges {S : Type u} {Seg : Type v} {Op : Type w} [MergeState S]
    [DecidableEq Seg] {P : RunModel S Op} {I : Invariant S} (F : LiveFork P I)
    {σ : S → Seg} (hseg : SegmentedIConfluent σ I) :
    0 < F.px.crossings σ + F.py.crossings σ := by
  by_cases h1 : F.px.crossings σ = 0
  · by_cases h2 : F.py.crossings σ = 0
    · have e1 := Path.sigma_const_of_crossings_eq_zero σ F.px h1
      have e2 := Path.sigma_const_of_crossings_eq_zero σ F.py h2
      exact absurd (hseg _ _ (e1.trans e2.symm) F.hx F.hy).1 F.hbad
    · omega
  · omega

/-! ### Calibration — an inflationary model has no sequential floor

`Cost.clashBlocks_nil_of_inflationary` at the path level. It is why the OR-Set
witness below is a fork: along a single execution of a delivery model the state
only grows, and comparable states do not clash. -/

/-- Every step of the model only moves up the lattice. -/
def StepInflationary {S : Type u} {Op : Type w} [MergeState S]
    (P : RunModel S Op) : Prop :=
  ∀ (a : P.World) (o : Op) (b : P.World), P.Step a o b → P.observe a ⊑ P.observe b

/-- An inflationary execution only moves up. -/
theorem path_inflationary {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} (h : StepInflationary P) :
    ∀ {a b : P.World}, Path P a b → P.observe a ⊑ P.observe b := by
  intro a b p
  induction p with
  | nil a => exact leq_refl _
  | cons a b op hs t ih => exact leq_trans (h a op b hs) ih

/-- **An inflationary model admits no clash carving at all.** So a positive
*sequential* live floor is evidence of a step that overwrites — and a delivery
model, whose steps only add, carries its coordination charge as a fork
instead. -/
theorem ClashChain.length_eq_zero_of_inflationary {S : Type u} {Op : Type w}
    [MergeState S] {P : RunModel S Op} {I : Invariant S}
    (hinf : StepInflationary P) :
    ∀ {a b : P.World} (ch : ClashChain I a b), ch.length = 0 := by
  intro a b ch
  cases ch with
  | done a => rfl
  | block a b blk ha hb hclash rest =>
      have hle : P.observe a ⊔ P.observe b = P.observe b := path_inflationary hinf blk
      exact absurd (by rw [hle]; exact hb) hclash

/-! ## §3. Three adapters — the abstraction is not vacuous -/

/-! ### (a) The total-state machine: `Cost.run` as a `RunModel` -/

/-- **The old theory as a model.** Worlds *are* states, `observe` is the
identity, and every op steps every state to `step s o`. `Cost.lean`'s workload
model is exactly this instance — the sense in which the old theory is a special
case, made precise by `pathOfOps_crossings` and `liveOfWorkload` below. -/
def totalModel {S : Type u} {Op : Type w} (step : S → Op → S) : RunModel S Op where
  World := S
  observe := id
  Step := fun s o s' => step s o = s'

/-- **A grounding**: the model can perform the total transition `step` at every
world, and performing it observes exactly what `step` computes. This is the
load-bearing hypothesis of the transport theorem in §5 — the thing `Cost.lean`
assumed silently by having no model at all. -/
structure Grounds {S : Type u} {Op : Type w} (P : RunModel S Op)
    (step : S → Op → S) where
  /-- The world an op takes a world to. -/
  lift : P.World → Op → P.World
  /-- …and it really is a step of the model. -/
  steps : ∀ (a : P.World) (o : Op), P.Step a o (lift a o)
  /-- …observing exactly what the total transition computes. -/
  observes : ∀ (a : P.World) (o : Op), P.observe (lift a o) = step (P.observe a) o

/-- Groundedness as a proposition — "this model can perform this transition" —
so that a model's **refusal** of a transition is statable. `ewTeleport_not_grounded`
is the refusal that carries §4's witness 2. -/
def Groundable {S : Type u} {Op : Type w} (P : RunModel S Op)
    (step : S → Op → S) : Prop := Nonempty (Grounds P step)

/-- The world an op stream reaches, through a grounding. -/
def Grounds.runW {S : Type u} {Op : Type w} {P : RunModel S Op}
    {step : S → Op → S} (G : Grounds P step) : P.World → List Op → P.World
  | a, [] => a
  | a, o :: os => G.runW (G.lift a o) os

/-- **An op stream, as an execution of the model.** This is where a `List Op`
becomes a `Path`: each op is discharged by the grounding's `steps`. -/
def Grounds.path {S : Type u} {Op : Type w} {P : RunModel S Op}
    {step : S → Op → S} (G : Grounds P step) :
    (a : P.World) → (os : List Op) → Path P a (G.runW a os)
  | a, [] => .nil a
  | a, o :: os => .cons a (G.lift a o) o (G.steps a o) (G.path (G.lift a o) os)

/-- The grounded run observes exactly `Cost.run`. -/
theorem Grounds.observe_runW {S : Type u} {Op : Type w} {P : RunModel S Op}
    {step : S → Op → S} (G : Grounds P step) :
    ∀ (a : P.World) (os : List Op),
      P.observe (G.runW a os) = Cost.run step (P.observe a) os := by
  intro a os
  induction os generalizing a with
  | nil => rfl
  | cons o os ih =>
      show P.observe (G.runW (G.lift a o) os)
        = Cost.run step (step (P.observe a) o) os
      rw [ih (G.lift a o), G.observes a o]

/-- **The grounded execution costs exactly what the op stream cost.** So no
crossing count moves under the repair: `Cost.crossings` is `Path.crossings` at a
grounded model. -/
theorem Grounds.path_crossings {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {P : RunModel S Op} {step : S → Op → S} (G : Grounds P step)
    (σ : S → Seg) :
    ∀ (a : P.World) (os : List Op),
      (G.path a os).crossings σ = Cost.crossings σ step (P.observe a) os := by
  intro a os
  induction os generalizing a with
  | nil => rfl
  | cons o os ih =>
      show (if σ (P.observe (G.lift a o)) = σ (P.observe a) then 0 else 1)
          + (G.path (G.lift a o) os).crossings σ
        = (if σ (step (P.observe a) o) = σ (P.observe a) then 0 else 1)
          + Cost.crossings σ step (step (P.observe a) o) os
      rw [ih (G.lift a o), G.observes a o]

/-- Legality of the grounded execution is exactly `Budget.RunLegal`. -/
theorem Grounds.path_legal {S : Type u} {Op : Type w} {P : RunModel S Op}
    {step : S → Op → S} (G : Grounds P step) (I : Invariant S) :
    ∀ (a : P.World) (os : List Op),
      (G.path a os).Legal I ↔ Budget.RunLegal I step (P.observe a) os := by
  intro a os
  induction os generalizing a with
  | nil => exact Iff.rfl
  | cons o os ih =>
      have h2 := ih (G.lift a o)
      rw [G.observes a o] at h2
      show I (P.observe a) ∧ (G.path (G.lift a o) os).Legal I
        ↔ I (P.observe a) ∧ Budget.RunLegal I step (step (P.observe a) o) os
      exact and_congr Iff.rfl h2

/-- The world a *block decomposition* reaches, through a grounding. Structural on
the block list, so no "run of an append" equation is ever needed and no transport
cast appears in `Grounds.chain`. -/
def Grounds.runBlocks {S : Type u} {Op : Type w} {P : RunModel S Op}
    {step : S → Op → S} (G : Grounds P step) : P.World → List (List Op) → P.World
  | a, [] => a
  | a, b :: bs => G.runBlocks (G.runW a b) bs

/-- **The transport itself.** A `Cost.ClashBlocks` decomposition, carried across
a grounding into a `ClashChain` of the model — every block now a real execution,
every accused pair now joined by one. -/
def Grounds.chain {S : Type u} {Op : Type w} [MergeState S] {P : RunModel S Op}
    {step : S → Op → S} (G : Grounds P step) (I : Invariant S) :
    (a : P.World) → (bs : List (List Op)) →
    Cost.ClashBlocks I step (P.observe a) bs → ClashChain I a (G.runBlocks a bs)
  | a, [], _ => .done a
  | a, b :: bs, h =>
      .block a (G.runW a b) (G.path a b) h.1
        (by rw [G.observe_runW]; exact h.2.1)
        (by rw [G.observe_runW]; exact h.2.2.1)
        (G.chain I (G.runW a b) bs (by rw [G.observe_runW]; exact h.2.2.2))

/-- The carving has exactly as many blocks as the decomposition. -/
theorem Grounds.chain_length {S : Type u} {Op : Type w} [MergeState S]
    {P : RunModel S Op} {step : S → Op → S} (G : Grounds P step) (I : Invariant S) :
    ∀ (a : P.World) (bs : List (List Op))
      (h : Cost.ClashBlocks I step (P.observe a) bs),
      (G.chain I a bs h).length = bs.length := by
  intro a bs
  induction bs generalizing a with
  | nil => intro _; rfl
  | cons b bs ih =>
      intro h
      have hb : Cost.ClashBlocks I step (P.observe (G.runW a b)) bs := by
        rw [G.observe_runW]; exact h.2.2.2
      show (G.chain I (G.runW a b) bs hb).length + 1 = bs.length + 1
      rw [ih (G.runW a b) hb]

/-- …and its execution costs exactly what the op stream cost. Transport moves the
bound without moving the number. -/
theorem Grounds.chain_crossings {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} {step : S → Op → S}
    (G : Grounds P step) (I : Invariant S) (σ : S → Seg) :
    ∀ (a : P.World) (bs : List (List Op))
      (h : Cost.ClashBlocks I step (P.observe a) bs),
      ((G.chain I a bs h).flatten).crossings σ
        = Cost.crossings σ step (P.observe a) bs.flatten := by
  intro a bs
  induction bs generalizing a with
  | nil => intro _; rfl
  | cons b bs ih =>
      intro h
      have hb : Cost.ClashBlocks I step (P.observe (G.runW a b)) bs := by
        rw [G.observe_runW]; exact h.2.2.2
      show ((G.path a b).append ((G.chain I (G.runW a b) bs hb).flatten)).crossings σ
        = Cost.crossings σ step (P.observe a) (b ++ bs.flatten)
      rw [Path.crossings_append, ih (G.runW a b) hb, G.path_crossings σ a b,
        G.observe_runW a b, Cost.crossings_append]

/-- ⚠ **The total-state model grounds every transition whatsoever** — which is
the honest content of the repair. Transported into `totalModel`, a `Cost` floor
is neither strengthened nor weakened, because `totalModel` is the model that
believes every step. The repair is not "live floors are harder"; it is "the model
is now a parameter you must supply, and a *causal* model refuses what this one
accepts" — §4 witness 2. -/
def totalGrounds {S : Type u} {Op : Type w} (step : S → Op → S) :
    Grounds (totalModel step) step where
  lift := step
  steps := fun _ _ => rfl
  observes := fun _ _ => rfl

/-- The same, as the statement it is: no transition is refused here. -/
theorem totalModel_grounds_everything {S : Type u} {Op : Type w}
    (step : S → Op → S) : Groundable (totalModel step) step :=
  ⟨totalGrounds step⟩

/-- An op stream as an execution of the total-state model. -/
def pathOfOps {S : Type u} {Op : Type w} (step : S → Op → S) (s : S)
    (os : List Op) : Path (totalModel step) s ((totalGrounds step).runW s os) :=
  (totalGrounds step).path s os

/-- **The old cost IS a path cost.** `Cost.crossings` of a stream equals
`Path.crossings` of the execution the total-state model performs for it. -/
theorem pathOfOps_crossings {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] (step : S → Op → S) (σ : S → Seg) (s : S) (os : List Op) :
    (pathOfOps step s os).crossings σ = Cost.crossings σ step s os :=
  (totalGrounds step).path_crossings σ s os

/-- **Every `Budget.Workload` is a `LiveWorkload` of the total-state model** —
the old theory exhibited as a special case, not merely claimed to be one. -/
def liveOfWorkload {S : Type u} {Op : Type w} [MergeState S]
    (wl : Budget.Workload S Op) : LiveWorkload (totalModel wl.step) where
  I := wl.I
  start := wl.start
  stop := (totalGrounds wl.step).runW wl.start wl.ops
  path := pathOfOps wl.step wl.start wl.ops
  legal := ((totalGrounds wl.step).path_legal wl.I wl.start wl.ops).mpr wl.legal

/-- …and every old plan's achieved cost is that live workload's cost, on the
nose. Nothing is re-priced by the repair. -/
theorem liveOfWorkload_cost {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] (wl : Budget.Workload S Op)
    (τ : Strategy wl.I Seg) :
    (liveOfWorkload wl).cost τ = Cost.crossings τ.seam wl.step wl.start wl.ops :=
  pathOfOps_crossings wl.step τ.seam wl.start wl.ops

/-! ### (b) The causal adapter — `CausalReach`'s cuts as worlds

Worlds are **downward-closed cuts** of a `FinHistory`, and a step *delivers* one
op the cut did not already hold. So a world is a causal state by construction,
and `observe` is the cut's interpretation — no state that no cut produces can
appear anywhere in this model. That single fact is what refuses the `Bounds`
defect in §4. -/

/-- **The causal execution model.** `World := Cut H` — downward-closure is a
field of the world, so it cannot be skipped — and `Step c o c'` says `c'` is `c`
with `o` delivered, an op `c` did not already hold. -/
def causalModel {Op σ : Type} [DecidableEq Op] (H : CausalReach.FinHistory Op)
    (interp : CausalReach.Cut H → σ) : RunModel σ Op where
  World := CausalReach.Cut H
  observe := interp
  Step := fun c o c' => c.mem o = false ∧ ∀ p, c'.mem p = (c.mem p || decide (p = o))

/-- **A causal model observes only states some cut interprets to.** The one-line
theorem the whole §4 refusal rests on: `observe` *is* `interp`, so a state
outside `interp`'s image is outside every world of the model. -/
theorem causalModel_observes_a_cut {Op σ : Type} [DecidableEq Op]
    {H : CausalReach.FinHistory Op} {interp : CausalReach.Cut H → σ} {s : σ}
    (h : ∃ v : (causalModel H interp).World, (causalModel H interp).observe v = s) :
    ∃ c : CausalReach.Cut H, interp c = s := h

/-! ### (c) The `Necessity.Impl` adapter — a reachable clash IS a live fork -/

/-- **A coordination-free implementation as a model.** Worlds are states,
`observe` is the identity, and a step is a *successful local commit*: `tryApply`
returning `some`. An aborted op is not a step, which is the difference from
`totalModel`. -/
def implModel {S : Type u} {Op : Type w} (impl : Necessity.Impl S Op) :
    RunModel S Op where
  World := S
  observe := id
  Step := fun s o s' => impl.tryApply o s = some s'

/-- A successful `Necessity` run is an execution of `implModel`. -/
theorem pathOfRunsTo {S : Type u} {Op : Type w} (impl : Necessity.Impl S Op) :
    ∀ (base s : S) (ops : List Op), Necessity.RunsTo impl base s ops →
      Nonempty (Path (implModel impl) base s) := by
  intro base s ops
  induction ops generalizing base with
  | nil =>
      intro h
      have h0 : (some base : Option S) = some s := h
      have hb : base = s := Option.some.inj h0
      subst hb
      exact ⟨Path.nil (P := implModel impl) base⟩
  | cons o ops ih =>
      intro h
      have h2 : Necessity.run impl base (o :: ops) = some s := h
      cases htry : impl.tryApply o base with
      | none =>
          rw [Necessity.run_cons_none impl base o ops htry] at h2
          exact absurd h2 (by simp)
      | some b =>
          rw [Necessity.run_cons_some impl base o ops htry] at h2
          obtain ⟨t⟩ := ih b h2
          exact ⟨Path.cons (P := implModel impl) base b o htry t⟩

/-- **`Necessity.ReachableClash` is a `LiveFork`.** The modal model's own
reachability notion — two successful local runs from a common legal ancestor — is
an instance of the abstract fork, so the abstraction subsumes it rather than
competing with it. -/
theorem reachableClash_is_a_live_fork {S : Type u} {Op : Type w} [MergeState S]
    {impl : Necessity.Impl S Op} {I : Invariant S}
    (c : Necessity.ReachableClash impl I) :
    Nonempty (LiveFork (implModel impl) I) := by
  obtain ⟨px⟩ := pathOfRunsTo impl c.base c.x c.opsx c.hx_run
  obtain ⟨py⟩ := pathOfRunsTo impl c.base c.y c.opsy c.hy_run
  exact ⟨⟨c.base, c.x, c.y, px, py, c.hx, c.hy, c.hbad⟩⟩

/-- …and it is charged: every valid seam pays at least one crossing across the
two branches of a reachable clash. `Bounds.reachable_clash_costs_the_session`,
re-derived at the abstract model. -/
theorem reachableClash_charges {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {impl : Necessity.Impl S Op}
    {I : Invariant S} {σ : S → Seg} (hseg : SegmentedIConfluent σ I)
    (c : Necessity.ReachableClash impl I) :
    ∃ F : LiveFork (implModel impl) I, 0 < F.px.crossings σ + F.py.crossings σ := by
  obtain ⟨F⟩ := reachableClash_is_a_live_fork c
  exact ⟨F, F.charges hseg⟩

/-! ## §4. THE SEPARATION — three witnesses -/

/-! ### Witness 1 — the tag-scoped OR-Set clash is LIVE

`CausalReach` §2 proves the catalog clash jointly reachable under tag-scoped
rem-after-add. Here it is more than joint: the two clash states are the endpoints
of two **delivery paths out of one common ancestor cut** — the cut holding both
adds and neither remove. -/

/-- The tag-scoped OR-Set delivery model. -/
def or4Model : RunModel (ORSet.ORSet Nat Nat) CausalReach.OR4 :=
  causalModel CausalReach.or4H CausalReach.or4Interp

/-- The common ancestor's membership: both adds delivered, neither remove. -/
def memAdds : CausalReach.OR4 → Bool
  | .a1 | .a2 => true
  | .r1 | .r2 => false

/-- …and it is a cut: nothing below a delivered op is missing. -/
def cutAdds : CausalReach.Cut CausalReach.or4H where
  mem := memAdds
  down := by intro a b hm hh; revert hm hh; cases a <;> cases b <;> decide

/-- Delivering `r2` at the ancestor gives `CausalReach.cutX` — a real step of the
model. -/
theorem step_to_cutX :
    or4Model.Step cutAdds CausalReach.OR4.r2 CausalReach.cutX :=
  ⟨rfl, fun p => by cases p <;> rfl⟩

/-- Delivering `r1` at the ancestor gives `CausalReach.cutY`. -/
theorem step_to_cutY :
    or4Model.Step cutAdds CausalReach.OR4.r1 CausalReach.cutY :=
  ⟨rfl, fun p => by cases p <;> rfl⟩

/-- **The fork.** One ancestor cut, two single-delivery executions, two legal
presence states whose merge holds nothing — `CausalReach.orset_clash_present`,
now carried by paths. -/
def orsetFork :
    LiveFork or4Model (fun s : ORSet.ORSet Nat Nat => ORSet.Present s 0) where
  base := cutAdds
  x := CausalReach.cutX
  y := CausalReach.cutY
  px := Path.cons (P := or4Model) cutAdds CausalReach.cutX CausalReach.OR4.r2
          step_to_cutX (Path.nil (P := or4Model) CausalReach.cutX)
  py := Path.cons (P := or4Model) cutAdds CausalReach.cutY CausalReach.OR4.r1
          step_to_cutY (Path.nil (P := or4Model) CausalReach.cutY)
  hx := CausalReach.orset_clash_present.1
  hy := CausalReach.orset_clash_present.2.1
  hbad := CausalReach.orset_clash_present.2.2

/-- ⚠ **WITNESS 1 — the tag-scoped clash produces a LIVE bound.** Under every
valid seam for presence, at every segment type in every universe, the two
delivery branches together cost at least one coordination event; the two states
they reach are `CausalReach.orClashL` and `orClashR` on the nose; and those are
the interpretations of two real cuts of the tag-scoped history
(`CausalReach.orset_clash_joint`).

This is what a live bound looks like: the charge is attached to an execution, and
the execution is exhibited. -/
theorem orset_tag_scoped_clash_is_live :
    (∀ {Seg : Type v} [DecidableEq Seg] (σ : ORSet.ORSet Nat Nat → Seg),
        SegmentedIConfluent σ (fun s : ORSet.ORSet Nat Nat => ORSet.Present s 0) →
        0 < orsetFork.px.crossings σ + orsetFork.py.crossings σ)
      ∧ or4Model.observe orsetFork.x = CausalReach.orClashL
      ∧ or4Model.observe orsetFork.y = CausalReach.orClashR
      ∧ CausalReach.Joint CausalReach.or4H CausalReach.or4Interp
          CausalReach.orClashL CausalReach.orClashR :=
  ⟨fun _ hseg => orsetFork.charges hseg, rfl, rfl, CausalReach.orset_clash_joint⟩

/-- **The live bound is a number, not an empty quantifier.** At the identity seam
— always valid (`Bounds.id_segmented`), through the classical decidable equality
`Bounds.orsetDecEq`, used only to instantiate — the fork's two branches cost at
least one crossing between them. -/
theorem orset_live_bound_inhabited :
    0 < @Path.crossings (ORSet.ORSet Nat Nat) (ORSet.ORSet Nat Nat) CausalReach.OR4
          Bounds.orsetDecEq or4Model id _ _ orsetFork.px
      + @Path.crossings (ORSet.ORSet Nat Nat) (ORSet.ORSet Nat Nat) CausalReach.OR4
          Bounds.orsetDecEq or4Model id _ _ orsetFork.py :=
  @LiveFork.charges (ORSet.ORSet Nat Nat) (ORSet.ORSet Nat Nat) CausalReach.OR4 _
    Bounds.orsetDecEq or4Model _ orsetFork id (Bounds.id_segmented _)

/-! ### Witness 2 — the element-wide pair is REFUSED

`Bounds.ew_rejected_at_zero_over_unreachable_pair` is the defect: a hard refusal
of every plan, justified by a clash between two states no cut of the element-wide
history reaches. Here the same pair cannot be accused at all. -/

/-- The element-wide OR-Set delivery model. -/
def ewModel : RunModel (ORSet.ORSet Nat Nat) CausalReach.OR4 :=
  causalModel CausalReach.ewH CausalReach.ewInterp

/-- No world of the element-wide model observes the left clash state —
`CausalReach.ew_clashL_unreachable`, read through `observe`. -/
theorem ewModel_never_observes_L :
    ¬ ∃ v : ewModel.World, ewModel.observe v = CausalReach.ewClashL :=
  CausalReach.ew_clashL_unreachable

/-- Nor the right one. -/
theorem ewModel_never_observes_R :
    ¬ ∃ v : ewModel.World, ewModel.observe v = CausalReach.ewClashR :=
  CausalReach.ew_clashR_unreachable

/-- The empty cut — so the model has worlds at all, and the refusal below is
about an unreachable *state* rather than an empty model. -/
def ewEmptyCut : CausalReach.Cut CausalReach.ewH where
  mem := fun _ => false
  down := by intro a b hm _; exact Bool.noConfusion hm

/-- **The general refusal.** A transition whose value at some world is a state no
world observes cannot be grounded in that model. One line, and it is the whole
mechanism by which a model refuses a teleport. -/
theorem not_grounded_of_unobserved {S : Type u} {Op : Type w} {P : RunModel S Op}
    {step : S → Op → S} (a : P.World) (o : Op)
    (h : ¬ ∃ v : P.World, P.observe v = step (P.observe a) o) :
    ¬ Groundable P step :=
  fun ⟨G⟩ => h ⟨G.lift a o, G.observes a o⟩

/-- `Bounds.ewStep` re-alphabeted to the causal model's op type. It ignores its
op — `ewTeleport_is_ewStep` proves the two are the same transition — so the only
difference is which alphabet the model's `Step` relation is indexed by, and the
causal model's is the history's. -/
def ewTeleport : ORSet.ORSet Nat Nat → CausalReach.OR4 → ORSet.ORSet Nat Nat :=
  fun _ _ => CausalReach.ewClashL

/-- The re-alphabeting is not a change of transition. -/
theorem ewTeleport_is_ewStep (s : ORSet.ORSet Nat Nat) (o : CausalReach.OR4) :
    ewTeleport s o = Bounds.ewStep s () := rfl

/-- ⚠ **The teleport is not grounded in the causal model.** It takes *every*
state to `ewClashL`; a grounding would therefore have to exhibit a world
observing `ewClashL`, and there is none. So §5's transport does not apply to it —
which is the precise sense in which the defect is refused rather than patched. -/
theorem ewTeleport_not_grounded : ¬ Groundable ewModel ewTeleport :=
  not_grounded_of_unobserved (P := ewModel) ewEmptyCut CausalReach.OR4.a1
    ewModel_never_observes_L

/-- ⚠ **WITNESS 2 — THE REFUSAL.** In the element-wide causal model:

  1. no clash carving, of any execution, accuses the pair — because a carving's
     accused worlds are worlds, and no world observes either state;
  2. no live fork accuses it either;
  3. the teleport that produced the defect is not grounded, so §5's transport
     cannot carry the old floor across;
  4. and yet `Budget.ForcedFloor Bounds.ewWorkload 1` **still holds** — the old
     floor is a true theorem about the `step` it was handed, and
     `Bounds.ew_rejected_at_zero_over_unreachable_pair` still turns it into "no
     plan fits, in any universe".

Conjuncts 1–3 against conjunct 4 are the separation. The defect was never a false
theorem; it was a floor with nowhere to record which executions produce its
accused pair. Now there is a place, and this pair cannot fill it. -/
theorem ew_pair_refuses_a_live_accusation :
    (∀ (I : Invariant (ORSet.ORSet Nat Nat)) (a b : ewModel.World)
        (ch : ClashChain (P := ewModel) I a b) (x y : ewModel.World),
        ch.Accuses x y →
        ¬ (ewModel.observe x = CausalReach.ewClashR
            ∧ ewModel.observe y = CausalReach.ewClashL))
      ∧ (∀ (I : Invariant (ORSet.ORSet Nat Nat)) (F : LiveFork ewModel I),
          ¬ (ewModel.observe F.x = CausalReach.ewClashL
              ∧ ewModel.observe F.y = CausalReach.ewClashR))
      ∧ ¬ Groundable ewModel ewTeleport
      ∧ Budget.ForcedFloor Bounds.ewWorkload 1 := by
  refine ⟨?_, ?_, ewTeleport_not_grounded, Bounds.ew_forced_floor_one⟩
  · intro I a b ch x y _ hobs
    exact ewModel_never_observes_L ⟨y, hobs.2⟩
  · intro I F hobs
    exact ewModel_never_observes_L ⟨F.x, hobs.1⟩

/-! ### Witness 3 — the old lattice workload keeps its carrier-global bound -/

/-- `Cost.lean` §6's budget workload as a live workload of the total-state
model. -/
def budgetLive : LiveWorkload (totalModel (Cost.reallocStep 10)) :=
  liveOfWorkload Budget.budgetWorkload

/-- Its execution's clash carving: `Cost.budget_clashBlocks`, transported by the
total grounding. -/
def budgetLiveChain :
    ClashChain (P := totalModel (Cost.reallocStep 10)) (BudgetInv 10)
      Cost.budgetStart
      ((totalGrounds (Cost.reallocStep 10)).runBlocks Cost.budgetStart
        Cost.budgetBlocks) :=
  (totalGrounds (Cost.reallocStep 10)).chain (BudgetInv 10) Cost.budgetStart
    Cost.budgetBlocks Cost.budget_clashBlocks

/-- …and it carves the workload's own execution, into three blocks. -/
theorem budgetLive_forced_three : LiveForcedFloor budgetLive 3 :=
  ⟨budgetLiveChain, rfl, rfl⟩

/-- **WITNESS 3 — the repair costs the old results nothing.** Three re-divisions
of a shared budget still force three coordination events under **every** valid
seam, at every segment type in every universe (first conjunct) — and the live
crossing count is the old crossing count, seam by seam (second). -/
theorem budget_live_floor_is_three :
    (∀ {Seg : Type v} [DecidableEq Seg] (τ : Strategy (BudgetInv 10) Seg),
        3 ≤ budgetLive.cost τ)
      ∧ ∀ {Seg : Type v} [DecidableEq Seg] (σ : QuotaState → Seg),
          budgetLive.path.crossings σ
            = Cost.crossings σ (Cost.reallocStep 10) Cost.budgetStart Cost.budgetW :=
  ⟨fun τ => budgetLive_forced_three.le_cost τ,
   fun σ => pathOfOps_crossings (Cost.reallocStep 10) σ Cost.budgetStart Cost.budgetW⟩

/-! ## §5. THE TRANSPORT THEOREM — exactly when an old bound becomes a live one -/

/-- ⚠ **THE TRANSPORT THEOREM.** Exactly when an old `Cost` bound becomes a live
one.

  * **Source judgement** — `Cost.ClashBlocks I step (P.observe a) bs`: a block
    decomposition of an op stream under a total transition, with no history.
  * **Target judgement** — `G.chain I a bs h`, a `ClashChain` of the model with
    the same length, whose every block is an execution of `P`, whose flattened
    cost is the old crossing count, whose length therefore lower-bounds that cost
    under every valid seam, and whose every accused pair is joined by a path.
  * **Load-bearing hypothesis** — `Grounds P step`: the model performs `step` at
    every world, observing exactly what `step` computes. Without it the transport
    is not merely unproved — the source judgement holds and the target object
    cannot exist.
  * **Counterexample without it** — the teleport of `Bounds` §7 in `ewModel`.
    `Bounds.ew_teleport_clashBlocks` is a genuine source judgement and
    `Bounds.ew_forced_floor_one` a genuine `ForcedFloor`, while
    `ewTeleport_not_grounded` refutes the hypothesis and
    `ew_pair_refuses_a_live_accusation` shows no target object exists in that
    model at all.

⚠ And the honest reading of the hypothesis: `totalModel` grounds every `step`
(`totalGrounds`, `totalModel_grounds_everything`), so transporting into it is
free and buys nothing. The hypothesis has teeth only against a model that
refuses transitions — which is what a causal model does, and which is now the
modeller's declared choice rather than an unstated one. -/
theorem cost_floor_becomes_live {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} {step : S → Op → S}
    {I : Invariant S} {σ : S → Seg} (hseg : SegmentedIConfluent σ I)
    (G : Grounds P step) (a : P.World) (bs : List (List Op))
    (h : Cost.ClashBlocks I step (P.observe a) bs) :
    (G.chain I a bs h).length = bs.length
      ∧ ((G.chain I a bs h).flatten).crossings σ
          = Cost.crossings σ step (P.observe a) bs.flatten
      ∧ bs.length ≤ ((G.chain I a bs h).flatten).crossings σ
      ∧ ∀ x y : P.World, (G.chain I a bs h).Accuses x y → Nonempty (Path P x y) := by
  refine ⟨G.chain_length I a bs h, G.chain_crossings I σ a bs h, ?_, ?_⟩
  · have hlen := G.chain_length I a bs h
    have hb := ClashChain.length_le_crossings (σ := σ) hseg (G.chain I a bs h)
    omega
  · intro x y hacc
    exact (ClashChain.accused_are_connected (G.chain I a bs h) hacc).1

/-! ## §6. Profiles survive unchanged

`CoordEffect` composes cost profiles pointwise over `Strategy → Nat` and defers
minimization. Nothing in that construction reads where a trajectory came from, so
all of it applies to path costs verbatim — `Profile`, `⊗`, `optimum`,
`Admissible` and `Strategy` are the sibling file's, used and not redefined. -/

/-- **A path's cost profile**: `Path.crossings` as a function of the session's
strategy. `CoordEffect.streamProfile`, with the stream replaced by an
execution. -/
def pathProfile {S : Type u} {Seg : Type v} {Op : Type w} [MergeState S]
    [DecidableEq Seg] {P : RunModel S Op} (I : Invariant S) {a b : P.World}
    (p : Path P a b) : Profile (Strategy I Seg) :=
  fun τ => p.crossings τ.seam

@[simp] theorem pathProfile_apply {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} (I : Invariant S)
    {a b : P.World} (p : Path P a b) (τ : Strategy I Seg) :
    pathProfile (Seg := Seg) I p τ = p.crossings τ.seam := rfl

/-- **A live forced floor lower-bounds the profile's minimum** —
`CoordEffect.forced_le_optimum` over paths, by the same one-liner: the floor
holds at every admissible strategy pointwise. -/
theorem live_forced_le_optimum {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} {wl : LiveWorkload P}
    {n : Nat} (h : LiveForcedFloor wl n) (A : Admissible (Strategy wl.I Seg)) :
    n ≤ optimum A (pathProfile wl.I wl.path) :=
  le_optimum (fun τ _ => h.le_cost τ)

/-- **A live fork's charge survives minimization too** — over every admissible
space, at every segment type, in every universe.
`Bounds.reachable_clash_floor_le_session_optimum`, at the abstract model. -/
theorem live_fork_le_optimum {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {P : RunModel S Op} {I : Invariant S}
    (F : LiveFork P I) (A : Admissible (Strategy I Seg)) :
    1 ≤ optimum A (pathProfile I F.px ⊗ pathProfile I F.py) :=
  le_optimum (fun τ _ => F.charges τ.valid)

/-- The OR-Set fork as a session budget: at least one coordination event, over
every admissible catalogue of seams. Witness 1 in profile form — the same number,
through the sibling file's machinery, unmodified. -/
theorem orset_session_floor {Seg : Type v} [DecidableEq Seg]
    (A : Admissible
      (Strategy (fun s : ORSet.ORSet Nat Nat => ORSet.Present s 0) Seg)) :
    1 ≤ optimum A
        (pathProfile (fun s : ORSet.ORSet Nat Nat => ORSet.Present s 0) orsetFork.px
          ⊗ pathProfile (fun s : ORSet.ORSet Nat Nat => ORSet.Present s 0)
              orsetFork.py) :=
  live_fork_le_optimum orsetFork A

/-! ## §7. The readings, side by side -/

/-- **Old and live agree where the model believes everything**: the budget
workload's live cost is its old cost, seam by seam. -/
example : ∀ {Seg : Type} [DecidableEq Seg] (σ : QuotaState → Seg),
    budgetLive.path.crossings σ
      = Cost.crossings σ (Cost.reallocStep 10) Cost.budgetStart Cost.budgetW :=
  fun σ => budget_live_floor_is_three.2 σ

/-- **The live floor of the budget workload is three**, under every strategy. -/
example {Seg : Type} [DecidableEq Seg] (τ : Strategy (BudgetInv 10) Seg) :
    3 ≤ budgetLive.cost τ :=
  budget_live_floor_is_three.1 τ

/-- **And the pair `Bounds` charges for cannot be charged for here.** -/
example : ¬ Groundable ewModel ewTeleport :=
  ew_pair_refuses_a_live_accusation.2.2.1

end Uwueave.LiveCost
