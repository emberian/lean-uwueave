/-
# Uwueave.Exits — the menu: which exits a clash leaves open, and what each costs.

`Verdict.clash` (`Spec.lean`) tells a schema author that coordination is needed;
`SegVerdict` tells them *where*; `Cost.lean` tells them *how often*. None of
them tells them **what their options are**. This file does.

## The gap, as an external reviewer named it

codex, reviewing this tree against LoRe (Haas, Mogk, Yanakieva, Bieniusa,
Mezini — *"LoRe: A Programming Model for Verifiably Safe Local-First
Software"*, arXiv:2304.07133v2), put the difference plainly: **LoRe is a design
assistant** — it takes an unsafe program and *inserts* the coordination that
makes it safe, so the developer never has to know what a token or a lock is.
**We are a judgement engine** — we take an invariant and report a verdict with
evidence, and then stop. A verdict that says "escalates" and stops is the
distributed-systems equivalent of a type error with no suggested fix.

The prescription this file executes is codex's: a clash should return not just
"escalates" but **the minimal exits, with their prices**. The point of the
exercise is that *every exit was already proved somewhere in this tree*; nobody
had assembled them into a menu, so no caller could see them together, and no
caller could see that **different clashes leave different exits open**.

## The eight currencies

An exit is a way of *not paying* for a clash in full-coordination coin. Each
one buys coordination-freedom with something else:

| exit               | what it spends                                            |
|--------------------|-----------------------------------------------------------|
| `escrow`           | some state that was legal stops being reachable            |
| `seam`             | meetings, but only at `σ`-changes                          |
| `arbitration`      | the merge stops being a join (an exogenous verdict lands)  |
| `strongerMetadata` | states become unrepresentable in the richer carrier        |
| `weakenedInvariant`| the invariant stops saying what you wanted                 |
| `exposedFork`      | the result type — plurality becomes the caller's problem   |
| `rollback`         | at least one replica's contribution is dropped             |
| `fullCoordination` | meetings, one per op                                       |

Each price is a **theorem**, named at the constructor and again at the exit's
price. A number with no theorem would be a lie here: `Exit.price` is a `Nat`
and the theorems in §4 are what make the `Nat` mean something.

## What a menu does NOT do — ⟨UNDONE⟩, and it is the biggest gap

**A menu is not a solver.** It reports that a `seam` exit exists *for a `σ` you
hand it*, and that an `escrow` exit exists *for a split you hand it*. It does
not **synthesize** the `σ`, and it does not **synthesize** the escrow's quota
partition. That is a search problem over projections of the state space, and
nothing here searches. LoRe does not synthesize these either — it inserts
coordination from a fixed repertoire — so this gap is not a gap against the
prior art; it is the next thing to build, and it is named ⟨UNDONE⟩ rather than
paved over. Concretely, what is missing is a function

    synth : (I : Invariant S) → Option (Σ Seg, {σ : S → Seg // SegmentedIConfluent σ I})

that is not `fun _ => none` and not `fun _ => some ⟨S, id, identity_seam_segmented⟩`
— i.e. one that finds a *non-trivial* seam. The second trivial inhabitant is
constructed below (`identity_seam_segmented`, and `fullCoordination_has_a_seam`
is it wearing the exit's name), which is exactly why the interesting statement
is about non-triviality and why nothing here proves it.

Four further non-claims, labelled:

  * ⟨UNDONE⟩ **The menu is not proved exhaustive.** `menu_sound` says every
    *listed* exit applies. Nothing says an unlisted exit does not — except
    where a named refutation says so (`pin_escrow_starves`,
    `balance_total_not_a_seam`, `duel_escrow_starves`). An absent row means
    "nobody proved it", not "impossible".
  * ⟨UNDONE⟩ **`Exit.seam`'s `floor` field is free data.** `Applies` certifies
    the *seam*; it does not certify the *number*. `seam_price_is_forced` is the
    theorem that makes a floor honest, and each worked menu with a seam entry
    discharges it separately (`ceiling_seam_floor_is_zero`). Nothing in the type
    forces that discharge, and that is a hole in the type, not in the proofs.
  * ⟨scope⟩ **Two prices are in different currencies.** `seam` and
    `fullCoordination` are priced in `Cost.crossings` — meetings, with a floor
    theorem. `arbitration` and `rollback` are priced `0` because no *meeting
    between replicas* is needed (the verdict is computed locally from the merged
    state), and their real price is paid in §4's two price theorems and in
    `GatedEra.ge_not_antitone`, not in crossings. Reading the two `0`s as the
    same `0` is the mistake this note exists to prevent.
  * ⟨scope⟩ **Everything is at `Type`.** Every carrier in this tree is `Type 0`
    (`GSet Nat`, `QuotaState`, `GrantSet`); universe-polymorphic exits would buy
    nothing and cost every statement a binder. `Cost.coordination_forced` is
    universe-polymorphic and is instantiated here at level 0.

## What the tree already proved, and where it lives

Nothing in §1–§3 is new mathematics. The exits are:

  * `escrow` — `Catalog.escrow_local_bound_iconfluent` (Balegas et al.'s bounded
    counter, as this tree states it).
  * `seam` — `Segmented.SegmentedIConfluent` (Whittaker–Hellerstein, VLDB'19),
    with `Seams.lean`'s three instances and `SeamAlgebra.linked_segmented` for
    when two exits share one meeting.
  * `arbitration` — `Era.lean` / `GatedEra.lean` (Dougal, PaPoC'26), whose
    price is `GatedEra.ge_not_antitone`: arbitration buys a live op feed and
    loses `Gated.gated_antitone`'s shrinkage.
  * `exposedFork` — `MVRegister.lean` (keep both writes, surface the conflict).
    The stance has a name in the literature: Schiefer, Litt and Jackson,
    *"Merge What You Can, Fork What You Can't: Managing Data Integrity in
    Local-First Software"* (MIT CSAIL, 2022; PDF in `paperbin/uweave/`).
  * `rollback` — ERA's pending epoch: `GatedEra.ge_duel_arbiter_flips` is the
    live witness that a permitted op becomes denied when a later cut lands.
  * `fullCoordination` — the top, and `identity_seam_segmented` proves it is
    always available (σ = id is always a valid seam).
  * `Ancestral.clash_dichotomy` — the test that decides whether the
    ancestor-reading exit is live at all: **resurrection** (some serialization of
    the two operations is legal) versus **accumulation** (none is, and by
    `serialization_clash_defeats_every_merge` no effect-faithful merge helps).
  * `Cost.coordination_forced` — the floor under every seam price.

⚠ **A correction to the brief this file was written from.** The brief said
"escrow/LCA applies only to RESURRECTION clashes, never accumulation". The tree
says the opposite for escrow, and says it in `Ancestral.clash_dichotomy`'s own
docstring: the resurrection branch is where *the ancestor-reading merge* is the
fix, and the accumulation branch is where "escrow or coordinate" is all that is
left (`Ancestral.budget_defeats_every_faithful_merge` names escrow explicitly as
what survives there). So escrow and stronger-metadata sit on **opposite** branches
of the dichotomy, and `ancestral_exit_discriminates` below proves the
stronger-metadata half in both directions. What escrow actually keys on is a
second axis — **divisibility** — and the worked menus exhibit it: the balance
clash and the pin ceiling are *both* accumulation, and escrow takes one and not
the other, because a bound of 10 splits into 5+5 and a bound of 1 does not split
at all without starving a slot (`pin_escrow_zero_quota`).
-/
import Uwueave.Spec
import Uwueave.Ceiling
import Uwueave.Cost
import Uwueave.GatedEra
import Uwueave.Ancestral
import Uwueave.JoinHom

namespace Uwueave.Exits

open Uwueave Uwueave.Catalog Uwueave.Segmented
open scoped Uwueave.JoinHom

/-! ## §1. The eight exits

An `Exit S` is a *proposal*: a way out of a clash on the carrier `S`, carrying
whatever data the proposal needs to be checked. Whether the proposal is
available for a particular invariant is `Exit.Applies` (§2); what it costs is
`Exit.price` (§3); why the price is that number is §4. -/

/-- **The eight exits a clash leaves open.** Each constructor carries the data
its availability check needs, and nothing more:

  * `escrow ι q obs` — a per-replica split: an index type `ι`, a quota `q`, and
    the observation `obs` that reads each replica's charge off the state.
  * `seam Seg σ floor` — a projection `σ` replicas hold fixed between
    coordination events, and the number of meetings the workload forces.
    ⚠ `floor` is free data; `seam_price_is_forced` is what makes it honest.
  * `arbitration verdict` — an exogenous canonicalisation: whatever two legal
    replicas merged to, `verdict` maps it to something legal.
  * `strongerMetadata T instT π` — a richer carrier `T` that projects onto `S`.
  * `weakenedInvariant J` — give up and assert less.
  * `exposedFork` — keep both replicas as branches; stop merging.
  * `rollback keep` — arbitration constrained to *discard only* (`keep s ⊑ s`).
  * `fullCoordination workload` — meet on every op. -/
inductive Exit (S : Type) [MergeState S] : Type 1 where
  /-- Pre-partition the bound: index type, quota, and the per-replica charge. -/
  | escrow (ι : Type) (q : ι → Nat) (obs : S → Escrow ι)
  /-- Coordinate only where `σ` changes; `floor` is the forced meeting count. -/
  | seam (Seg : Type) (σ : S → Seg) (floor : Nat)
  /-- An exogenous verdict repairs the merge. -/
  | arbitration (verdict : S → S)
  /-- A richer carrier, projecting onto this one. -/
  | strongerMetadata (T : Type) (instT : MergeState T) (π : T → S)
  /-- Assert less. -/
  | weakenedInvariant (J : Invariant S)
  /-- Keep both; the caller resolves. -/
  | exposedFork
  /-- Discard back to something legal. -/
  | rollback (keep : S → S)
  /-- Meet on every op of a `workload`-long stream. -/
  | fullCoordination (workload : Nat)

/-! ## §2. Availability — when is this exit open for this clash?

`Applies` is the checkable content of an exit. Every clause is a proposition
about `I` and the exit's own data, and every one of them is discharged by a
theorem already in this tree at the worked menus of §6. -/

/-- **When an exit is available.** Read clause by clause:

  * `escrow` — the charge is a join-homomorphism into the escrow lattice
    (so quotas survive gossip), staying inside quota keeps the invariant, and
    every index gets a *positive* share. The third clause is what stops
    "escrow" from naming a lease that starves every replica but one, and it is
    what `pin_escrow_starves` refutes for the uniqueness ceiling.
  * `seam` — `Segmented.SegmentedIConfluent`, verbatim.
  * `arbitration` — whatever two legal replicas merge to, the verdict is legal.
    Note what is *not* required: that the verdict agree with either replica.
  * `strongerMetadata` — `π` is a join-homomorphism and the pulled-back
    invariant is I-confluent upstairs.
  * `weakenedInvariant` — `J` is I-confluent and `I` entails it.
  * `exposedFork` — the branch lattice's "every branch is legal" invariant is
    I-confluent. Unconditional, but **not** `True`: the row carries
    `branches_iconfluent`, so nothing is discharged over an empty premise.
  * `rollback` — `keep` only ever discards (`keep s ⊑ s`) and lands legal.
  * `fullCoordination` — `σ = id` is a valid seam. Unconditional, and again not
    `True`: the row carries `identity_seam_segmented`.

The last two are the ones to watch. An exit that always applies is exactly the
shape that goes vacuous if its availability check is a constant, so both are
stated as the theorem they stand on and neither is inhabited by `trivial`. -/
def Exit.Applies {S : Type} [MergeState S] : Exit S → Invariant S → Prop
  | .escrow _ q obs, I =>
      (∀ x y : S, obs (x ⊔ y) = obs x ⊔ obs y)
      ∧ (∀ s : S, (∀ i, obs s i ≤ q i) → I s)
      ∧ (∀ i, 0 < q i)
  | .seam _ σ _, I => SegmentedIConfluent σ I
  | .arbitration verdict, I => ∀ x y : S, I x → I y → I (verdict (x ⊔ y))
  | .strongerMetadata T instT π, I =>
      (∀ a b : T, π (@MergeState.merge T instT a b) = π a ⊔ π b)
      ∧ @IConfluent T instT (fun t => I (π t))
  | .weakenedInvariant J, I => IConfluent J ∧ (∀ s : S, I s → J s)
  | .exposedFork, I =>
      IConfluent (S := S → Prop) (fun bs => ∀ s, bs s → I s)
  | .rollback keep, I =>
      (∀ s : S, keep s ⊑ s) ∧ (∀ x y : S, I x → I y → I (keep (x ⊔ y)))
  | .fullCoordination _, I => SegmentedIConfluent (fun s : S => s) I

/-! ## §3. The price, in meetings

`Cost.crossings` counts the meetings a workload forces under a chosen seam. Six
of the eight exits are priced `0`. Four of those six are justified by *the same*
theorem — `zero_price_of_iconfluent`: an exit that restores global I-confluence
leaves a one-point seam, and a one-point seam costs nothing — and the remaining
two (`arbitration`, `rollback`) by a weaker statement in a different currency,
which the module docstring flags. -/

/-- **The price of an exit, in meetings.** ⚠ The two `0`s at `arbitration` and
`rollback` are not the same `0` as the other four: see §4.5 and the module
docstring's ⟨scope⟩ note. -/
def Exit.price {S : Type} [MergeState S] : Exit S → Nat
  | .escrow .. => 0
  | .seam _ _ floor => floor
  | .arbitration _ => 0
  | .strongerMetadata .. => 0
  | .weakenedInvariant _ => 0
  | .exposedFork => 0
  | .rollback _ => 0
  | .fullCoordination n => n

@[simp] theorem price_seam {S : Type} [MergeState S] (Seg : Type) (σ : S → Seg)
    (n : Nat) : (Exit.seam (S := S) Seg σ n).price = n := rfl

@[simp] theorem price_fullCoordination {S : Type} [MergeState S] (n : Nat) :
    (Exit.fullCoordination (S := S) n).price = n := rfl

/-! ## §4. The prices, earned

### §4.1 The shared zero — a one-point seam costs nothing -/

/-- **A one-point seam is free on every workload.** With `σ` constant, no op can
move it, so `Cost.crossings` never increments. This is the arithmetic half of
every `price = 0` below. -/
theorem crossings_unit_seam_eq_zero {S Op : Type} (step : S → Op → S) :
    ∀ (s : S) (w : List Op), Cost.crossings (fun _ : S => ()) step s w = 0 := by
  intro s w
  induction w generalizing s with
  | nil => rfl
  | cons o w ih =>
      have hstep : Cost.crossings (fun _ : S => ()) step s (o :: w)
          = (if ((fun _ : S => ()) (step s o)) = ((fun _ : S => ()) s) then 0 else 1)
            + Cost.crossings (fun _ : S => ()) step (step s o) w := rfl
      rw [hstep, if_pos rfl, Nat.zero_add]
      exact ih (step s o)

/-- **Price zero, justified once.** An exit that hands back a *globally*
I-confluent invariant `J` has no seam to cross: `J` is segmented over the
one-point projection (`Segmented.iconfluent_iff_trivially_segmented`, the
conservativity half), and a one-point seam costs zero crossings on every
workload. Four of the six `0`-priced exits cite this theorem at their own `J`:
`escrow`, `strongerMetadata`, `weakenedInvariant`, `exposedFork`. -/
theorem zero_price_of_iconfluent {S : Type} [MergeState S] (J : Invariant S)
    (hJ : IConfluent J) :
    SegmentedIConfluent (S := S) (fun _ => ()) J
    ∧ ∀ {Op : Type} (step : S → Op → S) (s : S) (w : List Op),
        Cost.crossings (fun _ : S => ()) step s w = 0 :=
  ⟨(iconfluent_iff_trivially_segmented J).mp hJ,
   fun step s w => crossings_unit_seam_eq_zero step s w⟩

/-! ### §4.2 escrow — price 0, and the state it costs you -/

/-- **What an available escrow buys**: the per-quota invariant is I-confluent
(`Catalog.escrow_local_bound_iconfluent`, transported along the homomorphism
`obs`) and it entails `I`. So a replica that stays inside its share never needs
a meeting, and never breaks the invariant. -/
theorem escrow_strengthening_iconfluent {S : Type} [MergeState S] {I : Invariant S}
    {ι : Type} {q : ι → Nat} {obs : S → Escrow ι}
    (h : (Exit.escrow (S := S) ι q obs).Applies I) :
    IConfluent (fun s : S => ∀ i, obs s i ≤ q i)
      ∧ ∀ s : S, (∀ i, obs s i ≤ q i) → I s := by
  obtain ⟨hhom, hent, -⟩ := h
  refine ⟨?_, hent⟩
  intro x y hx hy i
  have hxy : obs (x ⊔ y) i = Nat.max (obs x i) (obs y i) := by rw [hhom]; rfl
  rw [hxy]
  exact Nat.max_le.mpr ⟨hx i, hy i⟩

/-- **The escrow exit costs zero meetings** — `zero_price_of_iconfluent` at the
per-quota invariant. This is the theorem the `0` in `Exit.price` cites. -/
theorem escrow_price_zero {S : Type} [MergeState S] {I : Invariant S}
    {ι : Type} {q : ι → Nat} {obs : S → Escrow ι}
    (h : (Exit.escrow (S := S) ι q obs).Applies I) :
    SegmentedIConfluent (S := S) (fun _ => ()) (fun s : S => ∀ i, obs s i ≤ q i)
    ∧ ∀ {Op : Type} (step : S → Op → S) (s : S) (w : List Op),
        Cost.crossings (fun _ : S => ()) step s w = 0 :=
  zero_price_of_iconfluent _ (escrow_strengthening_iconfluent h).1

/-- **⚠ The price: an escrow always forbids a state that was legal.** At a
clash pair, the two replicas cannot *both* be inside quota — if they were, the
homomorphism would put their merge inside quota too, and the entailment would
make the merge legal. So the pre-split necessarily rules out at least one legal
replica state: that is what "the whole budget on one device" stops being
reachable *means*, stated as a theorem instead of as a caveat. -/
theorem escrow_forbids_a_clash_replica {S : Type} [MergeState S] {I : Invariant S}
    {ι : Type} {q : ι → Nat} {obs : S → Escrow ι}
    (h : (Exit.escrow (S := S) ι q obs).Applies I)
    {x y : S} (hbad : ¬ I (x ⊔ y)) :
    ¬ ((∀ i, obs x i ≤ q i) ∧ (∀ i, obs y i ≤ q i)) := by
  rintro ⟨hx, hy⟩
  exact hbad ((escrow_strengthening_iconfluent h).2 _
    ((escrow_strengthening_iconfluent h).1 x y hx hy))

/-- The same fact from the other side, and the sharper reading: an escrow that
is **faithful** — one that leaves every legal state inside quota — *proves* the
invariant I-confluent. So for an invariant that genuinely clashes, no faithful
escrow exists, and every available escrow is unfaithful by construction. -/
theorem faithful_escrow_implies_iconfluent {S : Type} [MergeState S] {I : Invariant S}
    {ι : Type} {q : ι → Nat} {obs : S → Escrow ι}
    (h : (Exit.escrow (S := S) ι q obs).Applies I)
    (hfaith : ∀ s : S, I s → ∀ i, obs s i ≤ q i) : IConfluent I := by
  intro x y hx hy
  exact (escrow_strengthening_iconfluent h).2 _
    ((escrow_strengthening_iconfluent h).1 x y (hfaith x hx) (hfaith y hy))

/-! ### §4.3 seam — the floor is forced by the specification -/

/-- **The seam's price has a floor nobody can design around** —
`Cost.coordination_forced`, read as an exit price. A workload whose trajectory
contains `n` clash blocks costs at least `n` crossings under **this** seam; and
the cited theorem quantifies over every seam in every universe, so no
re-choice of `σ` goes lower. This is the theorem that makes a `seam` exit's
`floor` field honest — and it must be applied per menu, because the field
itself carries no proof. -/
theorem seam_price_is_forced {S Op : Type} [MergeState S] {I : Invariant S}
    {Seg : Type} [DecidableEq Seg] {σ : S → Seg} {step : S → Op → S} {s : S}
    {bs : List (List Op)} (hcl : Cost.ClashBlocks I step s bs)
    (h : (Exit.seam (S := S) Seg σ bs.length).Applies I) :
    (Exit.seam (S := S) Seg σ bs.length).price
      ≤ Cost.crossings σ step s bs.flatten := by
  show bs.length ≤ Cost.crossings σ step s bs.flatten
  exact Cost.coordination_forced hcl σ h

/-! ### §4.4 fullCoordination — always available, and the ceiling -/

/-- **The identity is always a valid seam.** Two replicas in the same fiber of
`σ = id` are the *same* replica, so the merge is idempotent and cannot leave the
fiber. This is why `fullCoordination` is unconditional: it is the seam exit at
its finest — one fiber per state, so every op that changes the state crosses —
and it always exists. -/
theorem identity_seam_segmented {S : Type} [MergeState S] (I : Invariant S) :
    SegmentedIConfluent (S := S) (fun s => s) I := by
  intro x y hσ hx _hy
  have hxy : x = y := hσ
  subst hxy
  exact ⟨by rw [merge_idem]; exact hx, merge_idem x⟩

/-- Full coordination *is* the seam exit at `σ = id` — the same availability
proof read through the other constructor, which is why the two rows never
disagree. -/
theorem fullCoordination_has_a_seam {S : Type} [MergeState S] (I : Invariant S)
    (n : Nat) : (Exit.seam (S := S) S (fun s => s) n).Applies I :=
  identity_seam_segmented I

/-- **The ceiling: no workload ever costs more than its length.** So
`fullCoordination w.length` is the top of the price order — the exit you can
always afford and never need to exceed (`Cost.crossings_le_length`). -/
theorem fullCoordination_is_the_ceiling {S Op : Type} [MergeState S]
    {Seg : Type} [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) (s : S)
    (w : List Op) :
    Cost.crossings σ step s w ≤ (Exit.fullCoordination (S := S) w.length).price :=
  Cost.crossings_le_length σ step s w

/-! ### §4.5 arbitration and rollback — a zero in a different currency

⚠ These two exits are priced `0` because **no meeting between replicas is
needed**: the verdict is a function of the state a replica already holds, so a
replica that has merged its peers' updates computes the answer alone. The
deployed instance of that claim is `GatedEra.ge_deterministic` — replicas with
the same event and cut *sets*, in any delivery order, with any duplication,
compute the same op feed. What these exits spend is not meetings, and the two
theorems below are the bill. -/

/-- The `0`, stated: an available arbitration repairs the merge of **any** two
legal replicas, with no hypothesis relating them — no meeting, no agreement
protocol, no waiting. (Formally this is `Applies` re-read and nothing more; its
content is in the hypothesis that is *absent*, and its force is
`GatedEra.ge_deterministic`, where replicas holding the same event and cut sets
— any order, any duplication — provably compute the same feed. That theorem is
the deployed form of this `0`, and it is not restated here.) -/
theorem arbitration_needs_no_meeting {S : Type} [MergeState S] {I : Invariant S}
    {verdict : S → S} (h : (Exit.arbitration (S := S) verdict).Applies I)
    (x y : S) (hx : I x) (hy : I y) : I (verdict (x ⊔ y)) := h x y hx hy

/-- **⚠ Price one: the arbiter overrides the merge.** At a clash, the verdict is
not the merged state — necessarily, since the merged state is illegal and the
verdict is not. Whatever gossip computed, something else is what stands. -/
theorem arbitration_overrides {S : Type} [MergeState S] {I : Invariant S}
    {verdict : S → S} (h : (Exit.arbitration (S := S) verdict).Applies I)
    {x y : S} (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y)) :
    verdict (x ⊔ y) ≠ x ⊔ y := by
  intro heq
  exact hbad (heq ▸ h x y hx hy)

/-- **⚠ Price two: an arbiter cannot be both faithful and a join-homomorphism.**
If the verdict left legal states alone *and* distributed over the merge, then at
a clash it would compute `x ⊔ y` itself — which is illegal. So an available
arbitration either overrides a legal replica, or is not a derived view of the
lattice at all. ERA is the second kind: the cut announcement is exogenous data,
which is why `JoinHom.lean`'s classification has nothing to say about it. -/
theorem arbitration_not_faithful_joinHom {S : Type} [MergeState S] {I : Invariant S}
    {verdict : S → S} (h : (Exit.arbitration (S := S) verdict).Applies I)
    {x y : S} (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y)) :
    ¬ ((∀ s : S, I s → verdict s = s)
        ∧ (∀ a b : S, verdict (a ⊔ b) = verdict a ⊔ verdict b)) := by
  rintro ⟨hfaith, hhom⟩
  refine arbitration_overrides h hx hy hbad ?_
  rw [hhom, hfaith x hx, hfaith y hy]

/-- **The third price, cited rather than re-proved: arbitration spends
antitonicity.** `Gated.lean` sells "late arrivals only ever remove moves from
effect"; an arbiter that can turn a denial into a permission cannot have that
sign (`GatedEra.antitone_forbids_enabling`), and ERA's promote does exactly
that. The bundle is the price tag the menu prints: the general refutation, and
the concrete pair of verdicts that refutes it. No new content — this is
`GatedEra`'s own result, assembled where a menu can cite it. -/
theorem arbitration_spends_antitonicity :
    ¬ GatedEra.AntitoneInEvents
    ∧ ¬ GatedEra.geGatedOps GatedEra.moveReq [] GatedEra.preLog
          GatedEra.duelOps GatedEra.opBob
    ∧ GatedEra.geGatedOps GatedEra.moveReq [] GatedEra.promLog
          GatedEra.duelOps GatedEra.opBob :=
  ⟨GatedEra.ge_not_antitone, GatedEra.ge_promote_denied_before,
   GatedEra.ge_promote_permitted_after⟩

/-- Rollback is arbitration with one extra constraint — it may only ever
*discard*. The constraint is what makes the loss theorem below available. -/
theorem rollback_is_an_arbitration {S : Type} [MergeState S] {I : Invariant S}
    {keep : S → S} (h : (Exit.rollback (S := S) keep).Applies I) :
    (Exit.arbitration (S := S) keep).Applies I := h.2

/-- **⚠ The rollback price: at a clash, at least one replica's contribution is
lost.** If the kept state were above *both* replicas it would be above their
merge (`merge_le_iff`), and it is below the merge by the discard-only
constraint, so antisymmetry would make it equal to the merge — which is
illegal. So somebody's work does not survive the rollback. ERA pays this in the
pending epoch: `GatedEra.ge_duel_arbiter_flips` is the same events, one more
cut, and the surviving op changes hands. -/
theorem rollback_loses_a_replica {S : Type} [MergeState S] {I : Invariant S}
    {keep : S → S} (h : (Exit.rollback (S := S) keep).Applies I)
    {x y : S} (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y)) :
    ¬ (x ⊑ keep (x ⊔ y) ∧ y ⊑ keep (x ⊔ y)) := by
  rintro ⟨hxk, hyk⟩
  obtain ⟨hdown, hleg⟩ := h
  have hup : (x ⊔ y) ⊑ keep (x ⊔ y) := merge_le_iff.mpr ⟨hxk, hyk⟩
  have heq : x ⊔ y = keep (x ⊔ y) := leq_antisymm hup (hdown (x ⊔ y))
  have hleg' : I (keep (x ⊔ y)) := hleg x y hx hy
  rw [← heq] at hleg'
  exact hbad hleg'

/-! ### §4.6 exposedFork — always open, and what it changes

The fork exit stops merging *values* and starts accumulating *branches*. The
branch lattice is `S → Prop` under pointwise disjunction (`JoinHom`'s
`instMergeStateProp` through the pointwise lift), and "every branch is legal" is
I-confluent for **every** invariant — which is why this exit is unconditional.
What it costs is the result type: after the merge there are two branches and
the caller must say which, or keep both. Kleppmann's slogan for the stance is
the title of a 2022 paper: *merge what you can, fork what you can't*. -/

/-- The branch carrier: a set of candidate states, merged by union. -/
abbrev Branches (S : Type) := S → Prop

/-- **Keeping both is always coordination-free.** "Every branch satisfies `I`"
is I-confluent over the branch lattice for every `I` whatsoever — a branch of
the union came from one side, and that side vouched for it. This is the content
behind `Exit.Applies`'s `True` for `exposedFork`. -/
theorem branches_iconfluent {S : Type} (I : Invariant S) :
    IConfluent (S := Branches S) (fun bs => ∀ s, bs s → I s) := by
  intro x y hx hy s hs
  have hs' : x s ∨ y s := hs
  exact hs'.elim (hx s) (hy s)

/-- **The fork exit costs zero meetings** — `zero_price_of_iconfluent` at the
branch invariant. -/
theorem fork_price_zero {S : Type} (I : Invariant S) :
    SegmentedIConfluent (S := Branches S) (fun _ => ()) (fun bs => ∀ s, bs s → I s)
    ∧ ∀ {Op : Type} (step : Branches S → Op → Branches S) (s : Branches S)
        (w : List Op), Cost.crossings (fun _ : Branches S => ()) step s w = 0 :=
  zero_price_of_iconfluent _ (branches_iconfluent I)

/-- **⚠ The fork price: the result is a plurality, and it is genuine.** At a
clash the two replicas are distinct (equal ones merge idempotently to a legal
state), and the union of their singleton branch sets is legal branch-by-branch.
So what the caller receives after a fork is not a state but two of them, and no
theorem here picks one. That choice left the engine. -/
theorem fork_presents_two_branches {S : Type} [MergeState S] {I : Invariant S}
    {x y : S} (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y)) :
    x ≠ y
    ∧ ∀ s : S, ((fun t => t = x) ⊔ (fun t => t = y) : Branches S) s → I s := by
  refine ⟨?_, ?_⟩
  · intro heq
    subst heq
    exact hbad (by rw [merge_idem]; exact hx)
  · intro s hs
    have hs' : s = x ∨ s = y := hs
    rcases hs' with rfl | rfl
    · exact hx
    · exact hy

/-! ### §4.7 weakenedInvariant and strongerMetadata -/

/-- **⚠ The weakening price: `J` admits a state `I` refuses.** Not "may admit" —
*does*, at the clash pair itself. A weakening that changed nothing would make
`I` I-confluent, so a weakening that works is always a weakening that lost
something, and the lost thing is exhibited. -/
theorem weakening_is_strict {S : Type} [MergeState S] {I J : Invariant S}
    (h : (Exit.weakenedInvariant (S := S) J).Applies I)
    {x y : S} (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y)) :
    J (x ⊔ y) ∧ ¬ I (x ⊔ y) := by
  obtain ⟨hJ, himp⟩ := h
  exact ⟨hJ x y (himp x hx) (himp y hy), hbad⟩

/-- The weakening exit costs zero meetings — `zero_price_of_iconfluent` at `J`. -/
theorem weakenedInvariant_price_zero {S : Type} [MergeState S] {I J : Invariant S}
    (h : (Exit.weakenedInvariant (S := S) J).Applies I) :
    SegmentedIConfluent (S := S) (fun _ => ()) J
    ∧ ∀ {Op : Type} (step : S → Op → S) (s : S) (w : List Op),
        Cost.crossings (fun _ : S => ()) step s w = 0 :=
  zero_price_of_iconfluent J h.1

/-- ⚠ **A third unconditional exit, and it is the worthless one.** `J = fun _ =>
True` applies to every invariant, so the menu's guaranteed rows are really
three, not two. `weakening_is_strict` prices it: the trivial weakening admits the
clash state, which is to say it admits everything. Naming it is the point —
an exit that always applies and always costs nothing is exactly the shape a
menu must not print without its price. -/
theorem weakenedInvariant_true_always_applies {S : Type} [MergeState S]
    (I : Invariant S) :
    (Exit.weakenedInvariant (S := S) (fun _ => True)).Applies I :=
  ⟨fun _ _ _ _ => trivial, fun _ _ => trivial⟩

/-- **⚠ The stronger-metadata price: some legal state stops being
representable.** If the richer carrier could represent every legal state — if
`π` covered them — then the upstairs confluence would push down and `I` would
have been I-confluent all along. So a refinement that fixes a real clash is
necessarily one where some legal `S`-state has no `T`-representative: the tags
did not merely *annotate* the state space, they *shrank* it. This is the lattice
form of the ancestral story, where only *reachable* triples are covered. -/
theorem refinement_needs_unreachability {S : Type} [MergeState S] {I : Invariant S}
    {T : Type} {instT : MergeState T} {π : T → S}
    (h : (Exit.strongerMetadata (S := S) T instT π).Applies I)
    (hcover : ∀ s : S, I s → ∃ t : T, π t = s) : IConfluent I := by
  obtain ⟨hhom, hconf⟩ := h
  intro x y hx hy
  obtain ⟨a, rfl⟩ := hcover x hx
  obtain ⟨b, rfl⟩ := hcover y hy
  have hab : I (π (@MergeState.merge T instT a b)) := hconf a b hx hy
  rw [hhom] at hab
  exact hab

/-- The stronger-metadata exit costs zero meetings — `zero_price_of_iconfluent`
upstairs, at the pulled-back invariant. -/
theorem strongerMetadata_price_zero {S : Type} [MergeState S] {I : Invariant S}
    {T : Type} {instT : MergeState T} {π : T → S}
    (h : (Exit.strongerMetadata (S := S) T instT π).Applies I) :
    @SegmentedIConfluent T Unit instT (fun _ => ()) (fun t => I (π t))
    ∧ ∀ {Op : Type} (step : T → Op → T) (s : T) (w : List Op),
        Cost.crossings (fun _ : T => ()) step s w = 0 :=
  @zero_price_of_iconfluent T instT (fun t => I (π t)) h.2

/-! ### §4.8 The dichotomy that decides whether the metadata exit is live

`Ancestral.clash_dichotomy` is the test. Its two branches name the two shapes a
clash can have, and they send you to *different* exits — which is the whole
reason a menu can discriminate at all rather than printing a constant list. -/

/-- **The dichotomy, read as an exit test** (`Ancestral.clash_dichotomy`). Take
an effect-faithful merge, a legal ancestor, and two locally-admitted operations
each legal there. Either some serialization of the two is legal —
**resurrection**, and there is something for an ancestor-reading merge to
choose, so the stronger-metadata exit is live — or no effect-faithful merge is
ancestrally confluent at all — **accumulation**, and that exit is dead for every
merge, not just for the one you tried. -/
theorem ancestral_exit_test {S Op : Type} (M : Ancestral.AncestralMerge S)
    (g : Ancestral.Guarded S Op) (I : Invariant S) (l : S) (a b : Op)
    (hser : Ancestral.Serializing M g) (hl : I l)
    (hga : g.guard a l = true) (hgb : g.guard b l = true)
    (ha : I (g.eff a l)) (hb : I (g.eff b l)) :
    (I (g.eff b (g.eff a l)) ∨ I (g.eff a (g.eff b l)))
      ∨ ¬ Ancestral.AncestralConfluent M g.impl I :=
  Ancestral.clash_dichotomy M g I l a b hser hl hga hgb ha hb

/-- **The test discriminates, in both directions, on this tree's own fixtures.**
Mutual exclusion under hand-off is a *resurrection* clash and the ancestral exit
takes it (`Ancestral.lock_ancestral_confluent`). A bounded counter is an
*accumulation* clash and the exit is dead — not for one merge but for **every**
effect-faithful one (`Ancestral.budget_defeats_every_faithful_merge`), which is
why `Ancestral.lean`'s own docstring sends that branch to escrow instead. This
is the theorem that refutes the "escrow rides resurrection" reading: escrow is
what is left when *this* exit is gone. -/
theorem ancestral_exit_discriminates :
    Ancestral.AncestralConfluent Ancestral.lockAM Ancestral.lockImpl Ancestral.AtMostOne
    ∧ ∀ M : Ancestral.AncestralMerge Nat,
        Ancestral.Serializing M (Ancestral.spendOps (10 + 1)) →
        ¬ Ancestral.AncestralConfluent M (Ancestral.spendOps (10 + 1)).impl
            (fun n => n ≤ 10 + 1) :=
  ⟨Ancestral.lock_ancestral_confluent,
   fun M hser => Ancestral.budget_defeats_every_faithful_merge 10 M hser⟩

/-! ### §4.9 The two unconditional exits, as availability proofs

These are the terms `menu_nonempty` stands on. Both are unconditional — and
both carry a theorem rather than a `True`, which is the whole difference
between "there is always an exit" and "there is always a row". -/

/-- **The fork exit is available for every invariant** — `branches_iconfluent`,
under the exit's own name. -/
theorem exposedFork_applies {S : Type} [MergeState S] (I : Invariant S) :
    (Exit.exposedFork (S := S)).Applies I := branches_iconfluent I

/-- **Full coordination is available for every invariant** —
`identity_seam_segmented`, under the exit's own name. -/
theorem fullCoordination_applies {S : Type} [MergeState S] (I : Invariant S)
    (n : Nat) : (Exit.fullCoordination (S := S) n).Applies I :=
  identity_seam_segmented I

/-! ## §5. The menu

The deliverable: for a given clash, the applicable exits with their prices and
their consequences, as a structure that **carries the proofs**. An entry cannot
be listed without an `Applies` term, so an unsound row is unrepresentable — that
is by construction, and `menu_sound` says so plainly rather than dressing the
construction up as a discovery. The content of `menu_sound` is its second
conjunct: the menu's own carried clash refutes global I-confluence, so a menu is
only ever built for an invariant that actually needs one. -/

/-- One row: an exit, a proof it is available, and the sentence a caller reads.
The `consequence` string is documentation, not evidence — every load-bearing
claim in it names a theorem in this file or in the tree. -/
structure MenuEntry {S : Type} [MergeState S] (I : Invariant S) : Type 1 where
  /-- The exit being offered. -/
  exit : Exit S
  /-- The proof that it is available for `I` — no row without one. -/
  applies : exit.Applies I
  /-- What the caller gives up by taking it. -/
  consequence : String

/-- **The menu for a clash**: the two replicas that refute I-confluence, the
workload length the full-coordination price is quoted against, and the
discriminating exits. The two unconditional rows are appended by
`ExitMenu.entries`, so no menu can forget them and none has to prove them. -/
structure ExitMenu {S : Type} [MergeState S] (I : Invariant S) : Type 1 where
  /-- One legal replica of the clash. -/
  x : S
  /-- The other. -/
  y : S
  /-- `x` is legal … -/
  hx : I x
  /-- … `y` is legal … -/
  hy : I y
  /-- … and the merge is not. -/
  hbad : ¬ I (x ⊔ y)
  /-- The workload the `fullCoordination` price is quoted against. -/
  workload : Nat
  /-- The exits that distinguish this clash from another. -/
  discriminating : List (MenuEntry I)

/-- The fork row, available to every invariant — content in
`branches_iconfluent` and `fork_presents_two_branches`. -/
def forkEntry {S : Type} [MergeState S] (I : Invariant S) : MenuEntry I where
  exit := .exposedFork
  applies := exposedFork_applies I
  consequence :=
    "keep both replicas as branches: 0 meetings (fork_price_zero), and the \
     result type changes — at a clash there are provably two distinct legal \
     branches and nothing here picks one (fork_presents_two_branches)"

/-- The full-coordination row, available to every invariant — content in
`identity_seam_segmented` (it is the seam at σ = id) and
`fullCoordination_is_the_ceiling` (nothing costs more). -/
def fullEntry {S : Type} [MergeState S] (I : Invariant S) (n : Nat) : MenuEntry I where
  exit := .fullCoordination n
  applies := fullCoordination_applies I n
  consequence :=
    "meet on every op: n meetings for an n-op workload, the ceiling \
     (fullCoordination_is_the_ceiling); always available because σ = id is \
     always a valid seam (identity_seam_segmented)"

/-- The menu as a list: the discriminating rows, then the two unconditional
ones. Appending them here is what makes `menu_nonempty` a theorem about every
menu rather than a property each menu must remember to have. -/
def ExitMenu.entries {S : Type} [MergeState S] {I : Invariant S} (m : ExitMenu I) :
    List (MenuEntry I) :=
  m.discriminating ++ [forkEntry I, fullEntry I m.workload]

/-- **There is always an exit.** The list-level argument is bookkeeping; what
makes the rows honest is that `exposedFork_applies` and
`fullCoordination_applies` are real theorems (`branches_iconfluent`,
`identity_seam_segmented`) holding for every invariant over every carrier. So no
clash ever leaves a caller with an empty menu, and no menu is padded with a row
that carries nothing. "Escalates" is never the whole answer. -/
theorem menu_nonempty {S : Type} [MergeState S] {I : Invariant S} (m : ExitMenu I) :
    m.entries ≠ [] := by
  cases hd : m.discriminating with
  | nil => simp [ExitMenu.entries, hd]
  | cons a l => simp [ExitMenu.entries, hd]

/-- **The menu is sound, and it is built for a real clash.** Every listed exit
genuinely applies — by construction, since `MenuEntry` cannot be built without
the proof; the honest content is the second conjunct, which says the invariant
the menu is *for* really does fail I-confluence, recovered from the carried
pair. A menu is therefore never advice about a free invariant. -/
theorem menu_sound {S : Type} [MergeState S] {I : Invariant S} (m : ExitMenu I) :
    (∀ e ∈ m.entries, e.exit.Applies I) ∧ ¬ IConfluent I :=
  ⟨fun e _ => e.applies, fun hconf => m.hbad (hconf m.x m.y m.hx m.hy)⟩

/-- The prices a caller compares. -/
def ExitMenu.prices {S : Type} [MergeState S] {I : Invariant S} (m : ExitMenu I) :
    List Nat := m.entries.map (fun e => e.exit.price)

/-! ## §6. Three worked menus — and they differ

Three real clashes from this tree, three menus. If the engine printed a constant
list the exercise would be worthless, so the load-bearing results here are the
*refutations*: `pin_escrow_starves` and `duel_escrow_starves` are why the escrow
row is absent from two menus, and `balance_total_not_a_seam` is why the seam row
is absent from the third. `the_menus_discriminate` collects them.

### §6.1 The uniqueness ceiling — pins, at most one

`Cost.pinInv` over `Cost.PinSet = GSet Bool`: at most one node pinned. The
canonical clash of this library (`Ceiling.uniqueness_ceiling`, wearing four
costumes across four files). -/

/-- One replica pins node `true`. -/
def pinT : Cost.PinSet := fun b => b == true

/-- The other pins node `false`. -/
def pinF : Cost.PinSet := fun b => b == false

theorem pinT_legal : Cost.pinInv pinT := by
  intro m n hm hn
  cases m <;> cases n
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · exact absurd hn (by decide)
  · rfl

theorem pinF_legal : Cost.pinInv pinF := by
  intro m n hm hn
  cases m <;> cases n
  · rfl
  · exact absurd hn (by decide)
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)

/-- ⚠ The merged document pins two nodes — the ceiling's death, on this carrier. -/
theorem pin_clash : ¬ Cost.pinInv (pinT ⊔ pinF) := by
  intro h
  exact absurd (h true false (by decide) (by decide)) (by decide)

/-- The arbitrated pin: an exogenous winner (`true`) is kept and every other
pin is dropped. Whatever two replicas merged to, at most one pin survives. -/
def pinKeepTrue (s : Cost.PinSet) : Cost.PinSet := fun b => s b && b

theorem pinKeepTrue_arbitrates :
    (Exit.arbitration (S := Cost.PinSet) pinKeepTrue).Applies Cost.pinInv := by
  intro x y _hx _hy m n hm hn
  have hm' : ((x m || y m) && m) = true := hm
  have hn' : ((x n || y n) && n) = true := hn
  have hm2 : m = true := ((Bool.and_eq_true _ _).mp hm').2
  have hn2 : n = true := ((Bool.and_eq_true _ _).mp hn').2
  rw [hm2, hn2]

/-- The per-slot charge: one unit for each pinned node. A join-homomorphism into
the escrow lattice — pinning is monotone and `max` is what union becomes under
the count. -/
def pinCharge (s : Cost.PinSet) : Escrow Bool := fun b => if s b = true then 1 else 0

theorem pinCharge_hom (x y : Cost.PinSet) :
    pinCharge (x ⊔ y) = pinCharge x ⊔ pinCharge y := by
  funext b
  show (if (x b || y b) = true then 1 else 0)
      = Nat.max (if x b = true then 1 else 0) (if y b = true then 1 else 0)
  cases hxb : x b <;> cases hyb : y b <;> decide

/-- **⚠ escrow ✗ for the uniqueness ceiling — and the reason is starvation.**
Any escrow of the pin ceiling at the per-slot charge that gives *every* slot a
positive share is unavailable: with a share each, both slots can be pinned
inside quota, and the entailment would then certify a two-pin state. A bound of
one does not divide. -/
theorem pin_escrow_starves (q : Bool → Nat) :
    ¬ (Exit.escrow (S := Cost.PinSet) Bool q pinCharge).Applies Cost.pinInv := by
  rintro ⟨-, hent, hpos⟩
  have hin : ∀ i, pinCharge (fun _ => true) i ≤ q i := by
    intro i
    have hqi := hpos i
    have hval : pinCharge (fun _ : Bool => true) i = 1 := rfl
    rw [hval]
    omega
  exact absurd (hent (fun _ => true) hin true false rfl rfl) (by decide)

/-- The same fact stated as the design consequence: **an available escrow of a
uniqueness ceiling must give some slot quota zero** — a replica that can never
pin. That is a lease with a single holder, not a pre-partition, and calling it
escrow would hide the cost. -/
theorem pin_escrow_zero_quota {q : Bool → Nat}
    (hent : ∀ s : Cost.PinSet, (∀ i, pinCharge s i ≤ q i) → Cost.pinInv s) :
    ∃ i, q i = 0 := by
  apply Classical.byContradiction
  intro hcon
  have hpos : ∀ i, 0 < q i := by
    intro i
    have hne : q i ≠ 0 := fun h => hcon ⟨i, h⟩
    omega
  exact pin_escrow_starves q ⟨pinCharge_hom, hent, hpos⟩

/-- **The ceiling's quoted seam price of `0`: forced, achieved — and an
undercount.** Three halves, and the third is why the row must never be read as
"free":

  * **forced** — pinning is an inflation (`Cost.pinStep_inflationary`), so a pin
    stream admits *no* clash blocks at all (`Cost.clashBlocks_nil_of_inflationary`)
    and §3's lower bound on it is `0`. The quoted number is not an omission.
  * **achieved** — and it is realised: the measured crossing count of pinning
    `true` from empty, under this seam, is exactly `0`
    (`Cost.pinTrue_free_under_seamFalse`).
  * **⚠ and it undercounts** — `Cost.no_seam_frees_both`: no single valid seam
    gives both streams cost zero, so two replicas running them concurrently must
    coordinate and no per-stream count reports it. This is `Cost.lean`'s own
    ⟨TERMINAL⟩ scope note surfacing as a menu row's fine print. -/
theorem ceiling_seam_floor_is_zero :
    (∀ bs : List (List Bool),
        Cost.ClashBlocks Cost.pinInv Cost.pinStep Cost.emptyPin bs → bs = [])
    ∧ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).price
        = Cost.crossings (fun s : Cost.PinSet => s false) Cost.pinStep
            Cost.emptyPin [true]
    ∧ ∀ (Seg : Type) [DecidableEq Seg] (σ : Cost.PinSet → Seg),
        SegmentedIConfluent σ Cost.pinInv →
        ¬ (Cost.crossings σ Cost.pinStep Cost.emptyPin [true] = 0
            ∧ Cost.crossings σ Cost.pinStep Cost.emptyPin [false] = 0) :=
  ⟨fun _ hcl => Cost.clashBlocks_nil_of_inflationary Cost.pinStep_inflationary hcl,
   Cost.pinTrue_free_under_seamFalse.symm,
   fun _ _ σ hseg => Cost.no_seam_frees_both σ hseg⟩

/-- **The ceiling's menu.** Two discriminating rows — a seam (whose zero comes
with its undercount attached) and an arbitration — plus the two unconditional
rows. No escrow row: `pin_escrow_starves`. -/
def ceilingMenu : ExitMenu Cost.pinInv where
  x := pinT
  y := pinF
  hx := pinT_legal
  hy := pinF_legal
  hbad := pin_clash
  workload := 2
  discriminating :=
    [ { exit := .seam Bool (fun s => s false) 0
        applies := Cost.seamFalse_segmented
        consequence :=
          "coordinate only when slot false changes. ⚠ the 0 is a PER-STREAM \
           floor (Cost.pinStep_inflationary): Cost.no_seam_frees_both proves no \
           single valid seam frees both streams, so the concurrent workload \
           costs more than any per-stream count reports \
           (ceiling_seam_floor_is_zero)" },
      { exit := .arbitration pinKeepTrue
        applies := pinKeepTrue_arbitrates
        consequence :=
          "an exogenous winner keeps its pin and every other pin is dropped: \
           0 meetings, but the verdict is not the merge \
           (arbitration_overrides) and the arbiter is not a join-hom \
           (arbitration_not_faithful_joinHom); the ERA form of this price is \
           arbitration_spends_antitonicity" } ]

/-! ### §6.2 The budget/balance clash — a shared bound over two devices

`Escrow Bool` under pointwise `max`, with the *shared* bound "the two devices
together have spent at most 10". This is `Catalog.lean` §4's
`pncounter_nonneg_not_iconfluent` shape: a bound nobody owns. -/

/-- The two-device spend record. -/
abbrev Balance := Escrow Bool

/-- The shared bound: together, at most 10. -/
def balanceInv : Invariant Balance := fun f => f true + f false ≤ 10

/-- One replica spends the whole budget on device `true` … -/
def balX : Balance := fun b => if b then 10 else 0

/-- … the other spends it all on device `false`. -/
def balY : Balance := fun b => if b then 0 else 10

theorem balX_legal : balanceInv balX := by
  show balX true + balX false ≤ 10
  decide

theorem balY_legal : balanceInv balY := by
  show balY true + balY false ≤ 10
  decide

/-- ⚠ Merging the two spends double the budget — the shared bound's death. -/
theorem balance_clash : ¬ balanceInv (balX ⊔ balY) := by
  show ¬ (Nat.max 10 0 + Nat.max 0 10 ≤ 10)
  decide

/-- **escrow ✓ for the shared bound.** Give each device 5. The charge is the
identity (the state already *is* the escrow lattice), staying inside 5 keeps the
bound by arithmetic, and both shares are positive — so this is a pre-partition
and not a lease. `Catalog.escrow_local_bound_iconfluent` is the confluence
underneath. -/
theorem balance_escrow_applies :
    (Exit.escrow (S := Balance) Bool (fun _ => 5) id).Applies balanceInv := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro f hf
    have h1 : f true ≤ 5 := hf true
    have h2 : f false ≤ 5 := hf false
    show f true + f false ≤ 10
    omega
  · intro _
    show 0 < 5
    decide

/-- The obvious seam candidate: how much has been spent in total. -/
def balTotal (f : Balance) : Nat := f true + f false

/-- **⚠ seam ✗ for the shared bound — the obvious projection is not a seam.**
Two replicas that have spent the same *total* can still merge over budget, and
`balX`/`balY` are exactly such a pair (total 10 each, merging to 20). So the
seam row is absent for a reason, not for want of trying. What buys a seam here
is moving the allocation *into* the state — `Segmented.QuotaState` and
`Segmented.budget_segmented` — which is escrow made re-splittable, at the cost
of a coordination point at each re-allocation. -/
theorem balance_total_not_a_seam (n : Nat) :
    ¬ (Exit.seam (S := Balance) Nat balTotal n).Applies balanceInv := by
  intro h
  exact balance_clash (h balX balY (by decide) balX_legal balY_legal).1

/-- **The balance's menu.** One discriminating row — the escrow — plus the two
unconditional rows. No seam row: `balance_total_not_a_seam`. -/
def balanceMenu : ExitMenu balanceInv where
  x := balX
  y := balY
  hx := balX_legal
  hy := balY_legal
  hbad := balance_clash
  workload := 2
  discriminating :=
    [ { exit := .escrow Bool (fun _ => 5) id
        applies := balance_escrow_applies
        consequence :=
          "give each device 5: 0 meetings while inside your share \
           (escrow_price_zero). ⚠ the price is reachability — \
           escrow_forbids_a_clash_replica proves at least one of the two legal \
           replicas is now out of quota, and here it is both: neither device \
           can spend the whole budget alone any more. Re-splitting needs \
           Segmented.budget_segmented's seam" } ]

/-! ### §6.3 The duelling admins — `Authority.SoleAdmin`

`Authority.sole_admin_not_iconfluent` is the clash: two partitions each mint
their own root admin, and the merge holds two. This is the scenario ERA exists
for, and it is the only one of the three whose menu has a rollback row. -/

/-- The invariant the arbiter repairs: at most one root-parented grant.
⚠ The conjunct `Authority.WF 9` is deliberately *not* here — see
`arbKeep_can_orphan`, which is why. -/
abbrev DuelInv : Invariant Authority.GrantSet := Authority.SoleAdmin

/-- ⚠ **`SoleAdmin` clashes** — `Authority.sole_admin_not_iconfluent`'s witness
pair, with the well-formedness conjunct dropped (each singleton is well-formed
anyway: `Authority.aliceRoot_wf`, `Authority.bobRoot_wf`). -/
theorem duel_clash : ¬ DuelInv (Authority.aliceRoot ⊔ Authority.bobRoot) := by
  intro h
  exact absurd (h 1 9 2 9 (by decide) (by decide)) (by decide)

/-- The arbiter's canonicalisation: keep every delegated grant, and among the
root-parented ones keep only the announced winner `w`. -/
def arbKeep (w : Nat) (s : Authority.GrantSet) : Authority.GrantSet :=
  fun g => s g && (!(g.2.1 == 0) || g.1 == w)

/-- **arbitration ✓ for the duel.** Whatever two replicas merged to, at most one
root-parented grant survives — both survivors carry the announced winner's id,
so they are equal. This is ERA's shape at the grant lattice: the arbiter never
names an admin, it announces which id its cut placement lets through. -/
theorem arbKeep_arbitrates (w : Nat) :
    (Exit.arbitration (S := Authority.GrantSet) (arbKeep w)).Applies DuelInv := by
  intro x y _hx _hy i σ i' σ' h h'
  have h1 : ((x (i, 0, σ) || y (i, 0, σ)) && (!((0 : Nat) == 0) || (i == w))) = true := h
  have h2 : ((x (i', 0, σ') || y (i', 0, σ')) && (!((0 : Nat) == 0) || (i' == w)))
      = true := h'
  have hi : i = w := by
    have := ((Bool.and_eq_true _ _).mp h1).2
    simpa using this
  have hi' : i' = w := by
    have := ((Bool.and_eq_true _ _).mp h2).2
    simpa using this
  rw [hi, hi']

/-- **rollback ✓ for the duel** — the same map, now read as a discard: the
arbiter only ever removes grants, never mints one. That is what makes
`rollback_loses_a_replica` available, and it is exactly what ERA pays in the
pending epoch. -/
theorem arbKeep_rolls_back (w : Nat) :
    (Exit.rollback (S := Authority.GrantSet) (arbKeep w)).Applies DuelInv := by
  refine ⟨?_, arbKeep_arbitrates w⟩
  intro s
  show arbKeep w s ⊔ s = s
  funext g
  show ((s g && (!(g.2.1 == 0) || g.1 == w)) || s g) = s g
  cases hs : s g <;> simp

/-- **⚠ The duel's rollback price, concretely: Bob's grant does not survive.**
`rollback_loses_a_replica` at the duel pair — the arbitrated state cannot be
above both minted admin grants. The deployed version of this loss flips with the
arbiter's cut placement: `GatedEra.ge_duel_arbiter_flips` is the same five
events, one more announcement, and the *other* duellist's op is the one that
survives. -/
theorem duel_rollback_loses_a_duellist :
    ¬ (Authority.aliceRoot ⊑ arbKeep 1 (Authority.aliceRoot ⊔ Authority.bobRoot)
        ∧ Authority.bobRoot ⊑ arbKeep 1 (Authority.aliceRoot ⊔ Authority.bobRoot)) :=
  rollback_loses_a_replica (arbKeep_rolls_back 1)
    Authority.aliceRoot_sole Authority.bobRoot_sole duel_clash

/-- A three-grant delegation chain: two root admins, and a grant that admin 2
issued. Well-formed (`orphanSet_wf`), and the counterexample carrier for
`arbKeep_can_orphan`. -/
def orphanSet : Authority.GrantSet := fun g =>
  (g == ((1 : Nat), (0 : Nat), (9 : Nat)))
    || ((g == ((2 : Nat), (0 : Nat), (9 : Nat)))
        || (g == ((3 : Nat), (2 : Nat), (5 : Nat))))

/-- Membership in `orphanSet` is one of its three grants. -/
theorem orphanSet_mem {g : Authority.Grant} (h : orphanSet g = true) :
    g = (1, 0, 9) ∨ g = (2, 0, 9) ∨ g = (3, 2, 5) := by
  have h' : ((g == ((1 : Nat), (0 : Nat), (9 : Nat)))
        || ((g == ((2 : Nat), (0 : Nat), (9 : Nat)))
            || (g == ((3 : Nat), (2 : Nat), (5 : Nat))))) = true := h
  rcases (Bool.or_eq_true _ _).mp h' with h2 | h2
  · exact Or.inl (by simpa using h2)
  · rcases (Bool.or_eq_true _ _).mp h2 with h3 | h3
    · exact Or.inr (Or.inl (by simpa using h3))
    · exact Or.inr (Or.inr (by simpa using h3))

/-- The chain is well-formed: both root grants narrow inside the root scope, and
grant 3 narrows inside its parent's. -/
theorem orphanSet_wf : Authority.WF 9 orphanSet := by
  intro i p σ hmem
  rcases orphanSet_mem hmem with h | h | h <;>
    (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h)
  · exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩
  · exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩
  · exact ⟨by omega, Or.inr ⟨0, 9, by decide, by omega⟩⟩

/-- ⚠ Pruning to winner 1 drops grant 2 — and grant 3, still present, now names
a parent nobody holds. -/
theorem arbKeep_orphans : ¬ Authority.WF 9 (arbKeep 1 orphanSet) := by
  intro hwf
  have hmem : arbKeep 1 orphanSet (3, 2, 5) = true := by decide
  obtain ⟨-, hnarrow⟩ := hwf 3 2 5 hmem
  rcases hnarrow with ⟨hp, -⟩ | ⟨q, σ', hq, -⟩
  · exact absurd hp (by omega)
  · have hq' : (orphanSet (2, q, σ') && (!(q == 0) || ((2 : Nat) == 1))) = true := hq
    have hsplit := (Bool.and_eq_true _ _).mp hq'
    rcases orphanSet_mem hsplit.1 with h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact absurd h.1 (by omega)
    · obtain ⟨-, rfl, -⟩ := h
      exact absurd hsplit.2 (by decide)
    · exact absurd h.1 (by omega)

/-- ⚠ **Why `Authority.WF 9` is not in `DuelInv`: the arbiter can orphan a
child.** A well-formed state where grant 3 was issued by grant 2 loses its
parent when the arbiter picks winner 1, and `WF`'s parent-existence clause is
then false — the delegation chain is cut above a grant that is still present.
Pruning a DAG by a rule that reads only the root layer does not preserve
well-formedness, and no choice of `w` fixes it. Repairing this is a different
exit (cascade the deletion — a *larger* rollback) and it is not built here. -/
theorem arbKeep_can_orphan :
    Authority.WF 9 orphanSet ∧ ¬ Authority.WF 9 (arbKeep 1 orphanSet) :=
  ⟨orphanSet_wf, arbKeep_orphans⟩

/-- The per-id charge on root-parented grants: one unit for each admin minted
under id `i`. -/
def grantCharge (s : Authority.GrantSet) : Escrow Nat :=
  fun i => if s (i, 0, 9) = true then 1 else 0

/-- **⚠ escrow ✗ for the duel — starvation again.** Any positive-share escrow of
"at most one admin" at the per-id charge would let every id mint an admin inside
quota, and the entailment would then certify a state with two. One admin does
not divide among many ids; the only escrow that applies gives all but one id a
share of zero, which is a lease, not a partition. -/
theorem duel_escrow_starves (q : Nat → Nat) :
    ¬ (Exit.escrow (S := Authority.GrantSet) Nat q grantCharge).Applies DuelInv := by
  rintro ⟨-, hent, hpos⟩
  have hin : ∀ i, grantCharge (fun _ => true) i ≤ q i := by
    intro i
    have hqi := hpos i
    have hval : grantCharge (fun _ : Authority.Grant => true) i = 1 := rfl
    rw [hval]
    omega
  exact absurd (hent (fun _ => true) hin 1 9 2 9 rfl rfl) (by decide)

/-- **The duel's menu.** Two discriminating rows — an arbitration and a rollback
(the same map, read twice) — plus the two unconditional rows. No escrow row:
`duel_escrow_starves`. This is the only menu of the three with a rollback. -/
def duelMenu : ExitMenu DuelInv where
  x := Authority.aliceRoot
  y := Authority.bobRoot
  hx := Authority.aliceRoot_sole
  hy := Authority.bobRoot_sole
  hbad := duel_clash
  workload := 2
  discriminating :=
    [ { exit := .arbitration (arbKeep 1)
        applies := arbKeep_arbitrates 1
        consequence :=
          "an announced winner's admin grant survives and the rival's is \
           dropped: 0 meetings between replicas (GatedEra.ge_deterministic), \
           paid for in antitonicity (arbitration_spends_antitonicity) and in a \
           verdict that is not the merge (arbitration_overrides). ⚠ it does not \
           preserve Authority.WF: arbKeep_can_orphan" },
      { exit := .rollback (arbKeep 1)
        applies := arbKeep_rolls_back 1
        consequence :=
          "read the same map as a discard: nothing is minted, and at least one \
           duellist's grant provably does not survive \
           (duel_rollback_loses_a_duellist). ERA pays this in the pending \
           epoch, where a later cut flips which one \
           (GatedEra.ge_duel_arbiter_flips)" } ]

/-! ### §6.4 The three menus, side by side — the engine discriminates

If the same rows appeared on every menu the exercise would have produced a
constant function with proofs attached. They do not, and the theorem below is
the evidence: **the same exit constructor is available on one clash and
refuted on another**, in both directions, for two different exits. -/

/-- **The menus differ, proved.** Escrow takes the shared bound and is refuted
on both the pin ceiling and the duel — a bound of 10 divides into 5+5, a bound
of 1 does not divide at all. The seam takes the pin ceiling and is refuted on
the shared bound's obvious projection. Rollback is available on the duel. Note
what the escrow rows say about the dichotomy: the ceiling and the balance are
*both* accumulation clashes in `Ancestral.clash_dichotomy`'s sense, and escrow
separates them anyway — so divisibility is a second axis, not a restatement of
the first. -/
theorem the_menus_discriminate :
    -- escrow: ✓ on the shared bound …
    (Exit.escrow (S := Balance) Bool (fun _ => 5) id).Applies balanceInv
    -- … ✗ on the pin ceiling, for every quota …
    ∧ (∀ q : Bool → Nat,
        ¬ (Exit.escrow (S := Cost.PinSet) Bool q pinCharge).Applies Cost.pinInv)
    -- … and ✗ on the duel, for every quota.
    ∧ (∀ q : Nat → Nat,
        ¬ (Exit.escrow (S := Authority.GrantSet) Nat q grantCharge).Applies DuelInv)
    -- seam: ✓ on the pin ceiling …
    ∧ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).Applies Cost.pinInv
    -- … ✗ on the shared bound's obvious projection, at every quoted floor.
    ∧ (∀ n : Nat, ¬ (Exit.seam (S := Balance) Nat balTotal n).Applies balanceInv)
    -- rollback: ✓ on the duel.
    ∧ (Exit.rollback (S := Authority.GrantSet) (arbKeep 1)).Applies DuelInv :=
  ⟨balance_escrow_applies, pin_escrow_starves, duel_escrow_starves,
   Cost.seamFalse_segmented, balance_total_not_a_seam, arbKeep_rolls_back 1⟩

/-- Every menu is non-empty and sound — the two headline theorems, at the three
worked clashes. -/
theorem worked_menus_are_menus :
    (ceilingMenu.entries ≠ [] ∧ ¬ IConfluent Cost.pinInv)
    ∧ (balanceMenu.entries ≠ [] ∧ ¬ IConfluent balanceInv)
    ∧ (duelMenu.entries ≠ [] ∧ ¬ IConfluent DuelInv) :=
  ⟨⟨menu_nonempty ceilingMenu, (menu_sound ceilingMenu).2⟩,
   ⟨menu_nonempty balanceMenu, (menu_sound balanceMenu).2⟩,
   ⟨menu_nonempty duelMenu, (menu_sound duelMenu).2⟩⟩

/-- The three price lists, evaluated. Every menu ends with the two unconditional
rows — fork at `0`, full coordination at the workload length — and differs
before them. The numbers mean what §4 proved they mean; in particular the
ceiling's leading `0` is `ceiling_seam_floor_is_zero`'s per-stream floor, with
its undercount attached, and not a claim that the ceiling is free. -/
theorem worked_menu_prices :
    ceilingMenu.prices = [0, 0, 0, 2]
    ∧ balanceMenu.prices = [0, 0, 2]
    ∧ duelMenu.prices = [0, 0, 0, 2] :=
  ⟨rfl, rfl, rfl⟩

end Uwueave.Exits
