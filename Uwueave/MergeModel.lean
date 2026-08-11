/-
# Uwueave.MergeModel — one merge interface, and the proof that it must have
three shapes.

## Where this came from

Our field-kind sketch (`CODEXHELP.md` §3.3, "tell us what a field kind must
carry") was **carrier + `MergeState` + verdict routes + exits**. codex's second
review rejected the `MergeState` slot as *mandatory*, and `PREOSCRIPTING.md` §6
records the verdict we adopted from it:

> `MergeState` cannot be mandatory. A join CRDT, an op-replay structure, and an
> MRDT with a merge base have genuinely different merge signatures — and
> `Ancestral.join_is_ancestral_merge_iff_trivial` proves a join *is* a
> three-way merge only on a one-point carrier. One mandatory binary interface
> would either lie about three-way merge or discard the base uncertainty that
> makes it valuable. So merge is a **model** with a context type
> (`Uwueave/MergeModel.lean`) …

This file is that named module. The objection is not stylistic: the repo
already contained the refutation of the alternative, so a field-kind interface
with one mandatory `MergeState` would have erased our own theorem — every MRDT
field would have had to present a join it provably does not have. §1 is the
interface with the merge *signature* left open, and §7 proves the three shapes
are genuinely three: pairwise separated, each by a theorem, so a reader can see
the generalization was forced rather than enjoyed.

**One visible deviation from that table.** `PREOSCRIPTING.md` §6 gives the
`MergeModel` capability as "carrier, merge context, outcomes, **laws**". The
laws are *not* fields here (§3 says why: the semilattice is false for the MRDT
counter, and associativity does not even typecheck once the merge result stops
being a state). They are separate predicates an instance supplies one at a
time. Likewise, the `Observation` triple below is the minimum needed to state
*one* confluence judgement across the three shapes — it is not the planned
`ObservationModel` capability, which owes a result domain **and its
approximation order**, and which this file does not build.

## What is here

  * §1 **The class**, in codex's shape — `State`, `MergeContext`, `MergeResult`,
    `merge`, `validContext` — plus the three fields (`Observation`,
    `observeState`, `observeResult`) and one list (`contextObs`) that make a
    *single* confluence judgement statable across models whose merge result is
    not a state at all. Every added field is used by an instance below; none is
    decoration.
  * §2 **`IConfluentIn K I`** — the invariant survives merging *in this model*.
  * §3 **The laws, à la carte.** Not fields of the class: separate predicates,
    each stated at the widest generality it has, so an instance supplies the
    ones it honestly satisfies. Two of them (`MergeAssociative`,
    `MergeFastForward`) are not even *typable* without an extra structure
    (`Internal`, `Based`) — which is the strongest available form of "this model
    is not required to have it".
  * §4–§6 **Three instances**: the join CRDT, the ancestral/MRDT merge, and
    op-replay (twice: the abstract derived-view pattern, and the shipping
    kernel).
  * §7 **The separation.** (a) vs (b) by instantiating
    `Ancestral.join_is_ancestral_merge_iff_trivial`; (b) has no semilattice at
    all (`counterAM` is *refutably* non-idempotent, not merely unproved);
    (c) vs (a) because the op-replay merge is a function of the op **set**
    (`ExecRefine.absReplay_ext_mem`) and **not** a function of the two replicas'
    views — witnessed, on the shipping kernel, by three real ops.
  * §8 **The agreement, which is the point of the exercise.** `IConfluent` is
    `IConfluentIn` at the join model and `Ancestral.AncestralConfluent` is
    `IConfluentIn` at the ancestral model — both as `Iff`s, and both are
    hypothesis-shuffling: nothing is proved twice, and every existing theorem
    about either transports. Two existing judgements become one parameterized
    judgement, and `Ancestral`'s incomparability result (§8 there) restates as
    four clauses about *one* predicate at two models.
  * §9 **A three-valued base decision** as a merge context — selected /
    ambiguous / unavailable, with absence *proved* rather than flagged, and
    with each of the three cases shown inhabited and the difference between
    them shown observable.

## Prior art next door, and what we did not take

`~/dev/minidregg` (sibling Lean repo, same author) has the hygiene layer under
this question, and this file **depends on none of it** — uwueave stays
self-contained; the citation is motivation, not linkage. What is there, stated
as we read it:

  * `Kernel/HyperdocumentMerge.lean` carries a per-field `base : Option
    VersionEventId`, a `ValidMerge` condition set, and
    `BaseDecision = selected | ambiguous | unavailable`, where
    `unavailableOfAbsent` makes *absence a proof obligation* rather than a free
    flag.
  * `Theory/CausalVersionAncestry.lean` has `LowestCommonBase` with
    `selected_unique`, and `AmbiguousCommonBases.excludes_lowest` — two distinct
    maximal common bases exclude a lowest one.

§9 is the analogue of the first, built on *our* `Ancestral.Reachable`. The
lesson we took is the three-valuedness itself: **ambiguity is a real third case,
and a binary merge interface has nowhere to put it.** Here it lives in
`validContext`, which is exactly the field an interface needs so that
"unavailable" can carry a refutation of the base's existence for *this* pair
rather than a boolean nobody checked.

## Non-claims

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE⟩ = work wearing a caveat's
clothes.

  * ⟨TERMINAL⟩ **A merge result carrying provenance is not symmetric as a
    result.** `MergeCommutative` is therefore stated at the *observation* level
    (`observeResult (merge c x y) = observeResult (merge c y x)`), and
    `MergeState.merge_comm` is the special case where result and observation
    coincide. Stating it as result equality would have forbidden §5's evidence
    fields, which is precisely the "discard what makes the MRDT model valuable"
    failure codex named.
  * ⟨TERMINAL⟩ **`MergeModel` is a signature plus a reading, not a semantics.**
    It says nothing about *why* a model's merge is right; §4–§6 each carry their
    own laws and their own confluence proof. A model with a nonsense `merge`
    typechecks here and fails §2.
  * ⟨TERMINAL⟩ **The separation results are at fixed carriers.** As
    `Ancestral` §6.1 says at length: a two-way CRDT escapes by enlarging Σ with
    causal metadata, and nothing here claims otherwise. §7's theorems say the
    three *models* differ, not that any invariant is unimplementable in any of
    them.
  * ⟨UNDONE⟩ **The full universe chain is not closed.** This file's key, state,
    context, result, and observation now inhabit independent universes, and all
    generic instances below follow. Downstream `Histories.VersionDag` /
    `Histories.History` and the evidence/world carriers remain in `Type 0`, so
    the end-to-end history/certificate chain is still bounded there.
  * ⟨UNDONE⟩ **No verdict routes, no exits.** The field-kind sketch has three
    more slots (`classify` routes, exits with prices, obligation types). This
    file settles only the merge slot, which is the one codex refused.
  * ⟨UNDONE⟩ **`contextObs` is a list, not a frontier.** A context that names
    two ambiguous bases exposes both; a context that names an antichain of
    frontiers (codex's Timely correction) would want more structure. The list
    is enough for selected/ambiguous/unavailable and no more.
  * ⟨UNDONE⟩ **Ambiguity is two distinct bases, not a refutation of a lowest
    one.** §9's `BaseDecision.Valid` demands the pair, because uwueave has no
    `LowestCommonBase` to refute against — minidregg's
    `AmbiguousCommonBases.excludes_lowest` is that theorem, and it is next door,
    not here. `ambiguous_inhabited` shows the situation is real regardless.
  * ⟨UNDONE⟩ **No repeated or criss-cross merging.** Like `Ancestral`, every
    judgement here is about a single fork-and-join. Convergence on a version
    DAG needs Kaki et al.'s further conditions and gets no verdict.

Literature: Kaki, Priya, Sivaramakrishnan, Jagannathan, "Mergeable Replicated
Data Types", OOPSLA 2019 (the `⟨Σ, σ₀, do, merge⟩` three-way model);
Kleppmann, Mulligan, Gomes, Beresford, "A highly-available move operation for
replicated trees", 2022 (the op-replay/derived-view pattern); Bailis et al.,
"Coordination Avoidance in Database Systems", VLDB 2015 (I-confluence).
-/
import Uwueave.Ancestral
import Uwueave.ExecRefine
import Uwueave.Move

namespace Uwueave

universe uK uS uC uR uO u v

/-! ## §1. The class

Five fields are codex's: `State`, `MergeContext`, `MergeResult`, `merge`,
`validContext`. Four are ours, and each is forced by an instance below:

  * `Observation` / `observeState` / `observeResult` — the op-replay model's
    merge returns a **materialized view**, not a state, so "does the invariant
    survive the merge?" cannot be a question about `State`. It is a question
    about what a replica and a merge result are *read as*. Where result and
    state coincide (§4, §5) these are identities and the generalization costs
    nothing.
  * `contextObs` — the ancestral model's judgement assumes its *ancestor* legal
    (`Ancestral.AncestralConfluent` takes `I l` as a hypothesis). A model must
    therefore be able to say which observations its context itself exposes: none
    for a join, the base for a three-way merge, **both** for an ambiguous base
    decision, and none again when no base was available (§9).

`observeState` takes the context because a log's view depends on the base it is
replayed against (§6.2); models whose observation is context-free ignore it. -/

/-- **A merge model.** The *signature* of a merge, plus the reading under which
an invariant can be asked about one.

`merge c x y` reconciles two replicas under a context `c` — nothing for a join,
an ancestor for an MRDT, a structural base for an op-replay kernel — and
`validContext c x y` says when that context is legitimate for that pair, which
is where a merge-base procedure's obligations live (§9).

No laws. Laws are §3, supplied per instance. -/
class MergeModel (K : Type uK) where
  /-- The replicated state a replica holds. -/
  State : Type uS
  /-- What the merge needs besides the two replicas. -/
  MergeContext : Type uC
  /-- What the merge returns — a state, or a view, or a state plus evidence. -/
  MergeResult : Type uR
  /-- What an invariant is asked about. -/
  Observation : Type uO
  /-- The merge itself. -/
  merge : MergeContext → State → State → MergeResult
  /-- When this context is legitimate for these two replicas. -/
  validContext : MergeContext → State → State → Prop
  /-- How a replica reads, against a context. -/
  observeState : MergeContext → State → Observation
  /-- How a merge result reads. -/
  observeResult : MergeResult → Observation
  /-- The observations the context itself exposes — the ones a judgement may
  assume legal, because they are states the system already committed. -/
  contextObs : MergeContext → List Observation

namespace MergeModel

open Uwueave.Ancestral Uwueave.Necessity Uwueave.Catalog

/-! ## §2. The judgement, parameterized by the model

`Confluence.IConfluent` asks: is the join of two legal replicas legal?
`Ancestral.AncestralConfluent` asks the same of a three-way merge on
co-reachable replicas. §8 proves both are this one predicate. -/

/-- **Invariant confluence in a model.** For every legitimate context and every
pair of replicas whose observations are legal — and with the context's own
observations legal, since they are states the system already committed — the
merge result reads legal.

Read the three hypothesis groups: `validContext` is *structural* legitimacy
(reachability, groundedness) and is independent of `I`; `contextObs` is where
`I` is assumed of the context; the last two are the replicas. -/
def IConfluentIn (K : Type u) [m : MergeModel K] (I : m.Observation → Prop) : Prop :=
  ∀ (c : m.MergeContext) (x y : m.State),
    m.validContext c x y →
    (∀ o ∈ m.contextObs c, I o) →
    I (m.observeState c x) → I (m.observeState c y) →
    I (m.observeResult (m.merge c x y))

/-! ## §3. The laws, à la carte

Three laws are statable for **every** model; two more need extra structure and
are not typable without it. That asymmetry is the deliverable: an interface
that demanded associativity of an MRDT would be demanding a sentence that does
not typecheck once the merge result stops being a state. -/

/-- **Commutativity, at the observation level**: both replicas compute the same
*reading* from the same triple, so "which peer merged" is unobservable.

⚠ Not stated as `merge c x y = merge c y x`. A three-way merge may return
provenance (§5's `Reconciled` carries the base and both sides), and a result
carrying which side was which is not symmetric as a result. It is symmetric as
an observation, which is the property anyone actually depends on.
`MergeState.merge_comm` is the special case where result and observation
coincide. -/
def MergeCommutative (K : Type u) [m : MergeModel K] : Prop :=
  ∀ (c : m.MergeContext) (x y : m.State), m.validContext c x y →
    m.observeResult (m.merge c x y) = m.observeResult (m.merge c y x)

/-- **Idempotence, at the observation level**: merging a replica with itself
tells you nothing new. Satisfied by both op-replay models (a log unioned with
itself is that log) and by the join; **refuted** for the MRDT counter (§7.2),
which is exactly why it is not a class field. -/
def MergeIdempotent (K : Type u) [m : MergeModel K] : Prop :=
  ∀ (c : m.MergeContext) (x : m.State), m.validContext c x x →
    m.observeResult (m.merge c x x) = m.observeState c x

/-- **The merge factors through observations**: the two replicas' *readings*
determine the merge. Trivially true whenever `observeState` is the identity —
so for the join model and the ancestral model alike — and **false** for
op-replay (§7.3), where two logs with the same view merge differently. This is
the precise sense in which an op-log merge "is not a binary join on views". -/
def ObservationalMerge (K : Type u) [m : MergeModel K] : Prop :=
  ∀ (c : m.MergeContext) (x y x' y' : m.State),
    m.validContext c x y → m.validContext c x' y' →
    m.observeState c x = m.observeState c x' →
    m.observeState c y = m.observeState c y' →
    m.observeResult (m.merge c x y) = m.observeResult (m.merge c x' y')

/-- **A model whose result is a state again.** Op-replay is not one: its result
is a view and there is no way back to the log. Associativity needs this to be
*typable* at all — `merge c (merge c x y) z` does not typecheck otherwise. -/
class Internal (K : Type u) [m : MergeModel K] where
  /-- Read the result back as a state. -/
  ofResult : m.MergeResult → m.State
  /-- …and reading it as a state agrees with reading it as a result. -/
  observe_ofResult : ∀ (c : m.MergeContext) (r : m.MergeResult),
    m.observeResult r = m.observeState c (ofResult r)

/-- **Associativity** — the third semilattice law, statable only for an
`Internal` model. The join model has it; nothing else here claims it. -/
def MergeAssociative (K : Type u) [m : MergeModel K] [i : Internal K] : Prop :=
  ∀ (c : m.MergeContext) (x y z : m.State),
    m.observeResult (m.merge c (i.ofResult (m.merge c x y)) z)
      = m.observeResult (m.merge c x (i.ofResult (m.merge c y z)))

/-- **A model whose context *is* a base state** — the MRDT/Git family.

⚠ The join model has no *canonical* one: its context is `Unit`, so a `Based`
instance would have to pick a distinguished state out of thin air, and
`MergeFastForward` at that state would be the claim that it is the lattice's
bottom. That is the whole difference: a three-way merge fast-forwards from
**every** base, and §7.1 is the theorem that no join on a two-state carrier
can. -/
class Based (K : Type u) [m : MergeModel K] where
  /-- The base the context names. -/
  baseOf : m.MergeContext → m.State

/-- **Fast-forward**: a replica that never left the base does not hold back one
that did. `Ancestral` §6 is the proof this is the load-bearing law — its two-way
form is refutable for *every* join on a state space with cyclic reachability
(`Ancestral.lock_no_update_preserving_join`). -/
def MergeFastForward (K : Type u) [m : MergeModel K] [b : Based K] : Prop :=
  ∀ (c : m.MergeContext) (y : m.State), m.validContext c (b.baseOf c) y →
    m.observeResult (m.merge c (b.baseOf c) y) = m.observeState c y

/-! ## §4. Instance (a) — the join CRDT

`MergeContext = Unit`, `MergeResult = State`, observation the identity, and the
laws are the semilattice. This is `Confluence.MergeState` with nothing added and
nothing taken away; §8 proves the judgement agrees on the nose. -/

/-- Tag for the join-CRDT model over `S`. -/
inductive JoinKey (S : Type u) where
  /-- The only inhabitant; the tag carries `S` as a parameter. -/
  | mk

/-- **The join model.** No context, result is a state, observation is the
state. -/
@[reducible] instance joinModel (S : Type u) [MergeState S] : MergeModel (JoinKey S) where
  State := S
  MergeContext := Unit
  MergeResult := S
  Observation := S
  merge _ x y := x ⊔ y
  validContext _ _ _ := True
  observeState _ s := s
  observeResult r := r
  contextObs _ := []

/-- The join model's result is a state — the identity. -/
@[reducible] instance joinInternal (S : Type u) [MergeState S] : Internal (JoinKey S) where
  ofResult r := r
  observe_ofResult _ _ := rfl

/-- The join is commutative — `MergeState.merge_comm`, at the observation
level. -/
theorem join_commutative (S : Type u) [MergeState S] : MergeCommutative (JoinKey S) :=
  fun _ x y _ => merge_comm x y

/-- The join is idempotent — `MergeState.merge_idem`. -/
theorem join_idempotent (S : Type u) [MergeState S] : MergeIdempotent (JoinKey S) :=
  fun _ x _ => merge_idem x

/-- The join is associative — `MergeState.merge_assoc`. All three semilattice
laws, supplied. -/
theorem join_associative (S : Type u) [MergeState S] : MergeAssociative (JoinKey S) :=
  fun _ x y z => merge_assoc x y z

/-- The join model's merge factors through observations, trivially: its
observation *is* its state. -/
theorem join_observational (S : Type u) [MergeState S] : ObservationalMerge (JoinKey S) := by
  intro _ x y x' y' _ _ hx hy
  have hx' : x = x' := hx
  have hy' : y = y' := hy
  show (x ⊔ y) = (x' ⊔ y')
  rw [hx', hy']

/-! ## §5. Instance (b) — the ancestral / MRDT merge

`MergeContext = the ancestor`. The result carries the triple it was reconciled
from, which is the evidence a three-way merge has and a join structurally
cannot: *which side moved*. The algebraic laws are `Ancestral.AncestralMerge`'s
two and no others — no associativity, no idempotence, no monotonicity (§7.2
refutes idempotence outright for the counter MRDT). -/

/-- A reconciled state, with the triple it came from. The three evidence fields
are why `MergeCommutative` is stated at the observation level: `left` and
`right` swap, and the merge is symmetric in what it *means*, not in what it
returns. -/
structure Reconciled (S : Type u) where
  /-- The reconciled state. -/
  state : S
  /-- The base it was reconciled against. -/
  base : S
  /-- The replica supplied first. -/
  left : S
  /-- The replica supplied second. -/
  right : S

/-- The three-way merge, packaged with its evidence. -/
def ancestralMerge {S : Type u} (M : AncestralMerge S) (l x y : S) : Reconciled S :=
  ⟨M.merge3 l x y, l, x, y⟩

/-- **The evidence is not decoration**: when it records that the left replica
never left the base, the reconciled state *is* the right replica — the merge
fast-forwarded. `AncestralMerge.fastforward`, read off the result. -/
theorem ancestralMerge_fastforward {S : Type u} (M : AncestralMerge S) (l y : S) :
    (ancestralMerge M l l y).state = (ancestralMerge M l l y).right :=
  M.fastforward l y

/-- Tag for the ancestral model determined by a three-way merge and the
implementation whose runs define reachability. -/
inductive AncestralKey {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op) where
  /-- The only inhabitant; the tag carries `M` and `impl` as parameters. -/
  | mk

/-- **The ancestral model.** The context is the ancestor; it is legitimate when
both replicas are reachable from it; and it exposes itself as an observation,
which is where `AncestralConfluent`'s `I l` hypothesis lives. -/
@[reducible] instance ancestralModel {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op) :
    MergeModel (AncestralKey M impl) where
  State := S
  MergeContext := S
  MergeResult := Reconciled S
  Observation := S
  merge l x y := ancestralMerge M l x y
  validContext l x y := Reachable impl l x ∧ Reachable impl l y
  observeState _ s := s
  observeResult r := r.state
  contextObs l := [l]

/-- The ancestral result is a state again — forget the evidence. -/
@[reducible] instance ancestralInternal {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op) :
    Internal (AncestralKey M impl) where
  ofResult r := r.state
  observe_ofResult _ _ := rfl

/-- The ancestral context *is* a base — this is the family fast-forward is
about. -/
@[reducible] instance ancestralBased {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op) :
    Based (AncestralKey M impl) where
  baseOf l := l

/-- Law one: `AncestralMerge.comm`. -/
theorem ancestral_commutative {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op) :
    MergeCommutative (AncestralKey M impl) :=
  fun l x y _ => M.comm l x y

/-- Law two: `AncestralMerge.fastforward` — and note the hypothesis it needs is
`validContext l l y`, i.e. `y` reachable from the base, which is what an
ancestor *is*. -/
theorem ancestral_fastForward {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op) :
    MergeFastForward (AncestralKey M impl) :=
  fun l y _ => M.fastforward l y

/-- The ancestral merge *does* factor through observations — its replicas are
its observations. This is what §7.3 separates op-replay from: the third model
fails this, and the first two do not. -/
theorem ancestral_observational {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op) :
    ObservationalMerge (AncestralKey M impl) := by
  intro l x y x' y' _ _ hx hy
  have hx' : x = x' := hx
  have hy' : y = y' := hy
  show (ancestralMerge M l x y).state = (ancestralMerge M l x' y').state
  rw [hx', hy']

/-! ## §6. Instance (c) — op-replay: the merge is a union of ops and a derived
view

The third shape, and the one that breaks the mould hardest: **the result is not
a state**. A replica holds a log; the merge unions the logs; what anyone reads
is a *materialized view*, a pure function of the union. `Move.lean` proves the
pattern's guarantee generically (`derived_view_sec`) and its price
(`view_not_stable`); `ExecRefine` proves both for the shipping kernel.

Two instances, because the family has an abstract member and a deployed one. -/

/-! ### §6.1 The abstract derived-view model -/

/-- Tag for the derived-view model over a log CRDT `L` read by `interp`. -/
inductive LogKey {L : Type u} {View : Type v} [MergeState L] (interp : L → View) where
  /-- The only inhabitant; the tag carries the interpreter as a parameter. -/
  | mk

/-- **The op-replay model, abstractly.** The context is the shared history; the
two replicas are logs; the result is the view of the union. `validContext` is
`True` — any log is a legitimate history, which is the pattern's whole appeal
and the reason its confluence is free. -/
@[reducible] instance logModel {L : Type u} {View : Type v} [MergeState L] (interp : L → View) :
    MergeModel (LogKey interp) where
  State := L
  MergeContext := L
  MergeResult := View
  Observation := View
  merge c x y := interp ((c ⊔ x) ⊔ y)
  validContext _ _ _ := True
  observeState c s := interp (c ⊔ s)
  observeResult r := r
  contextObs c := [interp c]

/-- **Law one is `derived_view_sec` clause (1)**: deltas arriving in either
order give the same view. `Move.derived_view_sec` states this when log and view
share a universe; the proof here is its three merge-law rewrites directly, so
the model may place its view in an independent universe. -/
theorem log_commutative {L : Type u} {View : Type v} [MergeState L] (interp : L → View) :
    MergeCommutative (LogKey interp) := by
  intro c x y _
  change interp ((c ⊔ x) ⊔ y) = interp ((c ⊔ y) ⊔ x)
  rw [merge_assoc, merge_comm x y, ← merge_assoc]

/-- **Law two is `derived_view_sec` clause (2)**: a redelivered delta changes
nothing. As above, the direct merge-law proof avoids coupling the view's
universe to the log's. -/
theorem log_idempotent {L : Type u} {View : Type v} [MergeState L] (interp : L → View) :
    MergeIdempotent (LogKey interp) := by
  intro c x _
  change interp ((c ⊔ x) ⊔ x) = interp (c ⊔ x)
  rw [merge_assoc, merge_idem]

/-- **…and clause (3) is confluence**: an invariant the interpreter enforces by
construction survives every merge, with no hypothesis on the replicas at all.
That is the derived-view pattern's bargain, in this file's judgement.

The price is not paid here and is not hidden: `Move.view_not_stable` shows the
view is **not stable** under log growth — an edit a user watched happen can be
un-happened by an older op arriving — so what this model buys in confluence it
spends in stability. -/
theorem log_iconfluentIn {L : Type u} {View : Type v} [MergeState L] (interp : L → View)
    (I : View → Prop) (henf : ∀ log, I (interp log)) :
    IConfluentIn (LogKey interp) I :=
  fun _ _ _ _ _ _ _ => henf _

/-- The move miniature, in the parameterized judgement: the cycle-skipping
replay keeps two-node acyclicity across every merge. `Move.miniInterp_acyclic`
is the enforcement obligation, discharged there. -/
theorem miniInterp_iconfluentIn :
    IConfluentIn (LogKey Move.miniInterp) Move.ViewAcyclic :=
  log_iconfluentIn Move.miniInterp Move.ViewAcyclic Move.miniInterp_acyclic

/-! ### §6.2 The shipping kernel

`Exec.absReplay` is the decision layer the Rust side links against. Here the
context is genuinely **not** a state: it is the weave's structural base
(`firstParent`), which no replica edits and which the log cannot express. The
observation carries that base beside the override block, because "is this view
acyclic" is a question about the pair (`ExecRefine.Reaches` reads both). -/

/-- Tag for the shipping-kernel op-replay model. -/
inductive ReplayKey where
  /-- The only inhabitant. -/
  | mk

/-- The kernel's observation: the structural base, and the override block
replayed over it. -/
abbrev KernelView : Type := Array Int × Array Int

/-- Reading a log: replay it over the base, and keep the base — "is this view
acyclic" is a question about the pair. -/
def kernelView (fp : Array Int) (a : Array Exec.Op) : KernelView :=
  (fp, Exec.absReplay fp a)

/-- The kernel's merge: the view of the concatenated logs. -/
def kernelMerge (fp : Array Int) (a b : Array Exec.Op) : KernelView :=
  kernelView fp (a ++ b)

/-- Acyclicity of a kernel view, as a predicate on the observation: no node
reaches itself through the effective-parent chain. -/
def KernelAcyclic (o : KernelView) : Prop := ∀ i, ¬ Exec.Reaches o.1 o.2 i i

/-- `ExecRefine.absReplay_append_comm`, on the merge. -/
theorem kernelMerge_comm (fp : Array Int) (a b : Array Exec.Op) :
    kernelMerge fp a b = kernelMerge fp b a := by
  unfold kernelMerge kernelView
  rw [Exec.absReplay_append_comm]

/-- Appending a log to itself adds no members, and
`ExecRefine.absReplay_append_mem` says the replay cannot see it. -/
theorem kernelMerge_idem (fp : Array Int) (a : Array Exec.Op) :
    kernelMerge fp a a = kernelView fp a := by
  unfold kernelMerge kernelView
  rw [Exec.absReplay_append_mem fp (fun _ hop => hop)]

/-- `ExecRefine.absReplay_ext_mem`, on the merge: only the union's membership
matters. -/
theorem kernelMerge_set (fp : Array Int) (a b a' b' : Array Exec.Op)
    (h : ∀ op, op ∈ (a ++ b).toList ↔ op ∈ (a' ++ b').toList) :
    kernelMerge fp a b = kernelMerge fp a' b' := by
  unfold kernelMerge kernelView
  rw [Exec.absReplay_ext_mem fp h]

/-- `ExecRefine.absReplay_acyclic`, on the merge. -/
theorem kernelMerge_acyclic (fp : Array Int) (a b : Array Exec.Op) (r : Nat → Nat)
    (hg : Exec.GroundedBase r fp) : KernelAcyclic (kernelMerge fp a b) :=
  Exec.absReplay_acyclic fp (a ++ b) r hg

/-- **The op-replay model, on the shipping kernel.** Merge = replay the
concatenated logs; `validContext` = the base is grounded, which is the
hypothesis every acyclicity theorem in `ExecRefine` carries. -/
@[reducible] instance replayModel : MergeModel ReplayKey where
  State := Array Exec.Op
  MergeContext := Array Int
  MergeResult := KernelView
  Observation := KernelView
  merge fp a b := kernelMerge fp a b
  validContext fp _ _ := ∃ r, Exec.GroundedBase r fp
  observeState fp a := kernelView fp a
  observeResult r := r
  contextObs fp := [kernelView fp #[]]

/-- Law one for the kernel: `ExecRefine.absReplay_append_comm`. -/
theorem replay_commutative : MergeCommutative ReplayKey :=
  fun fp a b _ => kernelMerge_comm fp a b

/-- Law two for the kernel: a redelivered log is invisible. -/
theorem replay_idempotent : MergeIdempotent ReplayKey :=
  fun fp a _ => kernelMerge_idem fp a

/-- **The kernel's characteristic law**: the merge is a function of the op
**set**. Logs agreeing on membership — any order, any duplication — merge to
the same view. This is `ExecRefine.absReplay_ext_mem` read as a law of the
model, and §7.3 is the other half of the sentence: a function of the set, and
*not* a function of the two views. -/
theorem replay_is_a_set_function (fp : Array Int) (x y x' y' : Array Exec.Op)
    (h : ∀ op, op ∈ (x ++ y).toList ↔ op ∈ (x' ++ y').toList) :
    (replayModel.merge fp x y) = (replayModel.merge fp x' y') :=
  kernelMerge_set fp x y x' y' h

/-- **Confluence for the shipping kernel, in the parameterized judgement**: over
a grounded base, the replay of any union of logs is acyclic.
`ExecRefine.absReplay_acyclic` does the work; `validContext` is exactly the
hypothesis it needs, which is what `validContext` is for. -/
theorem replay_iconfluentIn : IConfluentIn ReplayKey KernelAcyclic := by
  intro fp a b hv _ _ _
  obtain ⟨r, hg⟩ := hv
  exact kernelMerge_acyclic fp a b r hg

/-! ## §7. The three models are genuinely three

Every pair separated by a theorem rather than by taxonomy: §7.1 and §7.2 split
(a) from (b) twice — once at the merge, once at the laws — and §7.3 splits (c)
from both of the others at once. -/

/-! ### §7.1 (a) ≠ (b) — a join is a three-way merge only where nothing happens -/

/-- **No three-way merge on `Lock` computes the join.** Direct instantiation of
`Ancestral.join_is_ancestral_merge_iff_trivial`: an `AncestralMerge` that
ignored its ancestor and returned `x ⊔ y` would make fast-forward read
`l ⊑ y` for every pair, and antisymmetry would collapse the carrier — but
`Lock` has more than one state.

This is the theorem a mandatory `MergeState` slot would have contradicted: the
lock field would have had to present a join that is *provably* not its merge. -/
theorem no_ancestral_merge_on_lock_is_the_join (M : AncestralMerge Lock) :
    ¬ ∀ l x y : Lock, M.merge3 l x y = x ⊔ y := by
  intro h
  have htriv := (join_is_ancestral_merge_iff_trivial (S := Lock)).mp ⟨M, h⟩
  exact absurd (htriv ⟨true, false⟩ ⟨false, false⟩) (by decide)

/-- …and the same fact at the model level: for every three-way merge on `Lock`
there is a triple where the ancestral model's reading and the join model's
reading disagree. `ancestralMerge M` **is** `ancestralModel M impl`'s merge and
`⊔` **is** `joinModel Lock`'s, so this is the previous theorem said in the
class's own vocabulary. -/
theorem ancestral_model_differs_from_join_model (M : AncestralMerge Lock) :
    ∃ l x y : Lock, (ancestralMerge M l x y).state ≠ x ⊔ y := by
  apply Classical.byContradiction
  intro hcon
  exact no_ancestral_merge_on_lock_is_the_join M fun l x y =>
    Classical.byContradiction fun hne => hcon ⟨l, x, y, hne⟩

/-! ### §7.2 (b) has no semilattice — and not for want of trying

The MRDT counter of `Ancestral` §4 is `l + (a - l) + (b - l)`: merging a
replica with itself counts its delta **twice**. Idempotence is not merely
unproved for the ancestral model; it is false, at a reachable triple, for the
merge the literature supplies. -/

/-- ⚠ **The counter MRDT is not idempotent.** Ancestor `0`, replica `1` — one
locally admitted spend, so the context is legitimate — and the merge lands on
`2`. A class that made the semilattice laws mandatory would have excluded Sal
§2's counter from being a field kind at all. -/
theorem ancestral_not_idempotent :
    ¬ MergeIdempotent (AncestralKey counterAM (spendOps 1).impl) := by
  intro h
  have hg : (spendOps 1).guard () 0 = true := by decide
  have hr : Reachable (spendOps 1).impl 0 1 := (spendOps 1).reachable_step hg
  have hidem : counterAM.merge3 0 1 1 = 1 := h (0 : Nat) (1 : Nat) ⟨hr, hr⟩
  have hval : counterAM.merge3 0 1 1 = 2 := by
    show counterMerge 0 1 1 = 2
    unfold counterMerge; omega
  rw [hval] at hidem
  exact absurd hidem (by decide)

/-! ### §7.3 (c) ≠ (a), and (c) ≠ (b) — a function of the op set is not a
function of the views

Three real ops on the shipping kernel, over a two-node all-root base:

  * `opq` at t=2 — move node 0 under node 1;
  * `ops` at t=3 — move node 1 under node 0;
  * `opp` at t=4 — move node 0 under node 1 again.

The logs `#[opp]` and `#[opq, opp]` replay to the **same** view (node 0 under
node 1: the second grant re-applies the first's effect). Merge each with
`#[ops]` and they diverge: in the first, `ops` lands and `opp` is cycle-skipped;
in the second, `opq` lands first, `ops` is skipped instead, and `opp` re-applies.
Same two views in, different views out.

So no binary operation on views computes this merge — and by §6.2's
`replay_is_a_set_function` it is a function of the op *set* instead. Both of the
other models factor through their observations (`join_observational`,
`ancestral_observational`), so this one theorem separates the third shape from
both. That is the whole content of "an op-replay structure does not have a
join's signature". -/

/-- The miniature's structural base: two nodes, both at the root. -/
def kernelBase : Array Int := #[-1, -1]

/-- t = 2: move node 0 under node 1. -/
def opq : Exec.Op := ⟨2, 0, 0, 1, 0⟩
/-- t = 3: move node 1 under node 0. -/
def ops : Exec.Op := ⟨3, 0, 1, 0, 0⟩
/-- t = 4: move node 0 under node 1, again. -/
def opp : Exec.Op := ⟨4, 0, 0, 1, 0⟩

/-- An all-root base is grounded, by the constant rank: no first-parent edge is
present, so the descent obligation is vacuous. -/
theorem grounded_replicate (n : Nat) :
    Exec.GroundedBase (fun _ => 0) (Array.replicate n (-1)) := by
  intro i hi
  have h : (Array.replicate n (-1) : Array Int).getD i (-1) = -1 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  omega

/-- The two-node all-root base is grounded, so every context below is
legitimate. -/
theorem kernelBase_valid : ∃ r, Exec.GroundedBase r kernelBase :=
  ⟨fun _ => 0, grounded_replicate 2⟩

/- The four kernel values. Each replay is presented in sorted order — so
`List.mergeSort_of_pairwise` retires the sort — and the remaining fold is a
closed computation. -/

/-- Log `{opp}`: node 0 under node 1. -/
theorem replay_p : Exec.absReplay kernelBase #[opp] = #[1, -2] := by
  rw [Exec.absReplay_eq_foldl_mergeSort,
      show (#[opp] : Array Exec.Op).toList = [opp] from rfl,
      List.mergeSort_of_pairwise (le := Exec.opLe) (l := [opp]) (by decide)]
  decide

/-- Log `{opq, opp}`: the same view — the later grant re-applies the earlier
one's effect. -/
theorem replay_qp : Exec.absReplay kernelBase #[opq, opp] = #[1, -2] := by
  rw [Exec.absReplay_eq_foldl_mergeSort,
      show (#[opq, opp] : Array Exec.Op).toList = [opq, opp] from rfl,
      List.mergeSort_of_pairwise (le := Exec.opLe) (l := [opq, opp]) (by decide)]
  decide

/-- Log `{ops, opp}`: `ops` lands, and `opp` is skipped by the cycle rule. -/
theorem replay_sp : Exec.absReplay kernelBase #[ops, opp] = #[-2, 0] := by
  rw [Exec.absReplay_eq_foldl_mergeSort,
      show (#[ops, opp] : Array Exec.Op).toList = [ops, opp] from rfl,
      List.mergeSort_of_pairwise (le := Exec.opLe) (l := [ops, opp]) (by decide)]
  decide

/-- Log `{opq, ops, opp}`: now `opq` lands first, `ops` is the one skipped, and
`opp` re-applies. -/
theorem replay_qsp : Exec.absReplay kernelBase #[opq, ops, opp] = #[1, -2] := by
  rw [Exec.absReplay_eq_foldl_mergeSort,
      show (#[opq, ops, opp] : Array Exec.Op).toList = [opq, ops, opp] from rfl,
      List.mergeSort_of_pairwise (le := Exec.opLe) (l := [opq, ops, opp]) (by decide)]
  decide

/-- The first merge, in the model's own shape (`a ++ b`, reordered by
`absReplay_perm` — the replay is blind to delivery order). -/
theorem replay_merge_p_s : Exec.absReplay kernelBase (#[opp] ++ #[ops]) = #[-2, 0] := by
  rw [Exec.absReplay_perm kernelBase (b := #[ops, opp])
      (by rw [Array.toList_append]; exact List.Perm.swap ops opp [])]
  exact replay_sp

/-- The second merge. -/
theorem replay_merge_qp_s :
    Exec.absReplay kernelBase (#[opq, opp] ++ #[ops]) = #[1, -2] := by
  rw [Exec.absReplay_perm kernelBase (b := #[opq, ops, opp])
      (by rw [Array.toList_append]; exact (List.Perm.swap ops opp []).cons opq)]
  exact replay_qsp

/-- ⚠ **The op-replay merge is not a function of the replicas' views.** Two logs
with an identical view merge with a third log to different views — so no binary
operation on views computes it, and the op-replay model cannot be presented as a
join on what anyone reads.

Both contexts are legitimate (the base is grounded), so this is not a
counterexample that a validity filter removes. -/
theorem replay_not_observational : ¬ ObservationalMerge ReplayKey := by
  intro h
  have hobs : kernelView kernelBase #[opp] = kernelView kernelBase #[opq, opp] := by
    unfold kernelView
    rw [replay_p, replay_qp]
  have hbad : kernelMerge kernelBase #[opp] #[ops]
      = kernelMerge kernelBase #[opq, opp] #[ops] :=
    h kernelBase #[opp] #[ops] #[opq, opp] #[ops]
      kernelBase_valid kernelBase_valid hobs rfl
  have h1 : kernelMerge kernelBase #[opp] #[ops] = (kernelBase, #[-2, 0]) := by
    unfold kernelMerge kernelView
    rw [replay_merge_p_s]
  have h2 : kernelMerge kernelBase #[opq, opp] #[ops] = (kernelBase, #[1, -2]) := by
    unfold kernelMerge kernelView
    rw [replay_merge_qp_s]
  rw [h1, h2] at hbad
  exact absurd (congrArg Prod.snd hbad) (by decide)

/-! ### §7.4 The three, side by side -/

/-- **The generalization was forced.** Every pair of models is separated by a
theorem, and no pair is separated by taste:

  * (a) vs (b) — no three-way merge on `Lock` is the join
    (`Ancestral.join_is_ancestral_merge_iff_trivial`, instantiated); and again
    from the law side, the MRDT counter is *refutably* non-idempotent, so the
    semilattice cannot be demanded of the ancestral model;
  * (a) vs (c) and (b) vs (c) — the op-replay merge factors through the op set
    and provably **not** through the views, while both of the others factor
    through the views by construction.

A `MergeModel` class fixed to any one of these shapes would have had to state
something false about the other two. -/
theorem three_models_are_genuinely_different :
    (∀ M : AncestralMerge Lock, ¬ ∀ l x y : Lock, M.merge3 l x y = x ⊔ y)
    ∧ ¬ MergeIdempotent (AncestralKey counterAM (spendOps 1).impl)
    ∧ ObservationalMerge (JoinKey (GSet Nat))
    ∧ ObservationalMerge (AncestralKey lockAM lockImpl)
    ∧ ¬ ObservationalMerge ReplayKey :=
  ⟨no_ancestral_merge_on_lock_is_the_join, ancestral_not_idempotent,
   join_observational (GSet Nat), ancestral_observational lockAM lockImpl,
   replay_not_observational⟩

/-! ## §8. The agreement — two judgements become one

This is the deliverable's value: `IConfluent` and `AncestralConfluent` are not
merely *analogous* to `IConfluentIn`; each **is** it, at its model, as an `Iff`
that only shuffles hypotheses — no content is reproved in either direction.
Nothing is redefined either: `Confluence.lean` and `Ancestral.lean` are
untouched, and every existing theorem about them transports through these two
lemmas. -/

/-- **`IConfluent` is the join-model instance.** The join model's context is
`Unit`, its validity is `True`, and it exposes no context observations — so the
generalized judgement is the original one with three trivial hypotheses. -/
theorem iconfluentIn_join_iff (S : Type u) [MergeState S] (I : Invariant S) :
    IConfluentIn (JoinKey S) I ↔ IConfluent I :=
  ⟨fun h x y hx hy => h () x y trivial (by intro _ ho; cases ho) hx hy,
   fun h _ x y _ _ hx hy => h x y hx hy⟩

/-- **`Ancestral.AncestralConfluent` is the ancestral-model instance.** The
context is the ancestor, `contextObs` supplies `I l`, and `validContext`
supplies the two reachability hypotheses. Same predicate, same quantifiers. -/
theorem iconfluentIn_ancestral_iff {S : Type u} {Op : Type v} (M : AncestralMerge S)
    (impl : Impl S Op) (I : Invariant S) :
    IConfluentIn (AncestralKey M impl) I ↔ AncestralConfluent M impl I :=
  ⟨fun h l x y hl hx hy hrx hry =>
      h l x y ⟨hrx, hry⟩ (by intro o ho; cases ho with
        | head => exact hl
        | tail _ ht => cases ht) hx hy,
   fun h l x y hv hc hx hy => h l x y (hc l List.mem_cons_self) hx hy hv.1 hv.2⟩

/-- The catalog's workhorse, transported: "contains `a`" is confluent in the
join model. -/
theorem gset_mem_iconfluentIn {α : Type} (a : α) :
    IConfluentIn (JoinKey (GSet α)) (fun s : GSet α => s a = true) :=
  (iconfluentIn_join_iff (GSet α) _).mpr (gset_mem_iconfluent a)

/-- The prize of `Ancestral` §5, transported: mutual exclusion under hand-off is
confluent in the ancestral model. -/
theorem lock_iconfluentIn :
    IConfluentIn (AncestralKey lockAM lockImpl) AtMostOne :=
  (iconfluentIn_ancestral_iff lockAM lockImpl AtMostOne).mpr lock_ancestral_confluent

/-- **`Ancestral` §8's incomparability, as four clauses about one predicate.**
The two judgements it set side by side are now the same judgement at two
models, and the result reads as what it always was: the *model* decides, and
neither model dominates.

  * a ceiling is confluent in the join model and **not** in the ancestral one
    (the join bought its verdict by dropping a committed operation —
    `Ancestral.join_not_serializing`);
  * mutual exclusion under hand-off is **not** confluent in the join model and
    is confluent in the ancestral one. -/
theorem incomparable_in_one_judgement :
    IConfluentIn (JoinKey Nat) (fun n : Nat => n ≤ 1)
    ∧ ¬ IConfluentIn (AncestralKey counterAM (spendOps 1).impl) (fun n : Nat => n ≤ 1)
    ∧ ¬ IConfluentIn (JoinKey Lock) AtMostOne
    ∧ IConfluentIn (AncestralKey lockAM lockImpl) AtMostOne :=
  ⟨(iconfluentIn_join_iff Nat _).mpr (ceiling_iconfluent 1),
   fun h => ceiling_not_ancestral 0
     ((iconfluentIn_ancestral_iff counterAM (spendOps 1).impl _).mp h),
   fun h => lock_not_iconfluent ((iconfluentIn_join_iff Lock AtMostOne).mp h),
   lock_iconfluentIn⟩

/-! ## §9. The third case a binary interface cannot express

A merge-base procedure does not return a node. It returns **selected**,
**ambiguous** (two maximal common bases, so no lowest one exists) or
**unavailable** — minidregg's `BaseDecision`, whose `unavailableOfAbsent` makes
absence a proof obligation. That shape needs two things a binary `MergeState`
has nowhere to put: a context that is not a state, and a validity condition on
that context which is *about the specific pair being merged*.

Both are `MergeModel` fields already. `validContext` is where "no common base
exists **for these two replicas**" is discharged — as a refutation, not a
flag. -/

/-- **A merge-base procedure's honest output.** Not `Option S`: two maximal
common bases is a different answer from none, and the merge behaves differently
under it (`base_decision_is_observable`). -/
inductive BaseDecision (S : Type u) where
  /-- A single base was selected. -/
  | selected (base : S)
  /-- Two distinct common bases were found and could not be ordered. -/
  | ambiguous (b₁ b₂ : S)
  /-- No common base at all. -/
  | unavailable

/-- **When a base decision is legitimate for this pair** — and this is the whole
point of the case split. `selected` and `ambiguous` must *exhibit* their bases
as ancestors of both replicas (and ambiguity must exhibit two distinct ones);
`unavailable` must **refute** the existence of any. Nothing here is a flag a
caller sets.

⟨UNDONE⟩ `ambiguous` demands two *distinct* common bases and not a proof that
no lowest one exists: uwueave has no `LowestCommonBase`, and minidregg's
`AmbiguousCommonBases.excludes_lowest` is that theorem, next door. Two distinct
common bases is what a merge-base procedure can hand us here, and
`ambiguous_inhabited` shows the situation is real. -/
def BaseDecision.Valid {S : Type u} {Op : Type v} (impl : Impl S Op) :
    BaseDecision S → S → S → Prop
  | .selected l, x, y => Reachable impl l x ∧ Reachable impl l y
  | .ambiguous b₁ b₂, x, y =>
      (Reachable impl b₁ x ∧ Reachable impl b₁ y)
        ∧ (Reachable impl b₂ x ∧ Reachable impl b₂ y) ∧ b₁ ≠ b₂
  | .unavailable, x, y => ¬ ∃ b, Reachable impl b x ∧ Reachable impl b y

/-- The bases a decision names — none, one, or two. This is `contextObs`: the
observations a judgement may assume legal, because they are states the system
committed. `unavailable` supplies nothing, which is correct and is the reason
the invariant must be kept by the *policy* in that case. -/
def BaseDecision.bases {S : Type u} : BaseDecision S → List S
  | .selected l => [l]
  | .ambiguous b₁ b₂ => [b₁, b₂]
  | .unavailable => []

/-- A state decided under a base decision, with the decision kept as evidence:
a reader can tell a fast-forward from a policy call made blind. -/
structure Decided (S : Type u) where
  /-- The decided state. -/
  state : S
  /-- The decision it was computed under. -/
  under : BaseDecision S
  /-- The replica supplied first. -/
  left : S
  /-- The replica supplied second. -/
  right : S

/-- **The merge under a base decision.** With a base, the three-way merge. With
two, or with none, there is no fast-forward to be had — a replica that did not
move is indistinguishable from one that did — so the conflict-resolution policy
decides. -/
def decidedMerge {S : Type u} (M : AncestralMerge S) (resolve : S → S → S) :
    BaseDecision S → S → S → Decided S
  | .selected l, x, y => ⟨M.merge3 l x y, .selected l, x, y⟩
  | .ambiguous b₁ b₂, x, y => ⟨resolve x y, .ambiguous b₁ b₂, x, y⟩
  | .unavailable, x, y => ⟨resolve x y, .unavailable, x, y⟩

/-- Tag for the base-decision model. -/
inductive DecisionKey {S : Type u} {Op : Type v} (M : AncestralMerge S) (impl : Impl S Op)
    (resolve : S → S → S) where
  /-- The only inhabitant; the tag carries the merge, the implementation and the
  fallback policy. -/
  | mk

/-- **The base-decision model.** `MergeContext = BaseDecision S` — a context
that is *not* a state, and could not be one. -/
@[reducible] instance decisionModel {S : Type u} {Op : Type v}
    (M : AncestralMerge S) (impl : Impl S Op)
    (resolve : S → S → S) : MergeModel (DecisionKey M impl resolve) where
  State := S
  MergeContext := BaseDecision S
  MergeResult := Decided S
  Observation := S
  merge c x y := decidedMerge M resolve c x y
  validContext c x y := c.Valid impl x y
  observeState _ s := s
  observeResult r := r.state
  contextObs c := c.bases

/-- ⚠ **The three cases are observably different.** On the very triple that
busts the two-way join — ancestor "Alice holds", one replica handed the lock to
Bob, the other did nothing — a *selected* base fast-forwards to "Bob holds",
while the *ambiguous* branch has no fast-forward available and the priority
policy hands it back to Alice.

So the third value is not bookkeeping. A binary interface that reduced the
decision to "a base or nothing" would have to pick one of these two answers for
both cases, and it would be wrong about the other. -/
theorem base_decision_is_observable :
    (decidedMerge lockAM lockPriority (.selected ⟨true, false⟩)
      ⟨false, true⟩ ⟨true, false⟩).state
    ≠ (decidedMerge lockAM lockPriority (.ambiguous ⟨true, false⟩ ⟨false, true⟩)
      ⟨false, true⟩ ⟨true, false⟩).state := by decide

/-! ### §9.1 All three cases are inhabited — the split is not decoration

A case nothing can satisfy is a case a reader trusts for nothing. Each of the
three is exhibited, and `unavailable` is exhibited the hard way: with a genuine
refutation of every common base. -/

/-- The implementation that admits nothing: every operation aborts. Its
reachability is equality, which is what makes two distinct replicas genuinely
base-less. -/
def noOps (S : Type u) (Op : Type v) : Impl S Op := ⟨fun _ _ => none⟩

/-- Under `noOps` nothing moves: reachable implies equal. -/
theorem noOps_reachable {S : Type u} {Op : Type v} {b x : S}
    (h : Reachable (noOps S Op) b x) :
    b = x := by
  obtain ⟨ops, hr⟩ := h
  cases ops with
  | nil => exact Option.some.inj hr
  | cons op rest => simp [RunsTo, run, noOps] at hr

/-- `selected` is inhabited: Alice holds the lock, one replica hands it to Bob,
the other does nothing. -/
theorem selected_inhabited :
    (BaseDecision.selected (⟨true, false⟩ : Lock)).Valid lockImpl
      ⟨false, true⟩ ⟨true, false⟩ :=
  ⟨⟨[LockOp.grantBob], rfl⟩, ⟨[], rfl⟩⟩

/-- `ambiguous` is inhabited: "Alice holds" and "Bob holds" are two distinct
common bases of the released state — each replica gets there by one `release`.

Note *why* neither is "the lowest": under a replacement operation each of these
two reaches the other (`Ancestral` §6's cycle, the same one that defeats every
update-preserving join), so there is no order in which one of them is lower.
"Lowest" is not a well-defined selection here at all, which is exactly the
situation a three-valued answer exists for. -/
theorem ambiguous_inhabited :
    (BaseDecision.ambiguous (⟨true, false⟩ : Lock) ⟨false, true⟩).Valid lockImpl
      ⟨false, false⟩ ⟨false, false⟩ :=
  ⟨⟨⟨[LockOp.release], rfl⟩, ⟨[LockOp.release], rfl⟩⟩,
   ⟨⟨[LockOp.release], rfl⟩, ⟨[LockOp.release], rfl⟩⟩, by decide⟩

/-- `unavailable` is inhabited **with a proof of absence**, not a flag: under an
implementation that admits no operation, two distinct replicas have no common
ancestor at all, and the refutation is the content of the case. -/
theorem unavailable_inhabited :
    (BaseDecision.unavailable (S := Lock)).Valid (noOps Lock LockOp)
      ⟨true, false⟩ ⟨false, true⟩ := by
  rintro ⟨b, hx, hy⟩
  have h1 := noOps_reachable hx
  have h2 := noOps_reachable hy
  exact absurd (h1.symm.trans h2) (by decide)

/-- **Mutual exclusion survives every base decision.** Selected, ambiguous or
unavailable: the invariant holds. `Ancestral.lock_merge_atMostOne` covers the
first with no hypothesis on the ancestor at all, and `lockPriority_atMostOne`
covers the other two — the priority policy names at most one holder by
construction.

Read as the design statement it is: a merge-base procedure that finds two
candidate bases, or none at all, cannot break mutual exclusion here. Safety does
not rest on the base being *the* lowest one — which is the property that makes a
three-valued answer safe to give. -/
theorem lock_decision_iconfluentIn :
    IConfluentIn (DecisionKey lockAM lockImpl lockPriority) AtMostOne := by
  intro c x y _ _ hx hy
  cases c with
  | selected l => exact lock_merge_atMostOne l x y hx hy
  | ambiguous _ _ => exact lockPriority_atMostOne x y
  | unavailable => exact lockPriority_atMostOne x y

end MergeModel

end Uwueave
