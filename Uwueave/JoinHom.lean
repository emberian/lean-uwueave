/-
# Uwueave.JoinHom — monotone is not join-preserving, and what the difference costs.

**This file exists because an external reviewer (codex) read `FORCODEX.md` §4.1
and caught a real defect in its reasoning.** The memo wrote:

> hole-filling is monotone, so the space of partial results is itself a
> join-semilattice. That last clause is why every piece of machinery in this
> repo transfers from data to computation **unchanged**.

Two different properties are being run together there. "Hole-filling is
monotone" is a statement about `⊑`; "the machinery transfers unchanged" needs
the *equation* `f (x ⊔ y) = f x ⊔ f y`. Monotonicity is strictly weaker, and the
gap is not a technicality — it is exactly the difference between the two
architectures a replicated system can pick (§5).

Codex's counterexample, formalised here as `monotone_not_joinHom`: over finite
sets under union, `f X = |X|` is monotone, and it is **not** a join
homomorphism. `f ({a} ∪ {b}) = 2` while merging the two local counts by `max`
gives `1`; merging by `+` gets that pair right and then fails on
`{a} ∪ {a}` — `2` against a truth of `1`. And the sharp form
(`no_count_merge_without_provenance`): **no** binary function on the two raw
counts can be exact, because the input pair `(1, 1)` must answer `1` when the
replicas saw the same element and `2` when they saw different ones. A count
that has forgotten *which* element it counted cannot be merged at all.

## What was, and was not, wrong

`Holes.evalSet_hom` — the headline of `Holes.lean` — **was already a genuine
join homomorphism and remains one**: `evalSet` takes the *image* of a candidate
set, and images distribute over unions (∃ distributes over ∨, which is what its
proof says). Nothing there needed repair, and `evalSet_joinHom` below restates
it in this file's vocabulary precisely to keep that on the record. The defect
was in the **prose**: the word "unchanged", and the licence it silently gave to
replicate *computed summaries* rather than evidence. `evalSet` earns that
licence by a theorem; `card` does not have it; and the memo's sentence, read as
written, hands it to every monotone computation.

## The correction, in four parts

  1. `JoinHom` and `MonotoneLeq` are separate properties;
     `joinHom_implies_monotone` runs one way and `monotone_not_joinHom` blocks
     the other, concretely, over `GSet Bool` with `Nat`-under-max as the
     summary lattice.
  2. **Provenance is forced, not merely convenient.**
     `no_count_merge_without_provenance` quantifies over *every*
     `m : Nat → Nat → Nat`; `card_not_incrementallyMergeable` says the same
     thing in the vocabulary of §6; and `count_summary_must_distinguish` shows
     that any join-homomorphic summary through which the count factors must
     already tell `{a}` from `{b}` — i.e. it must carry the evidence.
  3. **The transport that survives is the pullback along a hom**
     (`iconfluent_pullback_of_joinHom`). ⚠ A pullback along a merely *monotone*
     map is **not** free: `monotone_pullback_can_fail` exhibits an I-confluent
     result invariant (`n ≤ 1`) whose pullback along the monotone `card` is not
     I-confluent. What *is* free without any homomorphism is the pullback of an
     **upward-closed** result invariant along any monotone summary
     (`iconfluent_pullback_of_monotone`): "the count is at least `k`" transfers
     for free, "at most `k`" does not. So the honest statement is not "lifting a
     result invariant back to the source is always available" — it is available
     for free exactly when the invariant is upward-closed, and otherwise it
     costs a homomorphism.
  4. **Two architectures, named** (§5). (i) *Replicate evidence and recompute
     the view* — `ReplicatesEvidence`, a theorem for **every** interpreter with
     no hypothesis at all (`evidence_architecture_is_free`, which is
     `Move.derived_view_sec` with the invariant clause dropped). (ii)
     *Replicate computed summaries* — `SummaryFoldAgrees`, which
     `summaryFold_iff_joinHom` proves correct **exactly** when the summary is a
     `JoinHom`. Not "needs": iff.

§6 is codex's proposed **fourth verdict**, beside the memo's three
(deterministic? coordination-free? does my invariant survive?):

> **is this computation incrementally mergeable from its results, or must it
> retain and replay source evidence?**

`IncrementallyMergeable f` asks for *some* combiner `m` with
`f (x ⊔ y) = m (f x) (f y)` — deliberately weaker than `JoinHom`, since it does
not fix the combiner and asks nothing of it (no commutativity, no idempotence).
`incrementallyMergeable_iff_resultDetermined` says the verdict is exactly
"is the merged result a function of the two results", and five computations are
classified against it (§6.2): images, high-water marks, existential reads and
filtered views answer `fromResults`; counting answers `needsEvidence`.

## Honest boundary

  * **The witness carrier is two-element.** ⟨TERMINAL for the refutation⟩ A
    counterexample only needs to be a counterexample; `GSet Bool` with the two
    replicas `sawA` / `sawB` is the smallest carrier on which the count clash
    exists, and every impossibility here bottoms out in `decide` on it. The
    *positive* results (§1–§3, §5, §6.1) are general and carry no carrier
    assumption.
  * **`IncrementallyMergeable` says nothing about cost.** ⟨UNDONE⟩ It asks for a
    combiner to exist, not for it to be cheap, small or shippable — the
    `canonicalCombine` witnessing the ⟸ direction of
    `incrementallyMergeable_iff_resultDetermined` is built from
    `Classical.choice` and is not an algorithm. A verdict that also priced the
    combiner is what an implementation would want and is not here.
  * **The general judgement remains semantic; a typed fragment now has a
    classifier.** ⟨DONE for `Preo.Expr`, terminal for arbitrary `f`⟩
    `Preo.DerivedProgram.preservesMerge_iff_joinHom` identifies the expression
    equation with this `JoinHom`, and `Preo.Expr.certifyMergeSafe` recursively
    produces proofs for its safe fragment while refusing negation, addition,
    malformed syntax, and unproved custom nodes. No total classifier for an
    arbitrary Lean function is possible or claimed.
  * **The provenance theorem is about one summary shape.**
    `count_summary_must_distinguish` shows a join-homomorphic summary computing
    the count must separate `sawA` from `sawB`; it does not characterise the
    *least* such summary. `Uwueave.MinimalSummary` now answers the adjacent
    semantic question: contextual equivalence constructs the coarsest
    future-sufficient partition for a declared query, with exact membership,
    count, and threshold examples. It does not prove a minimum-bit encoding,
    reachable-context minimum, or cheap implementation, so those cost questions
    remain outside this file.

Literature: the join-homomorphism/monotone distinction is standard lattice
theory; its CRDT-facing form is Shapiro et al.'s requirement that a *derived*
value be computed by a lattice morphism, and its database-facing form is why
aggregate maintenance ships provenance (counting Bloom filters, PN-counters,
`COUNT DISTINCT` sketches) rather than a bare count.
-/
import Uwueave.Holes
import Uwueave.Move

namespace Uwueave

open Uwueave.Catalog

universe u v

/-! ## §1. The two properties.

`MergeState` gives every carrier a join and an induced order (`Leq`, `⊑`). A
function between two such carriers can respect the *order* or respect the
*operation*, and these are different asks. -/

/-- **A join homomorphism**: computing after the merge equals merging after the
computation. This is the equation `Holes.evalSet_hom` establishes for the image
of a candidate set, and the one the design memo's "transfers unchanged" was
silently assuming for every computation. -/
def JoinHom {S : Type u} {R : Type v} [MergeState S] [MergeState R]
    (f : S → R) : Prop :=
  ∀ x y : S, f (x ⊔ y) = f x ⊔ f y

/-- **Monotone for the induced order**: learning more never moves the result
down. Every CRDT-shaped computation people call "monotone" means this. -/
def MonotoneLeq {S : Type u} {R : Type v} [MergeState S] [MergeState R]
    (f : S → R) : Prop :=
  ∀ x y : S, x ⊑ y → f x ⊑ f y

/-- A join homomorphism is monotone: rewrite the merge and use `x ⊔ y = y`. One
line, and it is the *only* direction that holds — `JoinHom.monotone_not_joinHom`
refutes the converse with a concrete pair. -/
theorem joinHom_implies_monotone {S : Type u} {R : Type v}
    [MergeState S] [MergeState R] {f : S → R} (h : JoinHom f) : MonotoneLeq f := by
  intro x y hxy
  show f x ⊔ f y = f y
  rw [← h, hxy]

/-! ## §2. Transport of the judgement — what a hom buys, and what monotonicity
does not.

`Confluence.lean`'s whole judgement is stated on a carrier. A computation moves
a state to a result, so the question is which invariants on *results* come back
as invariants on *sources*. -/

/-- **The honest transport.** An I-confluent invariant on results pulls back to
an I-confluent invariant on sources **along a join homomorphism**. This is
`Holes.result_invariant_transfers` with `evalSet` replaced by its defining
property, and it is the general form of what that theorem proves. -/
theorem iconfluent_pullback_of_joinHom {S : Type u} {R : Type v}
    [MergeState S] [MergeState R] {f : S → R} (hf : JoinHom f)
    {J : Invariant R} (hJ : IConfluent J) :
    IConfluent (fun s => J (f s)) := by
  intro x y hx hy
  show J (f (x ⊔ y))
  rw [hf]
  exact hJ _ _ hx hy

/-- An invariant closed **upward** in the induced order: if it holds of a state
it holds of everything that knows more. `Catalog.gset_monotone_iconfluent` is
this notion at the G-Set. -/
def UpClosed {R : Type v} [MergeState R] (J : Invariant R) : Prop :=
  ∀ x y : R, x ⊑ y → J x → J y

/-- An upward-closed invariant is I-confluent — the merge is above both
replicas, so it inherits either one's legality. -/
theorem upClosed_iconfluent {R : Type v} [MergeState R] {J : Invariant R}
    (hJ : UpClosed J) : IConfluent J :=
  fun x y hx _ => hJ x (x ⊔ y) (le_merge_left x y) hx

/-- **What is free without any homomorphism.** An *upward-closed* result
invariant pulls back along a merely **monotone** computation, with no equation
on `f` at all: the merge knows at least what `x` knew, so the result of the
merge is at least `f x`, and upward-closure finishes it.

This is the true reading of "lifting a result invariant back to source state is
always available" — it is available for lower bounds, thresholds, "has at least
these members", "the count is at least `k`". It is **not** available in general:
see `JoinHom.monotone_pullback_can_fail`, where a ceiling on the same monotone
`card` breaks. -/
theorem iconfluent_pullback_of_monotone {S : Type u} {R : Type v}
    [MergeState S] [MergeState R] {f : S → R} (hf : MonotoneLeq f)
    {J : Invariant R} (hJ : UpClosed J) :
    IConfluent (fun s => J (f s)) :=
  fun x y hx _ => hJ (f x) (f (x ⊔ y)) (hf x (x ⊔ y) (le_merge_left x y)) hx

/-! ## §3. Incremental mergeability — the weakest honest form of "ship the
answer".

`JoinHom` fixes the combiner to be `R`'s own join. A system that ships summaries
is free to merge them with *any* function it likes, so the property that
actually decides the architecture is weaker: does **some** binary combiner on
results reconstruct the merged result? -/

/-- **Incrementally mergeable from its results.** Some binary combiner on
results computes the result of the merge. Deliberately weak: `m` is not asked to
be commutative, associative, idempotent, or to be `R`'s join — the negative
result below (`JoinHom.card_not_incrementallyMergeable`) is therefore an
impossibility over *every* combiner, not a complaint about one. -/
def IncrementallyMergeable {S : Type u} {R : Type v} [MergeState S]
    (f : S → R) : Prop :=
  ∃ m : R → R → R, ∀ x y : S, f (x ⊔ y) = m (f x) (f y)

/-- The negative side of the same coin: this computation cannot be merged from
its results, so a replica must retain — and a peer must replay — source
evidence. -/
def RequiresEvidence {S : Type u} {R : Type v} [MergeState S]
    (f : S → R) : Prop :=
  ¬ IncrementallyMergeable f

/-- A join homomorphism is incrementally mergeable: take the combiner to be the
result lattice's own join. -/
theorem joinHom_incrementallyMergeable {S : Type u} {R : Type v}
    [MergeState S] [MergeState R] {f : S → R} (hf : JoinHom f) :
    IncrementallyMergeable f :=
  ⟨fun a b => a ⊔ b, hf⟩

/-- **The results determine the merged result.** Two source states that produce
equal results are interchangeable as far as the merged result is concerned —
i.e. the results have not forgotten anything the merge needs. -/
def ResultDetermined {S : Type u} {R : Type v} [MergeState S]
    (f : S → R) : Prop :=
  ∀ x y x' y' : S, f x = f x' → f y = f y' → f (x ⊔ y) = f (x' ⊔ y')

/-- Mergeable-from-results implies the results determine the merge: the combiner
only ever sees the results. -/
theorem resultDetermined_of_incrementallyMergeable {S : Type u} {R : Type v}
    [MergeState S] {f : S → R} (h : IncrementallyMergeable f) :
    ResultDetermined f := by
  obtain ⟨m, hm⟩ := h
  intro x y x' y' hx hy
  rw [hm, hm, hx, hy]

open Classical in
/-- The combiner built from `ResultDetermined`: pick *any* pair of source states
with the given results and merge them. Classical and not an algorithm — it
witnesses the ⟸ direction of `incrementallyMergeable_iff_resultDetermined` and
nothing more (see the boundary note on cost). -/
noncomputable def canonicalCombine {S : Type u} {R : Type v} [MergeState S]
    [Inhabited R] (f : S → R) (r₁ r₂ : R) : R :=
  if h : ∃ p : S × S, f p.1 = r₁ ∧ f p.2 = r₂ then f (h.choose.1 ⊔ h.choose.2)
  else default

/-- Result-determinacy is enough: `canonicalCombine` picks an arbitrary
preimage pair, and `ResultDetermined` says the choice does not matter. -/
theorem incrementallyMergeable_of_resultDetermined {S : Type u} {R : Type v}
    [MergeState S] [Inhabited R] {f : S → R} (h : ResultDetermined f) :
    IncrementallyMergeable f := by
  refine ⟨canonicalCombine f, fun x y => ?_⟩
  have hex : ∃ p : S × S, f p.1 = f x ∧ f p.2 = f y := ⟨(x, y), rfl, rfl⟩
  show f (x ⊔ y) = canonicalCombine f (f x) (f y)
  unfold canonicalCombine
  rw [dif_pos hex]
  exact (h hex.choose.1 hex.choose.2 x y hex.choose_spec.1 hex.choose_spec.2).symm

/-- **The fourth verdict, characterised.** A computation is mergeable from its
results **exactly** when the merged result is a function of the two results —
i.e. exactly when the results carry every distinction the merge is sensitive to.
Read the failure direction and you have the shape of every provenance
requirement: `JoinHom.no_count_merge_without_provenance` is this iff, refuted at
`card`, by exhibiting two source pairs with equal results and different merged
results. -/
theorem incrementallyMergeable_iff_resultDetermined {S : Type u} {R : Type v}
    [MergeState S] [Inhabited R] (f : S → R) :
    IncrementallyMergeable f ↔ ResultDetermined f :=
  ⟨resultDetermined_of_incrementallyMergeable,
   incrementallyMergeable_of_resultDetermined⟩

namespace JoinHom

open Uwueave.Catalog

/-! ## §4. THE SEPARATING WITNESS — counting.

Two replicas over a two-element universe (`Bool`, with `false` playing codex's
`a` and `true` playing his `b`). Each holds a one-element grow-only set. Each
computes a local count. The counts are equal — `1` and `1` — and the merged
count is `1` or `2` depending on a fact the counts do not contain. -/

/-- The indicator of a `Bool`, as a `Nat`. -/
def bit (b : Bool) : Nat := if b then 1 else 0

/-- Cardinality over the two-element universe: the computation codex named. -/
def card (s : GSet Bool) : Nat := bit (s false) + bit (s true)

/-- The replica that saw element `a` (encoded `false`), and nothing else. -/
def sawA : GSet Bool := fun b => !b

/-- The replica that saw element `b` (encoded `true`), and nothing else. -/
def sawB : GSet Bool := fun b => b

theorem card_sawA : card sawA = 1 := by decide

theorem card_sawB : card sawB = 1 := by decide

/-- Two replicas that saw **different** elements: the merged count is `2`. -/
theorem card_merge_diff : card (sawA ⊔ sawB) = 2 := by decide

/-- Two replicas that saw the **same** element: the merged count is `1`. Union
is idempotent; addition is not. -/
theorem card_merge_same : card (sawA ⊔ sawA) = 1 := by decide

/-- Monotonicity, pointwise: a `Bool` that implies another has a smaller
indicator. -/
theorem bit_le : ∀ {b c : Bool}, (b = true → c = true) → bit b ≤ bit c
  | false, _,     _ => Nat.zero_le _
  | true,  true,  _ => Nat.le_refl _
  | true,  false, h => absurd (h rfl) (by decide)

/-- Counting is monotone under inclusion — the sum of two pointwise
inequalities. -/
theorem card_le_of_subset {x y : GSet Bool} (h : ∀ a, x a = true → y a = true) :
    card x ≤ card y :=
  Nat.add_le_add (bit_le (h false)) (bit_le (h true))

/-- On `Nat` under `max`, the induced order **is** `≤`. Stated once so the
counting results can move between the lattice order and arithmetic. -/
theorem nat_leq_iff_le (m n : Nat) : m ⊑ n ↔ m ≤ n := by
  constructor
  · intro h
    have hle : m ≤ Nat.max m n := Nat.le_max_left m n
    rw [show Nat.max m n = n from h] at hle
    exact hle
  · intro h
    show Nat.max m n = n
    rw [nat_max_def, if_pos h]

/-- **Counting is monotone.** Union only adds elements, and adding elements only
raises the count — the half of the memo's claim that is true. -/
theorem card_monotone : MonotoneLeq card := by
  intro x y hxy
  exact (nat_leq_iff_le _ _).mpr
    (card_le_of_subset ((Holes.gset_leq_iff_subset x y).mp hxy))

/-- ⚠ **Counting is not a join homomorphism.** `card (sawA ⊔ sawB) = 2`, while
merging the two local counts in the summary lattice gives `max 1 1 = 1`. -/
theorem card_not_joinHom : ¬ JoinHom card :=
  fun h => absurd (h sawA sawB) (by decide)

/-- **THE SEPARATION.** Counting is monotone and is not a join homomorphism —
so "monotone" does not license replicating the summary, and the memo's
"transfers unchanged" does not follow from "hole-filling is monotone".

Both conjuncts are about the same function on the same carrier, so nothing here
turns on a mismatch of settings. -/
theorem monotone_not_joinHom : MonotoneLeq card ∧ ¬ JoinHom card :=
  ⟨card_monotone, card_not_joinHom⟩

/-- ⚠ Merging counts by `max` is wrong — codex's first example: two replicas
that saw different elements each report `1`, and `max 1 1 = 1` against a truth
of `2`. -/
theorem max_merge_not_exact :
    ¬ (∀ x y : GSet Bool, card x ⊔ card y = card (x ⊔ y)) :=
  fun h => absurd (h sawA sawB) (by decide)

/-- ⚠ Merging counts by `+` is wrong — codex's second example: two replicas that
saw the *same* element each report `1`, and `1 + 1 = 2` against a truth of `1`.
Union is idempotent and addition is not, so this failure is not repairable by
scaling. -/
theorem add_merge_not_exact :
    ¬ (∀ x y : GSet Bool, card x + card y = card (x ⊔ y)) :=
  fun h => absurd (h sawA sawA) (by decide)

/-- ⚠ **THE IMPOSSIBILITY. No binary merge on the summaries alone can be
exact** — for *every* candidate `m : Nat → Nat → Nat`, here are two scenarios
with pairwise-equal local counts and different merged counts, at least one of
which `m` gets wrong.

The witnesses do not depend on `m` at all: `(sawA, sawA)` and `(sawA, sawB)`
both present the pair of counts `(1, 1)`, and the truths are `1` and `2`. So the
obstruction is not a lack of cleverness in the merge function — it is that the
count has **discarded the identity of what it counted**, and the merge needs
precisely that. This is what "or a summary carrying enough provenance" means in
§5's architecture (ii), stated as an impossibility rather than as advice. -/
theorem no_count_merge_without_provenance (m : Nat → Nat → Nat) :
    ∃ x₁ y₁ x₂ y₂ : GSet Bool,
      card x₁ = card x₂ ∧ card y₁ = card y₂
        ∧ card (x₁ ⊔ y₁) ≠ card (x₂ ⊔ y₂)
        ∧ ¬ (m (card x₁) (card y₁) = card (x₁ ⊔ y₁)
              ∧ m (card x₂) (card y₂) = card (x₂ ⊔ y₂)) := by
  refine ⟨sawA, sawA, sawA, sawB, by decide, by decide, by decide, ?_⟩
  intro hcon
  have h1 := hcon.1
  have h2 := hcon.2
  rw [card_sawA] at h1 h2
  rw [card_sawB] at h2
  rw [card_merge_same] at h1
  rw [card_merge_diff] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- ⚠ **Counting requires evidence** — the same impossibility in §3's
vocabulary, and the classification `RequiresEvidence card` used in §6. -/
theorem card_not_incrementallyMergeable : ¬ IncrementallyMergeable card := by
  intro h
  obtain ⟨m, hm⟩ := h
  obtain ⟨x₁, y₁, x₂, y₂, _, _, _, hbad⟩ := no_count_merge_without_provenance m
  exact hbad ⟨(hm x₁ y₁).symm, (hm x₂ y₂).symm⟩

/-- ⚠ **A monotone summary does not transport the judgement.** `n ≤ 1` is
I-confluent on `Nat` under `max` (the max of two things ≤ 1 is ≤ 1), `card` is
monotone, and yet "my replica's count is at most one" is **not** I-confluent:
two replicas each holding one element merge to two.

So `iconfluent_pullback_of_joinHom`'s hypothesis is load-bearing, and the
pullback is *not* free for a merely monotone computation. The invariants that
*are* free are the upward-closed ones (`iconfluent_pullback_of_monotone`); a
ceiling is downward-closed, and it is exactly the shape that breaks — the same
ceiling `Ceiling.lean` refutes everywhere else, arriving here through a
summary. -/
theorem monotone_pullback_can_fail :
    ∃ J : Invariant Nat, IConfluent J ∧ MonotoneLeq card
      ∧ ¬ IConfluent (fun s : GSet Bool => J (card s)) := by
  refine ⟨fun n => n ≤ 1, ?_, card_monotone, ?_⟩
  · intro a b ha hb
    show Nat.max a b ≤ 1
    exact Nat.max_le.mpr ⟨ha, hb⟩
  · intro hconf
    have hbad : card (sawA ⊔ sawB) ≤ 1 := hconf sawA sawB (by decide) (by decide)
    rw [card_merge_diff] at hbad
    exact absurd hbad (by decide)

/-- **And the upward-closed half really does go through**: "the count is at
least `k`" is I-confluent on the *sources*, by monotonicity alone, with no
homomorphism anywhere. The pair with `monotone_pullback_can_fail` is the whole
content of §2: a lower bound transfers, a ceiling does not. -/
theorem count_lowerBound_iconfluent (k : Nat) :
    IConfluent (fun s : GSet Bool => k ≤ card s) :=
  iconfluent_pullback_of_monotone card_monotone
    (fun x y hxy hx => Nat.le_trans hx ((nat_leq_iff_le x y).mp hxy))

/-- ⚠ **Provenance is forced.** Suppose a summary `g` *is* a join homomorphism
and the count factors through it (`card = k ∘ g`). Then `g` must already
distinguish the replica that saw `a` from the replica that saw `b`.

Which is to say: you may replicate summaries and compute counts from them, but
only if the summary still records *which elements* were seen — at which point
the summary is evidence, and you are running architecture (i) with extra steps.
This is the constructive content of "a summary carrying enough provenance". -/
theorem count_summary_must_distinguish {R : Type v} [MergeState R]
    (g : GSet Bool → R) (hg : JoinHom g) (k : R → Nat)
    (hfactor : ∀ s, card s = k (g s)) : g sawA ≠ g sawB := by
  intro heq
  have h1 : g (sawA ⊔ sawB) = g sawA := by
    rw [hg, heq, merge_idem]
  have h2 : card (sawA ⊔ sawB) = card sawA := by
    rw [hfactor, hfactor, h1]
  rw [card_merge_diff, card_sawA] at h2
  exact absurd h2 (by decide)

/-! ## §5. THE TWO ARCHITECTURES.

The distinction §4 refutes is not academic: it is precisely the fork between the
two ways a replicated system can make a computed value available everywhere. -/

/-- **Architecture (i): replicate the evidence, recompute the view.** What is
shipped is the log/state; every replica recomputes the derived value from its
merged copy. The property this buys is that the view cannot tell delivery order
apart — `Move.derived_view_sec`'s clause (1). -/
def ReplicatesEvidence {L V : Type u} [MergeState L] (interp : L → V) : Prop :=
  ∀ base Δ₁ Δ₂ : L, interp ((base ⊔ Δ₁) ⊔ Δ₂) = interp ((base ⊔ Δ₂) ⊔ Δ₁)

/-- **Architecture (i) is free.** It holds for **every** interpreter, with no
hypothesis whatsoever — because the merge did the work before `interp` ever
ran. This is `Move.derived_view_sec` with the interpreter's invariant clause
dropped (take `I := True`), and it is why the library's Move/derived-view
pattern asks the *log* to be the CRDT and asks nothing of the view.

`Holes.evalSet_hom` is the same architecture at the computation carrier, with a
strictly stronger conclusion available there because the image happens to be a
homomorphism as well. -/
theorem evidence_architecture_is_free {L V : Type u} [MergeState L]
    (interp : L → V) : ReplicatesEvidence interp :=
  fun base Δ₁ Δ₂ =>
    (Move.derived_view_sec interp (fun _ => True) (fun _ => trivial) base Δ₁ Δ₂).1

/-- Redelivery is unobservable in architecture (i) too — `derived_view_sec`'s
clause (2), for the record, since a summary architecture has to earn this one
separately. -/
theorem evidence_architecture_redelivery {L V : Type u} [MergeState L]
    (interp : L → V) (base Δ : L) :
    interp ((base ⊔ Δ) ⊔ Δ) = interp (base ⊔ Δ) :=
  (Move.derived_view_sec interp (fun _ => True) (fun _ => trivial) base Δ Δ).2.1

/-- **Architecture (ii): replicate the computed summaries.** Each replica ships
`f` of its state, and a receiver folds the arriving summaries with the summary
lattice's own join (`Delta.joinAll` — the entire runtime of a delta-CRDT
receiver). The property required is that this fold agrees with recomputing from
the merged evidence, for every gossip history. -/
def SummaryFoldAgrees {S : Type u} {R : Type v} [MergeState S] [MergeState R]
    (f : S → R) : Prop :=
  ∀ (l : List S) (init : S),
    f (Delta.joinAll init l) = Delta.joinAll (f init) (l.map f)

/-- A join homomorphism folds: `Delta.lean`'s shipping laws apply to the
summaries, so any order, any batching, any duplication of *summaries* lands
where recomputation from the merged evidence lands. (`Holes.evalSet_fold` is
this theorem at `evalSet`, proved there directly from the headline.) -/
theorem joinHom_fold {S : Type u} {R : Type v} [MergeState S] [MergeState R]
    (f : S → R) (hf : JoinHom f) :
    ∀ (l : List S) (init : S),
      f (Delta.joinAll init l) = Delta.joinAll (f init) (l.map f)
  | [], _ => rfl
  | d :: rest, init => by
      show f (Delta.joinAll (init ⊔ d) rest)
          = Delta.joinAll (f init ⊔ f d) (rest.map f)
      rw [joinHom_fold f hf rest (init ⊔ d), hf]

/-- **Architecture (ii) is correct exactly for join homomorphisms.** Not "needs
a hom" — *iff*. The ⟸ direction is `joinHom_fold`; the ⟹ direction reads the
one-element history `[y]` from `init = x`, which is the homomorphism equation
verbatim.

So the memo's licence to replicate summaries is not merely unjustified by
monotonicity: it is equivalent to a property `card` provably lacks. -/
theorem summaryFold_iff_joinHom {S : Type u} {R : Type v}
    [MergeState S] [MergeState R] (f : S → R) :
    SummaryFoldAgrees f ↔ JoinHom f := by
  constructor
  · intro h x y
    exact h [y] x
  · intro hf
    exact joinHom_fold f hf

/-- ⚠ **The summary architecture, run on a count, is wrong in one gossip
step.** A replica that saw `a` receives the summary of a replica that saw `b`
and folds it into its own: the fold says `1`, recomputation says `2`. -/
theorem card_fold_disagrees :
    card (Delta.joinAll sawA [sawB]) ≠ Delta.joinAll (card sawA) ([sawB].map card) := by
  decide

/-! ## §6. THE FOURTH VERDICT.

`FORCODEX.md` §4.3 proposes three verdicts a single elaborator could report over
one program: **deterministic?** (LVars), **coordination-free?** (CALM), **does my
invariant on the result survive?** (I-confluence lifted to computation, this
library's). Codex's review adds a fourth, and §4 is why it is not implied by the
other three:

> **is this computation incrementally mergeable from its results, or must it
> retain and replay source evidence?**

The verdict is `IncrementallyMergeable` (§3) against `RequiresEvidence`, it is
characterised by `incrementallyMergeable_iff_resultDetermined`, and it selects
the architecture: `fromResults` licenses §5's (ii), `needsEvidence` mandates
§5's (i). -/

/-- **The fourth verdict**, as a named answer. -/
inductive Fourth where
  /-- The merged result is computable from the two results: ship summaries. -/
  | fromResults
  /-- The results have forgotten what the merge needs: ship evidence. -/
  | needsEvidence
  deriving DecidableEq, Repr

/-- What it means for a verdict to be the right answer for a computation. -/
def Fourth.Correct {S : Type u} {R : Type v} [MergeState S] (f : S → R) :
    Fourth → Prop
  | .fromResults => IncrementallyMergeable f
  | .needsEvidence => RequiresEvidence f

/-- Every computation has one of the two answers. (Classical: the verdict is a
genuine dichotomy, not a decision procedure — see the boundary.) -/
theorem fourth_total {S : Type u} {R : Type v} [MergeState S] (f : S → R) :
    ∃ v : Fourth, Fourth.Correct f v :=
  match Classical.em (IncrementallyMergeable f) with
  | Or.inl h => ⟨Fourth.fromResults, h⟩
  | Or.inr h => ⟨Fourth.needsEvidence, h⟩

/-- The two answers are exclusive: `RequiresEvidence` is the negation. -/
theorem fourth_exclusive {S : Type u} {R : Type v} [MergeState S] (f : S → R) :
    ¬ (Fourth.Correct f Fourth.fromResults ∧ Fourth.Correct f Fourth.needsEvidence) :=
  fun h => h.2 h.1

/-! ### §6.1 The class is inhabited — four join homomorphisms.

Architecture (ii) is not vacuous. Each of these is a real computation over
replicated state whose summary may be shipped and merged, and each is a
`JoinHom` by a proof, not by hope. -/

/-- **Set image** — `Holes.evalSet_hom`, restated in this file's vocabulary.
Recorded here to keep the correction exact: this theorem was **already** a
genuine join homomorphism (an image distributes over a union, because ∃
distributes over ∨) and needed no repair. What needed repair was the prose that
generalised from it. -/
theorem evalSet_joinHom {α : Type} (g : Holes.World → α) :
    JoinHom (Holes.evalSet g) :=
  Holes.evalSet_hom g

/-- The high-water mark over a two-replica G-Counter: the largest count anyone
has reached. -/
def high (c : GCounter Bool) : Nat := Nat.max (c false) (c true)

/-- Half of the four-way `max` shuffle. Stated one-directionally because the
other direction is this lemma with the middle two arguments swapped. (`omega`
treats `Nat.max` as an opaque atom, so this goes through `Nat.max_le` and the
two injections by hand.) -/
theorem nat_max_shuffle_le (a b c d : Nat) :
    Nat.max (Nat.max a b) (Nat.max c d) ≤ Nat.max (Nat.max a c) (Nat.max b d) :=
  Nat.max_le.mpr
    ⟨Nat.max_le.mpr
       ⟨Nat.le_trans (Nat.le_max_left a c) (Nat.le_max_left _ _),
        Nat.le_trans (Nat.le_max_left b d) (Nat.le_max_right _ _)⟩,
     Nat.max_le.mpr
       ⟨Nat.le_trans (Nat.le_max_right a c) (Nat.le_max_left _ _),
        Nat.le_trans (Nat.le_max_right b d) (Nat.le_max_right _ _)⟩⟩

/-- Four maxima regroup: `max` is commutative and associative, so which pairs
you take first cannot matter. This is the whole content of `high_joinHom`. -/
theorem nat_max_shuffle (a b c d : Nat) :
    Nat.max (Nat.max a b) (Nat.max c d) = Nat.max (Nat.max a c) (Nat.max b d) :=
  Nat.le_antisymm (nat_max_shuffle_le a b c d) (nat_max_shuffle_le a c b d)

/-- **Max is a join homomorphism.** Merging G-Counters pointwise by `max` and
then taking the max across keys is taking the max across keys and then merging —
associativity and commutativity of `max`, nothing more. So a high-water mark may
be replicated as a bare number, unlike a count. -/
theorem high_joinHom : JoinHom high := by
  intro x y
  show Nat.max (Nat.max (x false) (y false)) (Nat.max (x true) (y true))
      = Nat.max (Nat.max (x false) (x true)) (Nat.max (y false) (y true))
  exact nat_max_shuffle (x false) (y false) (x true) (y true)

/-- Prop under disjunction is a join-semilattice — the summary lattice of a
yes/no read. Scoped, so it cannot collide with the pointwise instance any other
file relies on. -/
scoped instance instMergeStateProp : MergeState Prop where
  merge p q := p ∨ q
  merge_comm _ _ := propext ⟨Or.symm, Or.symm⟩
  merge_assoc _ _ _ := propext
    ⟨fun h => h.elim (fun hpq => hpq.elim Or.inl (fun hq => Or.inr (Or.inl hq)))
       (fun hr => Or.inr (Or.inr hr)),
     fun h => h.elim (fun hp => Or.inl (Or.inl hp))
       (fun hqr => hqr.elim (fun hq => Or.inl (Or.inr hq)) Or.inr)⟩
  merge_idem _ := propext ⟨fun h => h.elim id id, Or.inl⟩

/-- **Existential quantification is a join homomorphism** — "does anyone's
replica contain something?" merges by `∨`. This is the same fact that powers
`Holes.evalSet_hom`, isolated: ∃ distributes over ∨. -/
theorem exists_joinHom {α : Type} :
    JoinHom (fun s : GSet α => ∃ a, s a = true) := by
  intro x y
  show (∃ a, (x ⊔ y) a = true) = ((∃ a, x a = true) ∨ (∃ a, y a = true))
  apply propext
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    rcases (Holes.gset_mem_or x y a).mp ha with h' | h'
    · exact Or.inl ⟨a, h'⟩
    · exact Or.inr ⟨a, h'⟩
  · intro h
    rcases h with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, (Holes.gset_mem_or x y a).mpr (Or.inl ha)⟩
    · exact ⟨a, (Holes.gset_mem_or x y a).mpr (Or.inr ha)⟩

/-- A filtered view of a grow-only set: keep the members satisfying `p`. -/
def restrict {α : Type} (p : α → Bool) (s : GSet α) : GSet α := fun a => s a && p a

/-- **Filtering is a join homomorphism** — `&&` distributes over `||`. A replica
may ship the filtered set and a peer may merge filtered sets: the practical
reason "the view is a projection" is a safe design and "the view is an
aggregate" is not. -/
theorem restrict_joinHom {α : Type} (p : α → Bool) : JoinHom (restrict p) := by
  intro x y
  funext a
  show ((x a || y a) && p a) = ((x a && p a) || (y a && p a))
  cases hx : x a <;> cases hy : y a <;> cases hp : p a <;> rfl

/-! ### §6.2 The classification.

Five computations over replicated state, each with its fourth verdict proved. -/

/-- **Image / derived view** — `fromResults`. -/
theorem verdict_image {α : Type} (g : Holes.World → α) :
    Fourth.Correct (Holes.evalSet g) Fourth.fromResults :=
  joinHom_incrementallyMergeable (evalSet_joinHom g)

/-- **High-water mark** — `fromResults`. -/
theorem verdict_high : Fourth.Correct high Fourth.fromResults :=
  joinHom_incrementallyMergeable high_joinHom

/-- **Existential read ("has anyone seen anything?")** — `fromResults`. -/
theorem verdict_exists {α : Type} :
    Fourth.Correct (fun s : GSet α => ∃ a, s a = true) Fourth.fromResults :=
  joinHom_incrementallyMergeable exists_joinHom

/-- **Filtered view** — `fromResults`. -/
theorem verdict_restrict {α : Type} (p : α → Bool) :
    Fourth.Correct (restrict p) Fourth.fromResults :=
  joinHom_incrementallyMergeable (restrict_joinHom p)

/-- ⚠ **Count** — `needsEvidence`, and this is the verdict the memo's prose
would have gotten wrong: counting is monotone, so a reading that stops at
monotonicity classifies it `fromResults` and ships a summary that cannot be
merged. -/
theorem verdict_card : Fourth.Correct card Fourth.needsEvidence :=
  card_not_incrementallyMergeable

end JoinHom

end Uwueave
