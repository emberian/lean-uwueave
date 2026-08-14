/-
# Uwueave.SeamColoring — segmented confluence is a proper colouring of the clash graph.

**This file exists because an external reviewer (codex), in a second review of
this tree, handed us a characterisation we had not seen.** The tree already had
the one-directional shadow of it — `SeamAlgebra.seam_must_separate_right` /
`_left`, "a seam is refuted by any fiber containing a clash" — and read it as a
family of impossibility results. Codex read it as *half of an equivalence*:

> Build the **clash graph**: vertices are the invariant-satisfying states,
> and there is an edge `x — y` exactly when `I x`, `I y` and `¬ I (x ⊔ y)`.
> A seam projection must separate every such pair. So a seam is a **proper
> colouring** of the clash graph, and seam synthesis is graph colouring.

That reading is what this file makes precise, and it is worth more than the
slogan: it turns a search for a projection into a decidable combinatorial
problem over a finite fragment, with an algorithm and a machine-checked
certificate at the end of it (§5, §6).

## What is claimed, and what is folklore

The **conflict-graph-and-colouring** move itself is not ours and is not new:
colouring a graph of pairwise-incompatible items is the standard shape of
register allocation, frequency assignment, exam timetabling and every other
conflict-serialisation problem, and it long predates this library. What is
claimed here is the **connection**: that `SegmentedIConfluent`'s first conjunct
is *exactly* the proper-colouring condition on the clash graph of `IConfluent`'s
refutations, that its second conjunct is *exactly* what colouring does not see,
and that a greedy colourer therefore synthesises seams. The theorems are the
claim; the graph theory is the vocabulary.

## The honest shape of the characterisation — read this before citing it

`SegmentedIConfluent σ I` is a **conjunction of two clauses** (see
`Segmented.lean`, and `SeamAlgebra.segmented_iff` which names them):

  1. *safety* — merges inside a fiber preserve `I`;
  2. *closure* — merges inside a fiber stay in the fiber (`SeamStableOn`).

**Colouring characterises clause 1 and says nothing whatever about clause 2.**
That is not a caveat bolted on: `coloring_alone_does_not_segment` below exhibits
a four-state carrier, an invariant with an *empty* clash graph (so every
projection is a proper colouring, vacuously), and a projection that is not a
seam. So the headline is an iff with the residual named rather than hidden:

    segmented_iff_properColoring :
      SegmentedIConfluent σ I ↔ (ProperColoring V σ I ∧ SeamStableOn I σ)

over a vertex pool `V` that **covers** the carrier. The colouring half is the
new content; `SeamStableOn` is the tree's own existing name for the rest, and
`SeamAlgebra.seamStable_of_hom` is the cheap sufficient condition that every
seam in this library actually discharges.

## Contents

  * §1 the clash graph — `Clashes`, symmetric and irreflexive, and
    `iconfluent_iff_no_clash_edge`: I-confluence *is* edgelessness.
  * §2 `ProperColoring` over a finite vertex pool, and its positive form.
  * §3 the headline, plus `properColoring_of_segmented` — which needs no
    finiteness at all and re-derives `SeamAlgebra.seam_must_separate_right`.
  * §4 synthesis: a greedy colourer, and `greedySeamFor_properColoring`, a
    **general** theorem that what it returns is proper — not a checked instance.
  * §5 the run, on the uniqueness ceiling of `Cost.lean` §9. The synthesised
    seam agrees with the hand-written `Cost.seamTrue_segmented` on every legal
    state, differs on the one illegal state (where nothing constrains it), and
    is certified `SegmentedIConfluent` by the headline.
  * §6 the composition payoff: `clash_edge_forces_crossing`, from which
    `Cost.no_seam_frees_both` is a corollary whose hand-written proof collapses
    to `decide` on a single edge.
  * §7 exact finite synthesis: enumerate an explicit carrier/palette search
    space, return a certified least-width seam, or prove that the entire named
    search space contains no seam.

## Non-claims

  * ⟨TERMINAL⟩ Colouring does not characterise the closure clause. This is not
    undone work: `coloring_alone_does_not_segment` proves no such implication
    exists, and the extra hypothesis in the headline is `SeamStableOn`, exactly.
  * ⟨SCOPE U-0140⟩ **Infinite carriers.** Every statement that turns a colouring back
    into a segmentation takes a covering pool `hV : ∀ s : S, s ∈ V`. Nothing
    here reasons about a reachable *fragment* of an infinite carrier as such;
    `SegmentedIConfluentOn` states what a non-covering pool does buy, which is
    strictly less.
  * ⟨TERMINAL at an explicit finite search space⟩ **Minimum colourings.**
    `greedySeamFor` still synthesises only *a* proper colouring and remains
    order-dependent. §7 separately enumerates every colouring of a supplied
    finite covering carrier by a supplied finite palette and returns a genuine
    minimum, or an exhaustive refusal theorem for exactly that space. It does
    not pretend to enumerate an arbitrary universe-polymorphic seam type.
  * ⟨UNDONE U-0141⟩ **Clique lower bounds.** §6 proves the two-stream floor from a
    single edge. The graph-theoretic generalisation — a `k`-clique in the clash
    graph forces `k` fibers, hence `k-1` crossings — is not here.
  * Classical logic: turning "no monochromatic edge" back into "same colour
    merges legally" is excluded middle on `I (x ⊔ y)`. `Classical.byContradiction`
    is Lean's, not an added axiom — the same footing as
    `Confluence.escalation_witness`, and flagged at each use.

Literature: Bailis et al., VLDB 2015 (I-confluence, and the clash witness this
graph's edges are); Whittaker–Hellerstein, VLDB 2019 (segmentation). The
colouring reading is codex's; conflict graphs are folklore.
-/
import Uwueave.Cost

namespace Uwueave.SeamColoring

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Seams Uwueave.SeamAlgebra
open Uwueave.Cost

universe u v w

/-! ## §1. The clash graph.

The vertices are the states that satisfy the invariant; the edges are precisely
the refutations `Confluence.escalation_witness` produces. There is no new
mathematical object here — the graph is `IConfluent`'s failure set, drawn. -/

/-- **A clash edge.** Two legal states whose merge is illegal: the bug report of
`Confluence.escalation_witness`, as an edge relation. -/
def Clashes {S : Type u} [MergeState S] (I : Invariant S) (x y : S) : Prop :=
  I x ∧ I y ∧ ¬ I (x ⊔ y)

instance instDecidableClashes {S : Type u} [MergeState S] (I : Invariant S)
    [DecidablePred I] (x y : S) : Decidable (Clashes I x y) := by
  unfold Clashes; infer_instance

/-- The clash relation is **symmetric** — because the merge is commutative. So
the graph is undirected, and "colouring" is the right word rather than an
analogy. -/
theorem clashes_symm {S : Type u} [MergeState S] {I : Invariant S} {x y : S}
    (h : Clashes I x y) : Clashes I y x :=
  ⟨h.2.1, h.1, by rw [merge_comm]; exact h.2.2⟩

/-- The clash relation is **irreflexive** — because the merge is idempotent. So
no vertex is its own neighbour, and a colouring is not asked for the impossible.
(Both of the two facts a colouring problem needs come from the CvRDT laws, which
is a small pleasant surprise: the graph is undirected and loopless for the same
reason gossip is safe to repeat.) -/
theorem not_clashes_self {S : Type u} [MergeState S] (I : Invariant S) (x : S) :
    ¬ Clashes I x x :=
  fun h => h.2.2 (by rw [merge_idem]; exact h.1)

/-- **I-confluence is edgelessness.** The two judgements are the same fact read
at two resolutions: `IConfluent I` says the clash graph has no edges at all, and
that is why a free invariant needs no seam — there is nothing to separate.

(⟸ is classical: from `¬ Clashes I x y` and `I x`, `I y` one recovers
`I (x ⊔ y)` only by excluded middle.) -/
theorem iconfluent_iff_no_clash_edge {S : Type u} [MergeState S] (I : Invariant S) :
    IConfluent I ↔ ∀ x y : S, ¬ Clashes I x y := by
  constructor
  · intro h x y hc
    exact hc.2.2 (h x y hc.1 hc.2.1)
  · intro h x y hx hy
    exact Classical.byContradiction fun hbad => h x y ⟨hx, hy, hbad⟩

/-- The edge relation as a `Bool`, so that a finite clash graph can be walked by
a program (§4) and checked by `decide`. -/
def clashesB {S : Type u} [MergeState S] (I : Invariant S) [DecidablePred I]
    (x y : S) : Bool :=
  decide (I x) && decide (I y) && !decide (I (x ⊔ y))

theorem clashesB_eq_true_iff {S : Type u} [MergeState S] {I : Invariant S}
    [DecidablePred I] {x y : S} : clashesB I x y = true ↔ Clashes I x y := by
  unfold clashesB Clashes
  constructor
  · intro h
    have h' := (Bool.and_eq_true _ _).mp h
    have h'' := (Bool.and_eq_true _ _).mp h'.1
    exact ⟨of_decide_eq_true h''.1, of_decide_eq_true h''.2,
      fun hI => by simp [decide_eq_true hI] at h'⟩
  · intro ⟨hx, hy, hbad⟩
    simp [decide_eq_true hx, decide_eq_true hy, decide_eq_false hbad]

theorem clashesB_symm {S : Type u} [MergeState S] (I : Invariant S)
    [DecidablePred I] (x y : S) : clashesB I x y = clashesB I y x := by
  unfold clashesB
  rw [show (x ⊔ y) = (y ⊔ x) from merge_comm x y]
  cases h1 : (decide (I x)) <;> cases h2 : (decide (I y)) <;> simp

theorem clashesB_irrefl {S : Type u} [MergeState S] (I : Invariant S)
    [DecidablePred I] (x : S) : clashesB I x x = false := by
  unfold clashesB
  rw [show (x ⊔ x) = x from merge_idem x]
  cases h : (decide (I x)) <;> simp

/-! ## §2. Proper colourings.

A **vertex pool** is an explicit `List S`. Nothing below requires it to be the
whole carrier, and the two directions of the characterisation differ exactly on
whether they need it to be — which is the honest place to put the finiteness.

We deliberately do **not** import `Tactics.Core`'s `FinEnum` class here. The
only thing this file wants from it is "a list plus its completeness proof", the
tactic layer is being edited concurrently, and a coverage *hypothesis*
(`hV : ∀ s : S, s ∈ V`) is weaker and more honest than a class anyway: it lets
every statement say precisely whether it needs coverage. §5's four-state
enumeration is therefore a local duplicate of one line of that class, and is
said to be. -/

/-- **A proper colouring of the clash graph.** No clash edge with both endpoints
in the pool is monochromatic: a seam must separate every pair it would otherwise
merge illegally. This is the whole of codex's condition. -/
def ProperColoring {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, Clashes I x y → σ x ≠ σ y

instance instDecidableProperColoring {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (σ : S → Seg) (I : Invariant S) [DecidablePred I] [DecidableEq Seg] :
    Decidable (ProperColoring V σ I) := by
  unfold ProperColoring; infer_instance

/-- The same condition stated positively: inside a fiber, merges are legal. This
is `SegmentedIConfluent`'s first conjunct, restricted to the pool. -/
def SeparatesOn {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, I x → I y → σ x = σ y → I (x ⊔ y)

/-- Safety ⟹ properness, constructively: a monochromatic pair merges legally, so
it was never an edge. -/
theorem properColoring_of_separatesOn {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {σ : S → Seg} {I : Invariant S} (h : SeparatesOn V σ I) :
    ProperColoring V σ I :=
  fun x hx y hy hc hσ => hc.2.2 (h x hx y hy hc.1 hc.2.1 hσ)

/-- Properness ⟹ safety. ⚠ Classical: properness gives `¬¬ I (x ⊔ y)`, and only
excluded middle turns that into `I (x ⊔ y)`. -/
theorem separatesOn_of_properColoring {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {σ : S → Seg} {I : Invariant S} (h : ProperColoring V σ I) :
    SeparatesOn V σ I :=
  fun x hx y hy hIx hIy hσ =>
    Classical.byContradiction fun hbad => h x hx y hy ⟨hIx, hIy, hbad⟩ hσ

/-- **The colouring condition and the safety clause are the same condition.** -/
theorem properColoring_iff_separatesOn {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {σ : S → Seg} {I : Invariant S} :
    ProperColoring V σ I ↔ SeparatesOn V σ I :=
  ⟨separatesOn_of_properColoring, properColoring_of_separatesOn⟩

/-- A free invariant has an edgeless graph, so **every** projection colours it
properly — over every pool, into every target. Read as a warning rather than a
convenience: this is exactly the situation in which a proper colouring carries
no information about seams at all (`coloring_alone_does_not_segment`). -/
theorem properColoring_of_iconfluent {S : Type u} {Seg : Type v} [MergeState S]
    {I : Invariant S} (h : IConfluent I) (V : List S) (σ : S → Seg) :
    ProperColoring V σ I :=
  fun x _ y _ hc _ => (iconfluent_iff_no_clash_edge I).mp h x y hc

/-- **The clash graph is 1-colourable iff the invariant is coordination-free** —
the graph-theoretic reading of `Segmented.iconfluent_iff_trivially_segmented`.
One colour is one fiber is no coordination point. -/
theorem unit_coloring_proper_iff {S : Type u} [MergeState S] {I : Invariant S}
    {V : List S} (hV : ∀ s : S, s ∈ V) :
    ProperColoring V (fun _ : S => ()) I ↔ IConfluent I := by
  constructor
  · intro h
    refine (iconfluent_iff_no_clash_edge I).mpr fun x y hc => ?_
    exact h x (hV x) y (hV y) hc rfl
  · intro h
    exact properColoring_of_iconfluent h V _

/-! ## §3. The headline.

`SeamAlgebra.segmented_iff` already splits the judgement into safety and
closure. §2 says the safety half *is* proper colouring. Composing the two is the
characterisation — and keeping them composed rather than merged is what keeps it
honest, because the closure half survives the composition untouched. -/

/-- Segmented I-confluence **restricted to a pool** — the fragment reading. Note
what it does not say: nothing about merges of states outside `V`, and nothing
about whether `x ⊔ y` is in `V`. A non-covering pool therefore buys a strictly
weaker statement than `SegmentedIConfluent`, and `segmented_of_segmentedOn` is
where the difference is paid. -/
def SegmentedIConfluentOn {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (σ : S → Seg) (I : Invariant S) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, σ x = σ y → I x → I y → I (x ⊔ y) ∧ σ (x ⊔ y) = σ x

/-- Fiber stability restricted to a pool — `SeamAlgebra.SeamStableOn`'s
pool-relative form, and the residual the colouring condition cannot see. -/
def SeamStableOnPool {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (I : Invariant S) (σ : S → Seg) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, I x → I y → σ x = σ y → σ (x ⊔ y) = σ x

instance instDecidableSeamStableOnPool {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (I : Invariant S) (σ : S → Seg) [DecidablePred I] [DecidableEq Seg] :
    Decidable (SeamStableOnPool V I σ) := by
  unfold SeamStableOnPool; infer_instance

/-- The pool-relative decomposition — `SeamAlgebra.segmented_iff` with the
safety half already traded for the colouring condition. This is the theorem the
headline is assembled from, and it needs **no** finiteness or coverage. -/
theorem segmentedOn_iff_properColoring {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {σ : S → Seg} {I : Invariant S} :
    SegmentedIConfluentOn V σ I ↔ (ProperColoring V σ I ∧ SeamStableOnPool V I σ) := by
  constructor
  · intro h
    refine ⟨properColoring_of_separatesOn ?_, fun x hx y hy hIx hIy hσ =>
      (h x hx y hy hσ hIx hIy).2⟩
    exact fun x hx y hy hIx hIy hσ => (h x hx y hy hσ hIx hIy).1
  · intro ⟨hcol, hstab⟩ x hx y hy hσ hIx hIy
    exact ⟨separatesOn_of_properColoring hcol x hx y hy hIx hIy hσ,
      hstab x hx y hy hIx hIy hσ⟩

/-- Restriction to a pool is free. -/
theorem segmentedOn_of_segmented {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I : Invariant S} (h : SegmentedIConfluent σ I) (V : List S) :
    SegmentedIConfluentOn V σ I :=
  fun x _ y _ hσ hIx hIy => h x y hσ hIx hIy

/-- …and coverage is exactly what buys the way back. -/
theorem segmented_of_segmentedOn {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {σ : S → Seg} {I : Invariant S} (hV : ∀ s : S, s ∈ V)
    (h : SegmentedIConfluentOn V σ I) : SegmentedIConfluent σ I :=
  fun x y hσ hIx hIy => h x (hV x) y (hV y) hσ hIx hIy

theorem seamStableOn_of_pool {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {I : Invariant S} {σ : S → Seg} (hV : ∀ s : S, s ∈ V)
    (h : SeamStableOnPool V I σ) : SeamStableOn I σ :=
  fun x y hIx hIy hσ => h x (hV x) y (hV y) hIx hIy hσ

theorem seamStableOnPool_of_seamStableOn {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {I : Invariant S} {σ : S → Seg} (h : SeamStableOn I σ) :
    SeamStableOnPool V I σ :=
  fun x _ y _ hIx hIy hσ => h x y hIx hIy hσ

/-- **THE HEADLINE — a seam is a proper colouring of the clash graph, plus fiber
stability, and nothing else.**

Over a pool `V` that covers the carrier, `SegmentedIConfluent σ I` holds **iff**
`σ` is a proper colouring of the clash graph *and* `σ`'s fibers are closed under
legal merges. Both conjuncts are load-bearing and neither implies the other:

  * colouring is not enough — `coloring_alone_does_not_segment` gives a
    four-state carrier where the graph is edgeless (so every projection is
    proper) and a projection that is still not a seam;
  * stability is not enough — `SeamAlgebra.seamStable_fst` says `Prod.fst` is
    stable on *every* product carrier, including ones whose first field clashes.

Read as a method: the colouring half is a decidable combinatorial problem over a
finite fragment (`instDecidableProperColoring`) and can be **solved** (§4); the
stability half is a property of the projection alone, discharged in one line by
`SeamAlgebra.seamStable_of_hom` for every seam this library actually uses. That
asymmetry is the practical content of the characterisation. -/
theorem segmented_iff_properColoring {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {σ : S → Seg} {I : Invariant S} (hV : ∀ s : S, s ∈ V) :
    SegmentedIConfluent σ I ↔ (ProperColoring V σ I ∧ SeamStableOn I σ) := by
  constructor
  · intro h
    have hOn := segmentedOn_iff_properColoring.mp (segmentedOn_of_segmented h V)
    exact ⟨hOn.1, seamStableOn_of_pool hV hOn.2⟩
  · intro ⟨hcol, hstab⟩
    exact segmented_of_segmentedOn hV
      (segmentedOn_iff_properColoring.mpr ⟨hcol, seamStableOnPool_of_seamStableOn hstab⟩)

/-- The safety clause **alone**, characterised exactly — no stability, no
residual, and this is the sentence the file's title means. Over a covering pool,
"merges inside a fiber preserve `I`" and "no clash edge is monochromatic" are
the same proposition. -/
theorem safetyClause_iff_properColoring {S : Type u} {Seg : Type v} [MergeState S]
    {V : List S} {σ : S → Seg} {I : Invariant S} (hV : ∀ s : S, s ∈ V) :
    (∀ x y : S, σ x = σ y → I x → I y → I (x ⊔ y)) ↔ ProperColoring V σ I := by
  constructor
  · intro h
    exact properColoring_of_separatesOn fun x _ y _ hIx hIy hσ => h x y hσ hIx hIy
  · intro h x y hσ hIx hIy
    exact separatesOn_of_properColoring h x (hV x) y (hV y) hIx hIy hσ

/-- **The direction that costs nothing.** Every seam is a proper colouring, over
*every* pool — no coverage, no finiteness, no classical logic. This is the
general form of `SeamAlgebra.seam_must_separate_right`/`_left`, with the
product-embedding stripped off: those theorems are this one applied to the pair
`((a, b₁), (a, b₂))`. -/
theorem properColoring_of_segmented {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I : Invariant S} (h : SegmentedIConfluent σ I) (V : List S) :
    ProperColoring V σ I :=
  fun x _ y _ hc hσ => hc.2.2 (h x y hσ hc.1 hc.2.1).1

/-- The contrapositive, which is the design statement: **one monochromatic clash
edge refutes a seam.** -/
theorem not_segmented_of_monochromatic {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I : Invariant S} {x y : S} (hc : Clashes I x y) (hσ : σ x = σ y) :
    ¬ SegmentedIConfluent σ I :=
  fun h => properColoring_of_segmented h [x, y] x (by simp) y (by simp) hc hσ

/-- `SeamAlgebra.seam_must_separate_right`, re-derived from the colouring
statement — recorded to show that the existing negative results of §5 there are
instances of this one fact and not a separate family. The clash edge is
`((a, b₁), (a, b₂))`; the product's merge is componentwise, so field B's
illegal merge is the whole pair's. -/
theorem seam_must_separate_right_via_coloring {A : Type u} {B : Type v} {T : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    (τ : A × B → T) (a : A) (ha : IA a) (b₁ b₂ : B)
    (h₁ : IB b₁) (h₂ : IB b₂) (hbad : ¬ IB (b₁ ⊔ b₂))
    (hτ : τ (a, b₁) = τ (a, b₂)) :
    ¬ SegmentedIConfluent τ (fun p : A × B => IA p.1 ∧ IB p.2) :=
  not_segmented_of_monochromatic ⟨⟨ha, h₁⟩, ⟨ha, h₂⟩, fun h => hbad h.2⟩ hτ

/-- **A single clash edge kills every constant seam** — coordination is not
optional once the graph has an edge. (`Segmented.iconfluent_iff_trivially_
segmented` says the same thing for the canonical constant seam; this says it for
all of them at once.) -/
theorem no_constant_seam_of_clash {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I : Invariant S} {x y : S} (hc : Clashes I x y)
    (hconst : ∀ a b : S, σ a = σ b) : ¬ SegmentedIConfluent σ I :=
  not_segmented_of_monochromatic hc (hconst x y)

/-! ## §4. Synthesis — a greedy colourer that returns its own certificate.

The colouring condition is decidable over a finite pool, so it can be *searched*
rather than guessed. What follows is an ordinary greedy colourer, and
`greedySeamFor_properColoring` is a **general** theorem about it — not a
`decide` on one example. The example is §5. -/

/-- The least colour not in `used`, searched upward from `n` with `fuel` steps.
Fuel is the only reason this is structural; `freshColor` supplies enough of it
that the search never runs out (`leastFreeFrom_not_mem`). -/
def leastFreeFrom (used : List Nat) (n : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n ∈ used then leastFreeFrom used (n + 1) fuel else n

/-- The search succeeds as soon as the fuel reaches past every used colour. The
induction is on fuel and the hypothesis strengthens itself along it — which is
why no pigeonhole argument is needed. -/
theorem leastFreeFrom_not_mem (used : List Nat) :
    ∀ (fuel n : Nat), (∀ c ∈ used, c < n + fuel) → leastFreeFrom used n fuel ∉ used := by
  intro fuel
  induction fuel with
  | zero =>
      intro n h hmem
      have := h n hmem
      omega
  | succ fuel ih =>
      intro n h
      simp only [leastFreeFrom]
      by_cases hn : n ∈ used
      · rw [if_pos hn]
        exact ih (n + 1) (fun c hc => by have := h c hc; omega)
      · rw [if_neg hn]
        exact hn

/-- A strict upper bound on a colour list — deliberately crude, since it is only
fuel. -/
def colorBound : List Nat → Nat
  | [] => 0
  | c :: l => c + 1 + colorBound l

theorem lt_colorBound : ∀ (used : List Nat), ∀ c ∈ used, c < colorBound used := by
  intro used
  induction used with
  | nil => intro c hc; cases hc
  | cons a l ih =>
      intro c hc
      show c < a + 1 + colorBound l
      rcases List.mem_cons.mp hc with h | h
      · omega
      · have := ih c h; omega

/-- **The least colour not already used by a coloured neighbour.** This is what
makes the colourer greedy rather than merely correct: a state takes the lowest
colour none of its coloured neighbours holds, rather than a fresh one each time,
so colours — and therefore fibers — are reused. "Greedy" is not "minimum";
§7 obtains the latter by exhaustive finite search. Only `freshColor_not_mem`,
the avoidance property, is used here. -/
def freshColor (used : List Nat) : Nat := leastFreeFrom used 0 (colorBound used)

theorem freshColor_not_mem (used : List Nat) : freshColor used ∉ used :=
  leastFreeFrom_not_mem used _ 0 (fun c hc => by have := lt_colorBound used c hc; omega)

/-- The colours already taken by the coloured neighbours of `v`. -/
def usedColors {S : Type u} (adj : S → S → Bool) (v : S) (tbl : List (S × Nat)) : List Nat :=
  tbl.filterMap fun p => if adj v p.1 then some p.2 else none

/-- The greedy table. The head of the pool is coloured **last**, against the
table already built for the tail — so the traversal order is the reverse of the
list, which is worth saying because greedy colouring is order-dependent and §5
reports which seam this particular order lands on. -/
def greedyTbl {S : Type u} (adj : S → S → Bool) : List S → List (S × Nat)
  | [] => []
  | v :: rest =>
      let tbl := greedyTbl adj rest
      (v, freshColor (usedColors adj v tbl)) :: tbl

theorem greedyTbl_cons {S : Type u} (adj : S → S → Bool) (v : S) (rest : List S) :
    greedyTbl adj (v :: rest)
      = (v, freshColor (usedColors adj v (greedyTbl adj rest))) :: greedyTbl adj rest :=
  rfl

/-- Reading a colour out of the table; states the table never saw get `0`, which
is junk and is only ever consumed off the pool. -/
def colorAt {S : Type u} [DecidableEq S] (tbl : List (S × Nat)) (s : S) : Nat :=
  match tbl.find? (fun p => decide (p.1 = s)) with
  | some p => p.2
  | none => 0

theorem colorAt_cons_self {S : Type u} [DecidableEq S] (v : S) (c : Nat)
    (tbl : List (S × Nat)) : colorAt ((v, c) :: tbl) v = c := by
  simp [colorAt]

theorem colorAt_cons_ne {S : Type u} [DecidableEq S] {v s : S} (h : v ≠ s) (c : Nat)
    (tbl : List (S × Nat)) : colorAt ((v, c) :: tbl) s = colorAt tbl s := by
  simp [colorAt, h]

/-- Every pooled state is in the table it was coloured by, **at the colour the
lookup returns**. This is the bridge between the table (which the algorithm
manipulates) and `colorAt` (which the theorem is about), and it is where
duplicate entries would otherwise hide. -/
theorem colorAt_mem {S : Type u} [DecidableEq S] (adj : S → S → Bool) :
    ∀ (V : List S) (s : S), s ∈ V →
      (s, colorAt (greedyTbl adj V) s) ∈ greedyTbl adj V := by
  intro V
  induction V with
  | nil => intro s hs; cases hs
  | cons v rest ih =>
      intro s hs
      rw [greedyTbl_cons]
      by_cases hv : v = s
      · subst hv
        rw [colorAt_cons_self]
        exact List.mem_cons_self
      · have hsr : s ∈ rest := by
          rcases List.mem_cons.mp hs with h | h
          · exact absurd h.symm hv
          · exact h
        rw [colorAt_cons_ne hv]
        exact List.mem_cons_of_mem _ (ih s hsr)

/-- **The colourer is correct.** For a symmetric, irreflexive edge relation, the
greedy table is a proper colouring of the pool: adjacent pooled states get
different colours. General — no example, no `decide`, no bound on the pool.

The proof is the textbook one made honest about lookup: when a state is
coloured, the colours of all its already-coloured neighbours are in `used`, and
`freshColor` avoids `used`; `colorAt_mem` is what makes "the neighbour's colour"
a colour that is actually in the table. -/
theorem greedyTbl_proper {S : Type u} [DecidableEq S] {adj : S → S → Bool}
    (hsymm : ∀ x y, adj x y = adj y x) (hirr : ∀ x, adj x x = false) :
    ∀ (V : List S) (x y : S), x ∈ V → y ∈ V → adj x y = true →
      colorAt (greedyTbl adj V) x ≠ colorAt (greedyTbl adj V) y := by
  intro V
  induction V with
  | nil => intro x y hx; cases hx
  | cons v rest ih =>
      intro x y hx hy hadj
      rw [greedyTbl_cons]
      have key : ∀ z : S, z ∈ rest → adj v z = true →
          colorAt (greedyTbl adj rest) z ∈ usedColors adj v (greedyTbl adj rest) := by
        intro z hz hvz
        exact List.mem_filterMap.mpr
          ⟨(z, colorAt (greedyTbl adj rest) z), colorAt_mem adj rest z hz, by simp [hvz]⟩
      by_cases hxv : v = x
      · subst hxv
        have hyv : v ≠ y := by
          intro h
          rw [← h, hirr v] at hadj
          exact Bool.noConfusion hadj
        have hyr : y ∈ rest := by
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h.symm hyv
          · exact h
        rw [colorAt_cons_self, colorAt_cons_ne hyv]
        intro hc
        exact freshColor_not_mem (usedColors adj v (greedyTbl adj rest))
          (by rw [hc]; exact key y hyr hadj)
      · by_cases hyv : v = y
        · subst hyv
          have hxr : x ∈ rest := by
            rcases List.mem_cons.mp hx with h | h
            · exact absurd h.symm hxv
            · exact h
          rw [colorAt_cons_ne hxv, colorAt_cons_self]
          intro hc
          have hvx : adj v x = true := by rw [hsymm]; exact hadj
          exact freshColor_not_mem (usedColors adj v (greedyTbl adj rest))
            (by rw [← hc]; exact key x hxr hvx)
        · have hxr : x ∈ rest := by
            rcases List.mem_cons.mp hx with h | h
            · exact absurd h.symm hxv
            · exact h
          have hyr : y ∈ rest := by
            rcases List.mem_cons.mp hy with h | h
            · exact absurd h.symm hyv
            · exact h
          rw [colorAt_cons_ne hxv, colorAt_cons_ne hyv]
          exact ih x y hxr hyr hadj

/-- **The synthesised seam**: greedily colour the clash graph of `I` over the
pool `V`, and read the colouring as a projection `S → Nat`. -/
def greedySeamFor {S : Type u} [DecidableEq S] [MergeState S] (I : Invariant S)
    [DecidablePred I] (V : List S) : S → Nat :=
  colorAt (greedyTbl (clashesB I) V)

/-- **Synthesis, proved.** What the colourer returns is a proper colouring of the
clash graph — for every carrier with decidable equality, every decidable
invariant and every pool. The CvRDT laws supply the two graph properties the
colourer needs (`clashesB_symm` from `merge_comm`, `clashesB_irrefl` from
`merge_idem`). -/
theorem greedySeamFor_properColoring {S : Type u} [DecidableEq S] [MergeState S]
    (I : Invariant S) [DecidablePred I] (V : List S) :
    ProperColoring V (greedySeamFor I V) I :=
  fun x hx y hy hc =>
    greedyTbl_proper (clashesB_symm I) (clashesB_irrefl I) V x y hx hy
      (clashesB_eq_true_iff.mpr hc)

/-- The synthesis, packaged as a value that **carries its certificate**: a
projection together with the proof that it colours the clash graph properly.
Total — there is no failure branch, because `greedySeamFor_properColoring` is a
theorem and not a check. -/
def synthesizeColoring {S : Type u} [DecidableEq S] [MergeState S] (I : Invariant S)
    [DecidablePred I] (V : List S) : { σ : S → Nat // ProperColoring V σ I } :=
  ⟨greedySeamFor I V, greedySeamFor_properColoring I V⟩

/-- **The full synthesis**, with the residual half checked rather than assumed.
Over a covering pool the colouring is synthesised and the *stability* clause is
decided; a `some` therefore carries a real `SegmentedIConfluent` proof and a
`none` is the honest report that the greedy colouring, though proper, is not
fiber-stable. Nothing here can return a seam that is not one. -/
def synthesizeSeam? {S : Type u} [DecidableEq S] [MergeState S] (I : Invariant S)
    [DecidablePred I] (V : List S) (hV : ∀ s : S, s ∈ V) :
    Option { σ : S → Nat // SegmentedIConfluent σ I } :=
  if h : SeamStableOnPool V I (greedySeamFor I V) then
    some ⟨greedySeamFor I V, (segmented_iff_properColoring hV).mpr
      ⟨greedySeamFor_properColoring I V, seamStableOn_of_pool hV h⟩⟩
  else
    none

/-! ## §5. The run — the uniqueness ceiling of `Cost.lean` §9.

`Cost.pinInv` is `Catalog.gset_atMostOne_not_iconfluent`'s invariant over two
candidate nodes: at most one node is pinned. `Cost.lean` proves *two* seams for
it by hand (`seamFalse_segmented`, `seamTrue_segmented`) and uses the pair to
exhibit the per-stream cost measure's undercount. Here the seam is **computed**.

The carrier has four states, and the enumeration below is a local duplicate of
what `Tactics.Core`'s `FinEnum Bool`-derived instance would give — one line,
duplicated deliberately so that this file does not import the concurrently-edited
tactic layer. -/

/-- Decidable equality on the two-node pin set. Lean core has no `DecidableEq`
for a function type; over `Bool` it is two `Bool` comparisons. -/
instance instDecidableEqPinSet : DecidableEq PinSet := fun x y =>
  decidable_of_iff (x false = y false ∧ x true = y true)
    ⟨fun h => funext fun b => by cases b <;> simp [h.1, h.2],
     fun h => ⟨by rw [h], by rw [h]⟩⟩

instance instDecidablePinInv : DecidablePred pinInv := fun s => by
  unfold pinInv; infer_instance

/-- Only `true` is pinned. -/
def pinT : PinSet := fun b => b

/-- Only `false` is pinned. -/
def pinF : PinSet := fun b => !b

/-- Both pinned — the illegal state, and the merge that makes the clash edge. -/
def pinBoth : PinSet := fun _ => true

/-- The four states, in the order the colourer will see them. -/
def pinStates : List PinSet := [emptyPin, pinT, pinF, pinBoth]

/-- The enumeration is complete: a `Bool → Bool` is pinned down by its two
values. -/
theorem pinStates_complete (s : PinSet) : s ∈ pinStates := by
  have h : s = emptyPin ∨ s = pinT ∨ s = pinF ∨ s = pinBoth := by
    cases hf : s false <;> cases ht : s true
    · exact Or.inl (funext fun b => by cases b <;> simp [emptyPin, hf, ht])
    · exact Or.inr (Or.inl (funext fun b => by cases b <;> simp [pinT, hf, ht]))
    · exact Or.inr (Or.inr (Or.inl (funext fun b => by cases b <;> simp [pinF, hf, ht])))
    · exact Or.inr (Or.inr (Or.inr (funext fun b => by cases b <;> simp [pinBoth, hf, ht])))
  rcases h with h | h | h | h <;> subst h <;> decide

/-- The pin streams' endpoints, named: pinning `true` from nothing reaches
`pinT`, pinning `false` reaches `pinF`. -/
theorem run_pin_true : run pinStep emptyPin [true] = pinT := by decide

theorem run_pin_false : run pinStep emptyPin [false] = pinF := by decide

/-- **The clash graph, computed: exactly one edge.** `pinT — pinF` is the whole
of it. `emptyPin` is adjacent to nothing (merging it into anything is legal) and
`pinBoth` is not a vertex at all (it fails the invariant). One edge is a
two-colourable graph, which is why one coordination point suffices. -/
theorem pin_clash_graph :
    Clashes pinInv pinT pinF
    ∧ ¬ Clashes pinInv emptyPin pinT
    ∧ ¬ Clashes pinInv emptyPin pinF
    ∧ ¬ Clashes pinInv emptyPin pinBoth
    ∧ ¬ Clashes pinInv pinT pinBoth
    ∧ ¬ Clashes pinInv pinF pinBoth := by decide

/-- The one edge, in the form §6 consumes: it joins the two streams' endpoints. -/
theorem pin_stream_endpoints_clash :
    Clashes pinInv (run pinStep emptyPin [true]) (run pinStep emptyPin [false]) := by
  decide

/-- The synthesised seam, evaluated. Greedy colours the pool from the right:
`pinBoth ↦ 0`, `pinF ↦ 0` (no legal neighbour), `pinT ↦ 1` (adjacent to `pinF`),
`emptyPin ↦ 0`. -/
theorem pin_synthesized_values :
    greedySeamFor pinInv pinStates emptyPin = 0
    ∧ greedySeamFor pinInv pinStates pinT = 1
    ∧ greedySeamFor pinInv pinStates pinF = 0
    ∧ greedySeamFor pinInv pinStates pinBoth = 0 := by decide

/-- **The synthesised seam is a seam** — a machine-computed projection with a
machine-checked `SegmentedIConfluent` proof, assembled by the headline from the
general colouring theorem and a decided stability check. This is the deliverable
the characterisation was for: no hand-written seam, no hand-written proof. -/
theorem pin_synthesized_segmented :
    SegmentedIConfluent (greedySeamFor pinInv pinStates) pinInv :=
  (segmented_iff_properColoring pinStates_complete).mpr
    ⟨greedySeamFor_properColoring pinInv pinStates,
     seamStableOn_of_pool pinStates_complete (by decide)⟩

/-- …and the packaged form really does return it. -/
theorem pin_synthesizeSeam_isSome :
    (synthesizeSeam? pinInv pinStates pinStates_complete).isSome = true := by decide

/-- **The synthesised seam agrees with the hand-written one, on the graph.**
Seams are only ever determined up to renaming of colours — what a seam *is* is
its fiber partition — so agreement is agreement of fibers, and on every legal
state the synthesised colouring induces exactly the partition of
`Cost.seamTrue_segmented`'s `fun s => s true`.

So the answer to "does synthesis find the seam a human wrote?" on this clash is
**yes**, and the human wrote two: greedy lands on `seamTrue` because it colours
the pool from the right and so reaches `pinF` before `pinT`. Reversing the
enumeration lands on the other one — `pin_synthesized_reversed_is_seamFalse`.
That order-dependence is not a defect being excused; it is
`Cost.no_seam_frees_both` seen from the other side: the two hand-written seams
are the two proper 2-colourings of one edge, and *choosing between them* is the
coordination. -/
theorem pin_synthesized_agrees_on_legal_states :
    ∀ x ∈ pinStates, ∀ y ∈ pinStates, pinInv x → pinInv y →
      (greedySeamFor pinInv pinStates x = greedySeamFor pinInv pinStates y
        ↔ x true = y true) := by decide

/-- **The other hand-written seam is the other colouring.** Run the colourer on
the reversed enumeration and it reaches `pinT` first, colours it `0`, and pushes
`pinF` to `1` — inducing exactly the fiber partition of
`Cost.seamFalse_segmented`'s `fun s => s false`. So both of the tree's
hand-written seams for this clash are recovered by synthesis, and which one you
get is the traversal order and nothing else. -/
theorem pin_synthesized_reversed_is_seamFalse :
    ∀ x ∈ pinStates.reverse, ∀ y ∈ pinStates.reverse, pinInv x → pinInv y →
      (greedySeamFor pinInv pinStates.reverse x = greedySeamFor pinInv pinStates.reverse y
        ↔ x false = y false) := by decide

/-- ⚠ **…and differs off the graph**, which is the more interesting half and must
be reported. `pinBoth` fails the invariant, so it is not a vertex, so nothing
constrains its colour: the synthesised seam puts it with `emptyPin`, while
`fun s => s true` puts it with `pinT`. Neither is wrong — `SegmentedIConfluent`
hypothesises `I x` and `I y` and therefore never looks. A consumer that reads a
seam value on an illegal state is reading noise. -/
theorem pin_synthesized_differs_off_the_graph :
    greedySeamFor pinInv pinStates pinBoth = greedySeamFor pinInv pinStates emptyPin
    ∧ (pinBoth true ≠ emptyPin true)
    ∧ ¬ pinInv pinBoth := by decide

/-- The cost reading transfers with the fibers. Under the synthesised seam the
`false`-stream is free — the same `0` that `Cost.pinFalse_free_under_seamTrue`
reports for the hand-written `fun s => s true` — and the `true`-stream costs one,
which is the crossing `no_seam_frees_both_via_coloring` says no valid seam can
give back. -/
theorem pin_synthesized_costs :
    crossings (greedySeamFor pinInv pinStates) pinStep emptyPin [false] = 0
    ∧ crossings (greedySeamFor pinInv pinStates) pinStep emptyPin [true] = 1 := by
  decide

/-- ⚠ **The residual, on a finite carrier: a proper colouring that is not a
seam.** Over the same four states with the trivial invariant, the clash graph is
edgeless, so *every* projection colours it properly — and `fun s => s true && s
false`, the "both pinned" observation, is still not a seam: `pinT` and `pinF`
agree on it and their merge does not.

This is the exact reason the headline carries `SeamStableOn` as a second
conjunct, and it is proved rather than asserted. (`SeamAlgebra.free_alone_not_
segmented` is the same phenomenon on the schema carrier; that one is infinite,
so it could not be stated against a covering pool at all.) -/
theorem coloring_alone_does_not_segment :
    ProperColoring pinStates (fun s : PinSet => s true && s false) (fun _ => True)
    ∧ ¬ SegmentedIConfluent (S := PinSet) (fun s => s true && s false) (fun _ => True) := by
  refine ⟨properColoring_of_iconfluent (fun _ _ _ _ => trivial) _ _, ?_⟩
  intro h
  have hbad := (h pinT pinF (by decide) trivial trivial).2
  exact absurd hbad (by decide)

/-- The same point against the tree's own witness, for the record: a widening
migration is I-confluent (`Seams.widening_needs_no_seam`), so its clash graph is
edgeless and every projection over every pool colours it properly — including
`SeamAlgebra.versionAndBoth`, which `SeamAlgebra.free_alone_not_segmented` proves
is not a seam. -/
theorem widening_colored_but_not_segmented :
    (∀ V : List SchemaState, ProperColoring V versionAndBoth (SchemaWF (fun v => 10 * (v + 1))))
    ∧ ¬ SegmentedIConfluent (S := SchemaState) versionAndBoth
          (SchemaWF (fun v => 10 * (v + 1))) :=
  ⟨fun V => properColoring_of_iconfluent widening_needs_no_seam V versionAndBoth,
   free_alone_not_segmented⟩

/-! ## §6. The composition payoff — why a global colouring fixes a per-stream
measure that is unsound.

`Cost.lean` §9 proves that `crossings` — a per-stream, per-seam count —
undercounts a concurrent workload: two streams are each free under a seam of
their own, and no single valid seam frees both. The reason, in this file's
vocabulary, is one sentence: **a colouring is a global choice, and the two
streams' endpoints are adjacent.** Properness is a constraint on the *pair*, so
it survives composition, while a per-stream minimum is taken before the
constraint set is composed and therefore never sees the edge. -/

/-- **A clash edge forces a crossing.** If two runs from a common start end on
adjacent vertices of the clash graph, then *every* seam that segments `I`
charges at least one crossing between them. Neither stream is named; the bound
comes from the edge.

This is `Cost.no_seam_frees_both` with the pin carrier removed — the general
fact, quantified over every seam, every step relation and every pair of
workloads. -/
theorem clash_edge_forces_crossing {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {σ : S → Seg} {I : Invariant S}
    {step : S → Op → S} {s : S} {w₁ w₂ : List Op}
    (hseg : SegmentedIConfluent σ I)
    (hclash : Clashes I (run step s w₁) (run step s w₂)) :
    1 ≤ crossings σ step s w₁ + crossings σ step s w₂ := by
  rcases Nat.eq_zero_or_pos (crossings σ step s w₁ + crossings σ step s w₂) with h | h
  · exfalso
    have h1 : crossings σ step s w₁ = 0 := by omega
    have h2 : crossings σ step s w₂ = 0 := by omega
    have e1 := sigma_const_of_crossings_eq_zero h1
    have e2 := sigma_const_of_crossings_eq_zero h2
    exact hclash.2.2 (hseg _ _ (e1.trans e2.symm) hclash.1 hclash.2.1).1
  · exact h

/-- The joint cost of a *set* of streams under one seam — the quantity a
concurrent workload actually pays, and the one `crossings` alone is not. -/
def jointCost {S : Type u} {Seg : Type v} {Op : Type w} [DecidableEq Seg]
    (σ : S → Seg) (step : S → Op → S) (s : S) (ws : List (List Op)) : Nat :=
  (ws.map (crossings σ step s)).sum

/-- **The composed floor.** Two streams whose endpoints clash cost at least one
crossing *jointly*, under every valid seam. The bound is a statement about the
whole constraint set at once, which is exactly the property a per-stream minimum
lacks. -/
theorem jointCost_floor_of_clash {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {σ : S → Seg} {I : Invariant S}
    {step : S → Op → S} {s : S} {w₁ w₂ : List Op}
    (hseg : SegmentedIConfluent σ I)
    (hclash : Clashes I (run step s w₁) (run step s w₂)) :
    1 ≤ jointCost σ step s [w₁, w₂] := by
  have h := clash_edge_forces_crossing hseg hclash
  show 1 ≤ ([crossings σ step s w₁, crossings σ step s w₂]).sum
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- **`Cost.no_seam_frees_both`, re-derived from the edge.** The original proof
is ~30 lines of case analysis on the pin lattice; here the whole content is
`pin_stream_endpoints_clash`, which `decide` establishes, fed to the general
theorem. That collapse is the payoff codex's characterisation was raised for:
the impossibility is a property of one edge of the clash graph, and once the
graph is the object, finding it is a computation. -/
theorem no_seam_frees_both_via_coloring {Seg : Type v} [DecidableEq Seg]
    (σ : PinSet → Seg) (hseg : SegmentedIConfluent σ pinInv) :
    ¬ (crossings σ pinStep emptyPin [true] = 0
        ∧ crossings σ pinStep emptyPin [false] = 0) := by
  intro ⟨h1, h2⟩
  have h := clash_edge_forces_crossing hseg pin_stream_endpoints_clash
  omega

/-- **The gap, stated as two numbers.** Per-stream, each of the two workloads has
minimum cost `0` — witnessed by a *valid* seam each, so the minimum is genuinely
attained and the per-stream measure is not merely loose. Jointly, under every
valid seam, the floor is `1`. Minimising per-stream and adding gives `0` and is
**unsound**; minimising over colourings of the composed clash graph gives `1`
and is a real lower bound.

The soundness asymmetry is structural, not numerical: `crossings σ …` is a
function of a seam that has already been chosen, so a per-stream minimum
silently quantifies the seam *inside* the sum, where the composed bound
quantifies it outside. -/
theorem perStream_minimisation_is_unsound :
    (crossings (fun s : PinSet => s false) pinStep emptyPin [true] = 0
      ∧ SegmentedIConfluent (S := PinSet) (fun s => s false) pinInv)
    ∧ (crossings (fun s : PinSet => s true) pinStep emptyPin [false] = 0
      ∧ SegmentedIConfluent (S := PinSet) (fun s => s true) pinInv)
    ∧ (∀ {Seg : Type v} [DecidableEq Seg] (σ : PinSet → Seg),
        SegmentedIConfluent σ pinInv →
        1 ≤ jointCost σ pinStep emptyPin [[true], [false]]) :=
  ⟨⟨pinTrue_free_under_seamFalse, seamFalse_segmented⟩,
   ⟨pinFalse_free_under_seamTrue, seamTrue_segmented⟩,
   fun _σ hseg => jointCost_floor_of_clash hseg pin_stream_endpoints_clash⟩

/-- The synthesised seam is subject to the same floor — it is not a cleverer
choice, and no choice was available. A colouring of a graph with an edge has at
least two colours, and the two streams end on the two sides of it. -/
theorem pin_synthesized_pays_the_floor :
    1 ≤ jointCost (greedySeamFor pinInv pinStates) pinStep emptyPin [[true], [false]] :=
  jointCost_floor_of_clash pin_synthesized_segmented pin_stream_endpoints_clash

/-! ## §7. Exact finite minimum synthesis

Greedy colouring is intentionally left greedy.  Exact minimisation is a
different algorithm with a different scope: callers provide a finite list `V`
covering the carrier and a finite palette `C`.  `allColorings` enumerates the
resulting function space, `minimumColoring?` minimizes the number of palette
entries actually used, and `synthesizeMinimumSeam?` packages the winner with
global seam validity and a `LeastSuch`-style theorem.

There is no `Fintype` fiction here.  The lists are data, carrier coverage is a
hypothesis, and the refusal theorem quantifies only over seams whose colours lie
in the supplied palette.  An infinite carrier or an unlisted colour is outside
the result by construction. -/

/-- A colouring uses only the caller's explicit palette on the explicit
carrier pool. -/
def UsesOnly {S : Type u} {Seg : Type v} (V : List S) (C : List Seg)
    (σ : S → Seg) : Prop :=
  ∀ s ∈ V, σ s ∈ C

/-- The number of distinct palette colours used by a colouring on `V`.
`eraseDups` makes the metric insensitive to a caller listing a colour twice. -/
def usedColorCount {S : Type u} {Seg : Type v} [DecidableEq Seg]
    (V : List S) (C : List Seg) (σ : S → Seg) : Nat :=
  (C.eraseDups.filter fun c => V.any (fun s => decide (σ s = c))).length

/-- The finite validity check: proper clash colouring plus fiber stability.
Coverage turns this pair into `SegmentedIConfluent` by
`segmented_iff_properColoring`. -/
def FiniteValid {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (σ : S → Seg) (I : Invariant S) : Prop :=
  ProperColoring V σ I ∧ SeamStableOnPool V I σ

instance instDecidableFiniteValid {S : Type u} {Seg : Type v} [MergeState S]
    (V : List S) (σ : S → Seg) (I : Invariant S)
    [DecidablePred I] [DecidableEq Seg] : Decidable (FiniteValid V σ I) := by
  unfold FiniteValid
  infer_instance

/-- Extend every colouring of the tail by every colour available for the head.
`fallback` totalizes functions away from `V`; a coverage proof later shows that
this branch is observationally irrelevant. -/
def allColorings {S : Type u} {Seg : Type v} [DecidableEq S]
    (C : List Seg) (fallback : Seg) : List S → List (S → Seg)
  | [] => [fun _ => fallback]
  | v :: rest =>
      C.flatMap fun c =>
        (allColorings C fallback rest).map fun σ s => if s = v then c else σ s

/-- Every enumerated function uses only palette colours on the vertices it was
constructed for. -/
theorem allColorings_usesOnly {S : Type u} {Seg : Type v} [DecidableEq S]
    (C : List Seg) (fallback : Seg) :
    ∀ (V : List S) {σ : S → Seg}, σ ∈ allColorings C fallback V → UsesOnly V C σ := by
  intro V
  induction V with
  | nil =>
      intro σ _ s hs
      cases hs
  | cons v rest ih =>
      intro σ hσ s hs
      simp only [allColorings, List.mem_flatMap, List.mem_map] at hσ
      obtain ⟨c, hc, τ, hτ, rfl⟩ := hσ
      by_cases hsv : s = v
      · subst s
        simpa using hc
      · have hrest : s ∈ rest := by
          rcases List.mem_cons.mp hs with h | h
          · exact absurd h hsv
          · exact h
        simpa [hsv] using ih hτ s hrest

/-- Pointwise completeness on the listed carrier: every palette-valued
colouring is represented by an enumerated function agreeing on `V`. -/
theorem allColorings_completeOn {S : Type u} {Seg : Type v} [DecidableEq S]
    (C : List Seg) (fallback : Seg) :
    ∀ (V : List S) (σ : S → Seg), UsesOnly V C σ →
      ∃ τ ∈ allColorings C fallback V, ∀ s ∈ V, τ s = σ s := by
  intro V
  induction V with
  | nil =>
      intro σ _
      exact ⟨fun _ => fallback, by simp [allColorings], fun _ hs => nomatch hs⟩
  | cons v rest ih =>
      intro σ huses
      have hv : σ v ∈ C := huses v List.mem_cons_self
      have htail : UsesOnly rest C σ :=
        fun s hs => huses s (List.mem_cons_of_mem v hs)
      obtain ⟨τ, hτ, hagree⟩ := ih σ htail
      let ext : S → Seg := fun s => if s = v then σ v else τ s
      refine ⟨ext, ?_, ?_⟩
      · simp only [allColorings, List.mem_flatMap]
        exact ⟨σ v, hv, List.mem_map.mpr ⟨τ, hτ, rfl⟩⟩
      · intro s hs
        by_cases hsv : s = v
        · subst s
          simp [ext]
        · have hsrest : s ∈ rest := by
            rcases List.mem_cons.mp hs with h | h
            · exact absurd h hsv
            · exact h
          simp [ext, hsv, hagree s hsrest]

/-- Global completeness is exactly where finite-carrier coverage is spent. -/
theorem allColorings_complete {S : Type u} {Seg : Type v} [DecidableEq S]
    (C : List Seg) (fallback : Seg) {V : List S} (hV : ∀ s : S, s ∈ V)
    (σ : S → Seg) (huses : UsesOnly V C σ) :
    σ ∈ allColorings C fallback V := by
  obtain ⟨τ, hτ, hagree⟩ := allColorings_completeOn C fallback V σ huses
  have heq : τ = σ := funext fun s => hagree s (hV s)
  rwa [heq] at hτ

/-! ### A certified argument-minimum over a list -/

/-- The standard structural argument-minimum, specialized to natural costs.
`List.minOn?` retains the first member when costs tie. -/
def argMin? {X : Type u} (cost : X → Nat) (xs : List X) : Option X :=
  xs.minOn? cost

theorem argMin_eq_none_iff {X : Type u} (cost : X → Nat) (xs : List X) :
    argMin? cost xs = none ↔ xs = [] := by
  cases xs <;> simp [argMin?, List.minOn?]

theorem argMin_mem {X : Type u} (cost : X → Nat)
    {xs : List X} {x : X} (hx : argMin? cost xs = some x) : x ∈ xs :=
  List.minOn?_mem (by simpa only [argMin?] using hx)

/-- The returned member costs no more than any member of the searched list. -/
theorem argMin_le_of_mem {X : Type u} (cost : X → Nat)
    {xs : List X} {x : X} (hx : argMin? cost xs = some x)
    {y : X} (hy : y ∈ xs) : cost x ≤ cost y := by
  have hne : xs ≠ [] := by
    intro hnil
    subst xs
    simp [argMin?, List.minOn?] at hx
  rw [argMin?, List.minOn?_eq_some_minOn hne] at hx
  injection hx with hx
  subst x
  exact List.apply_minOn_le_of_mem hy

/-- Regression for the executable tie contract: the first equal-cost member
is retained, rather than a later representative. -/
theorem argMin_first_tie_fixture :
    argMin? (fun _ : Bool => 7) [false, true] = some false := by
  decide

/-- All enumerated valid colourings, still as total functions. -/
def validColorings {S : Type u} {Seg : Type v} [DecidableEq S] [MergeState S]
    [DecidableEq Seg] (I : Invariant S) [DecidablePred I]
    (V : List S) (C : List Seg) (fallback : Seg) : List (S → Seg) :=
  (allColorings C fallback V).filter fun σ => decide (FiniteValid V σ I)

theorem mem_validColorings_iff {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (V : List S) (C : List Seg) (fallback : Seg) (σ : S → Seg) :
    σ ∈ validColorings I V C fallback ↔
      σ ∈ allColorings C fallback V ∧ FiniteValid V σ I := by
  simp [validColorings]

/-- Raw exact search: minimize palette usage over every valid colouring in the
explicit function space. -/
def minimumColoring? {S : Type u} {Seg : Type v} [DecidableEq S] [MergeState S]
    [DecidableEq Seg] (I : Invariant S) [DecidablePred I]
    (V : List S) (C : List Seg) (fallback : Seg) : Option (S → Seg) :=
  argMin? (usedColorCount V C) (validColorings I V C fallback)

theorem minimumColoring_spec {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (V : List S) (C : List Seg) (fallback : Seg) {σ : S → Seg}
    (hσ : minimumColoring? I V C fallback = some σ) :
    σ ∈ allColorings C fallback V
      ∧ FiniteValid V σ I
      ∧ ∀ τ, τ ∈ allColorings C fallback V → FiniteValid V τ I →
          usedColorCount V C σ ≤ usedColorCount V C τ := by
  have hm : σ ∈ validColorings I V C fallback :=
    argMin_mem _ hσ
  have hs := (mem_validColorings_iff I V C fallback σ).mp hm
  refine ⟨hs.1, hs.2, fun τ hτ hv => ?_⟩
  exact argMin_le_of_mem _ hσ
    ((mem_validColorings_iff I V C fallback τ).mpr ⟨hτ, hv⟩)

/-- Feasibility at an exact finite width. -/
def FiniteWidth {S : Type u} {Seg : Type v} [DecidableEq Seg] [MergeState S]
    (I : Invariant S) (V : List S) (C : List Seg) (n : Nat) : Prop :=
  ∃ σ : S → Seg, UsesOnly V C σ ∧ SegmentedIConfluent σ I
    ∧ usedColorCount V C σ = n

/-- `n` is feasible and no other feasible width is smaller. -/
def LeastSuch (F : Nat → Prop) (n : Nat) : Prop :=
  F n ∧ ∀ m, F m → n ≤ m

/-- A successful search result.  The minimality theorem ranges over *every*
valid total seam using the supplied palette, not merely over a table index. -/
structure MinimumSeam {S : Type u} {Seg : Type v} [DecidableEq Seg]
    [MergeState S] (I : Invariant S) (V : List S) (C : List Seg) where
  seam : S → Seg
  usesOnly : UsesOnly V C seam
  segmented : SegmentedIConfluent seam I
  minimum : ∀ τ : S → Seg, UsesOnly V C τ → SegmentedIConfluent τ I →
    usedColorCount V C seam ≤ usedColorCount V C τ

theorem MinimumSeam.leastSuch {S : Type u} {Seg : Type v} [DecidableEq Seg]
    [MergeState S] {I : Invariant S} {V : List S} {C : List Seg}
    (m : MinimumSeam I V C) :
    LeastSuch (FiniteWidth I V C) (usedColorCount V C m.seam) := by
  constructor
  · exact ⟨m.seam, m.usesOnly, m.segmented, rfl⟩
  · rintro n ⟨τ, huses, hseg, rfl⟩
    exact m.minimum τ huses hseg

/-- Turn a raw minimum into its proof-carrying form.  Carrier coverage is used
once, to promote the finite validity pair to a global seam certificate. -/
def certifyMinimum {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (V : List S) (hV : ∀ s : S, s ∈ V) (C : List Seg) (fallback : Seg)
    {σ : S → Seg} (hσ : minimumColoring? I V C fallback = some σ) :
    MinimumSeam I V C where
  seam := σ
  usesOnly := allColorings_usesOnly C fallback V (minimumColoring_spec I V C fallback hσ).1
  segmented := (segmented_iff_properColoring hV).mpr
    ⟨(minimumColoring_spec I V C fallback hσ).2.1.1,
     seamStableOn_of_pool hV (minimumColoring_spec I V C fallback hσ).2.1.2⟩
  minimum := by
    intro τ huses hseg
    have hτall := allColorings_complete C fallback hV τ huses
    have hτvalid : FiniteValid V τ I :=
      (segmentedOn_iff_properColoring.mp (segmentedOn_of_segmented hseg V))
    exact (minimumColoring_spec I V C fallback hσ).2.2 τ hτall hτvalid

/-- **EXHAUSTIVE REFUSAL.** A `none` result rules out every valid seam whose
values on the covered carrier lie in the supplied palette.  It says nothing
about colours outside `C` or carriers not covered by `V`. -/
theorem minimumColoring_none_exhaustive {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (V : List S) (hV : ∀ s : S, s ∈ V) (C : List Seg) (fallback : Seg)
    (hraw : minimumColoring? I V C fallback = none) :
    ∀ σ : S → Seg, UsesOnly V C σ → ¬ SegmentedIConfluent σ I := by
  intro σ huses hseg
  have hempty : validColorings I V C fallback = [] :=
    (argMin_eq_none_iff (usedColorCount V C) _).mp hraw
  have hσall := allColorings_complete C fallback hV σ huses
  have hvalid : FiniteValid V σ I :=
    segmentedOn_iff_properColoring.mp (segmentedOn_of_segmented hseg V)
  have hmem : σ ∈ validColorings I V C fallback :=
    (mem_validColorings_iff I V C fallback σ).mpr ⟨hσall, hvalid⟩
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

/-- The two possible certified results of finite synthesis.  Unlike `Option`,
the refusal constructor retains the exhaustive negative theorem. -/
inductive MinimumSynthesis {S : Type u} {Seg : Type v} [DecidableEq Seg]
    [MergeState S] (I : Invariant S) (V : List S) (C : List Seg) : Type (max u v) where
  | found (minimum : MinimumSeam I V C)
  | refused (exhaustive : ∀ σ : S → Seg, UsesOnly V C σ →
      ¬ SegmentedIConfluent σ I)

/-- **The exact finite synthesizer.** The positive branch carries a valid
least-width seam; the negative branch carries the exhaustive refusal theorem. -/
def synthesizeMinimumSeam {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (V : List S) (hV : ∀ s : S, s ∈ V) (C : List Seg) (fallback : Seg) :
    MinimumSynthesis I V C :=
  match h : minimumColoring? I V C fallback with
  | none => .refused (minimumColoring_none_exhaustive I V hV C fallback h)
  | some σ => .found (certifyMinimum I V hV C fallback (σ := σ) h)

/-- Forget the refusal proof only when an `Option`-shaped API is required. -/
def MinimumSynthesis.toOption {S : Type u} {Seg : Type v} [DecidableEq Seg]
    [MergeState S] {I : Invariant S} {V : List S} {C : List Seg} :
    MinimumSynthesis I V C → Option (MinimumSeam I V C)
  | .found m => some m
  | .refused _ => none

def synthesizeMinimumSeam? {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (V : List S) (hV : ∀ s : S, s ∈ V) (C : List Seg) (fallback : Seg) :
    Option (MinimumSeam I V C) :=
  (synthesizeMinimumSeam I V hV C fallback).toOption

/-- The search is total in the semantic sense by its result type, and either
branch exposes its entire certificate to callers. -/
theorem minimumSeam_search_total {S : Type u} {Seg : Type v}
    [DecidableEq S] [MergeState S] [DecidableEq Seg]
    (I : Invariant S) [DecidablePred I]
    (V : List S) (hV : ∀ s : S, s ∈ V) (C : List Seg) (fallback : Seg) :
    (match synthesizeMinimumSeam I V hV C fallback with
      | .found m => LeastSuch (FiniteWidth I V C) (usedColorCount V C m.seam)
      | .refused _ => ∀ σ, UsesOnly V C σ → ¬ SegmentedIConfluent σ I) := by
  cases synthesizeMinimumSeam I V hV C fallback with
  | found m => exact m.leastSuch
  | refused h => exact h

/-! ### Exact run: the pin clash needs exactly two colours -/

def pinMinimumSearch : Option (MinimumSeam pinInv pinStates [false, true]) :=
  synthesizeMinimumSeam? pinInv pinStates pinStates_complete [false, true] false

theorem pinMinimumSearch_isSome : pinMinimumSearch.isSome = true := by
  decide

def pinMinimum : MinimumSeam pinInv pinStates [false, true] :=
  pinMinimumSearch.get (by decide)

/-- The computed optimum is nontrivial and exact: the single clash edge forces
two colours, and exhaustive synthesis attains two. -/
theorem pinMinimum_uses_two_colors :
    usedColorCount pinStates [false, true] pinMinimum.seam = 2 := by
  decide

theorem pin_minimum_is_exact :
    LeastSuch (FiniteWidth pinInv pinStates [false, true]) 2 := by
  have h := pinMinimum.leastSuch
  rwa [pinMinimum_uses_two_colors] at h

end Uwueave.SeamColoring
