/-
# Uwueave.SeamAlgebra — how seams compose: one coordination point, or two?

`Segmented.lean` and `Seams.lean` hold three worked seams — budget, epoch,
schema — and nothing at all connecting them. So a schema author with two
seamed fields is left holding exactly the question the refined judgement was
invented to answer and does not: *my quota field coordinates at re-allocation,
my store coordinates at the version bump — is that one coordination point, or
two?* Whittaker–Hellerstein ("Interactive Checks for Coordination Avoidance",
VLDB'19) give the per-invariant judgement; the composition of segmentations is
not in that paper, and it is what a real schema actually asks.

This file is that algebra. Five laws, chased rather than assumed — two hold
outright, one holds only with a hypothesis whose absence is refuted by a
witness, one holds in a conjoined form and fails standalone (also with a
witness), and the fifth is a negative strong enough to be worth having:

  * **§1 Product** (holds) — `product_segmented`, the mirror of
    `Confluence.product_iconfluent`. Two seamed fields give a seamed record
    over the *pair* seam. This is the "two fields, two seams" baseline, and it
    is the reason the answer to the title question is never worse than "two".
  * **§2 Refinement** (⚠ FAILS) — a finer seam is *not* automatically a seam.
    `refine_freeWithinSeam` transports the free-running half along any
    refinement; `refinement_fails` is the witness that the *closure* half does
    not, so `SegmentedIConfluent` genuinely does not descend along refinement.
    The repair, `segmented_of_finer`, names the missing ingredient exactly:
    `SeamStable` — the finer projection's own fibers must be merge-closed.
  * **§3 THE PRIZE — seam merging** (holds, with a named condition).
    `seam_substitute` is the engine: a seam `σ` may be replaced by a seam `τ`
    when `τ` *determines* `σ` on legal states and `τ` is fiber-stable there.
    (Stability is also *necessary* — `seamStableOn_of_segmented`; determination
    is not, which is why the engine is stated as an implication.)
    `linked_segmented` is the payoff a schema author can act on: **two seams
    collapse to one when the invariant links them** — when well-formedness says
    `σ_B (field B) = g (σ_A (field A))`, the conjunction is segmented over
    `σ_A` **alone**. The link is a *cross-field* invariant, the shape that gets
    no free ride anywhere else in this library (`Spec.cross`); here it is
    precisely what buys the saving.
  * **§4 Free absorption** (holds conjoined, ⚠ FAILS standalone) —
    `absorb_iconfluent`: an I-confluent invariant rides a seamed one for
    nothing. But `free_alone_not_segmented` shows a coordination-*free*
    invariant is not segmented over an arbitrary `σ` — the closure conjunct is
    a fact about the seam, not about the invariant, and a free invariant has
    no closure half to donate.
  * **§5 The negative worth having** — `seam_must_separate_right` /
    `_left`: **every** joint seam must separate **every** clash pair the
    document can embed. Instantiated on a two-field document (schema store ×
    budgeted quota, §7), that yields `no_schema_only_seam` and
    `no_quota_only_seam`: for every type `T` in every universe and every
    candidate projection of a single field, the conjunction is not segmented
    over it. This document genuinely needs a seam that watches **both** fields
    — two coordination points, proved, not conjectured.

    §5 closes with the characterisation those negatives are instances of:
    `left_only_seam_iff` / `right_only_seam_iff` — a single-field seam segments
    an *unlinked* two-field conjunction **iff** the other field is
    coordination-free outright. So for a plain conjunction there is no clever
    projection to look for: either the second field never needed coordination
    (§4's absorption), or the invariant must be changed to link the seams (§3),
    or it is two.

§6 packages the useful ones as `SegVerdict` combinators (in `Spec`'s
`SegVerdict` namespace, so they are available by dot-notation, without editing
`Spec.lean`), and §7 works the two documents the algebra distinguishes:

  * `twoFieldSegVerdict` — schema store × budgeted quota, unlinked: seam =
    `(version, allocation)`, and §5 proves no single-field seam exists.
  * `flagDaySegVerdict` — the *same two fields*, with the allocation policy
    made a function of the schema version (`allocOf`): seam = the version
    **alone**. Re-allocation stops being a coordination event and rides the
    flag day. `linkedWF_strengthens` / `link_is_a_real_constraint` price it:
    the saving is bought with states you may no longer represent.

## The reading, in one line

**For a plain two-field conjunction, one coordination point exists iff one of
the fields is coordination-free; to get down to one when both clash you must
change the invariant — link the seams, and pay in states you may no longer
represent.**

## Honest boundary

§5 quantifies over every projection that reads a single field, in every
universe — that is the sense in which "one coordination point" is refuted. It
does **not** rule out every conceivable coarsening of the pair seam that still
reads both fields; what it does prove about those is `seam_must_separate_*`:
any such seam must keep both clash pairs in different fibers, so it must
observe the version *and* the allocation. That is the strongest form the
witnesses support, and it is stated as itself rather than as the stronger
claim.
-/
import Uwueave.Seams

namespace Uwueave.SeamAlgebra

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Spec Uwueave.Seams

universe u v w z

/-! ## §0. Seam hygiene — the two halves of the judgement, named separately.

`SegmentedIConfluent σ I` is a conjunction: merges inside a fiber preserve `I`,
and merges inside a fiber *stay* in the fiber. Almost every law below holds or
fails on the **second** half alone, so it gets a name of its own. -/

/-- **Fiber stability, relative to an invariant.** Merging two legal states of
one `σ`-fiber cannot leave the fiber. This is exactly the second conjunct of
`SegmentedIConfluent`, isolated: it is a property of the *seam* (given the
invariant's legal states), not of the invariant's preservation behaviour. -/
def SeamStableOn {S : Type u} {Seg : Type v} [MergeState S]
    (I : Invariant S) (σ : S → Seg) : Prop :=
  ∀ x y : S, I x → I y → σ x = σ y → σ (x ⊔ y) = σ x

/-- **Fiber stability, unconditionally** — the seam's fibers are merge-closed
for *all* states, legal or not. The stronger, invariant-free form: a projection
with this property is a seam candidate for every invariant at once. -/
def SeamStable {S : Type u} {Seg : Type v} [MergeState S]
    (σ : S → Seg) : Prop :=
  ∀ x y : S, σ x = σ y → σ (x ⊔ y) = σ x

theorem seamStableOn_of_seamStable {S : Type u} {Seg : Type v} [MergeState S]
    {I : Invariant S} {σ : S → Seg} (h : SeamStable σ) : SeamStableOn I σ :=
  fun x y _ _ hσ => h x y hσ

/-- **The decomposition.** The segmented judgement is precisely "fiberwise
preservation, and a stable seam". Every law in this file is proved by handling
these two halves separately, and the interesting failures are all in the
second one. -/
theorem segmented_iff {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I : Invariant S} :
    SegmentedIConfluent σ I ↔
      ((∀ x y : S, σ x = σ y → I x → I y → I (x ⊔ y)) ∧ SeamStableOn I σ) := by
  constructor
  · intro h
    exact ⟨fun x y hσ hx hy => (h x y hσ hx hy).1,
           fun x y hx hy hσ => (h x y hσ hx hy).2⟩
  · intro h x y hσ hx hy
    exact ⟨h.1 x y hσ hx hy, h.2 x y hx hy hσ⟩

/-- A seam that is a **merge homomorphism** is stable: equal seam values merge
by idempotence. This is the cheap sufficient condition, and it is how every
seam in this library qualifies — `Prod.fst` on a componentwise-merged record is
a homomorphism by `rfl`. -/
theorem seamStable_of_hom {S : Type u} {Seg : Type v} [MergeState S] [MergeState Seg]
    {σ : S → Seg} (h : ∀ x y : S, σ (x ⊔ y) = σ x ⊔ σ y) : SeamStable σ := by
  intro x y hσ
  rw [h, ← hσ, merge_idem]

/-- The workhorse instance: the first-field projection of a record is a stable
seam. Every worked seam in `Segmented.lean` and `Seams.lean` is this one. -/
theorem seamStable_fst {A : Type u} {B : Type v} [MergeState A] [MergeState B] :
    SeamStable (S := A × B) Prod.fst :=
  seamStable_of_hom (fun _ _ => rfl)

/-- Any `SegmentedIConfluent` proof *contains* a stability proof — recorded so
the negative results below can be read as "this candidate seam fails the second
conjunct", which is what they all in fact are. -/
theorem seamStableOn_of_segmented {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I : Invariant S} (h : SegmentedIConfluent σ I) :
    SeamStableOn I σ :=
  (segmented_iff.mp h).2

/-! ## §1. The product law — two fields, two seams, and it composes. -/

/-- **The product lift for seams** — the mirror of
`Confluence.product_iconfluent`. Two independently-seamed fields give a seamed
record, over the *pair* seam `(σ_A, σ_B)`: replicas that agree on both fields'
seams merge safely and stay in both fibers.

Read operationally, this is the baseline answer to "one coordination point or
two?": it is never worse than two, because the pair seam always works. The
whole interest of §3 and §5 is whether you can do better than the pair.

⚠ Same quantifier caveat as the I-confluent lift: this covers invariants that
mention **one field each**. A cross-field invariant is not of this shape — and
in §3 that is not a limitation but the mechanism. -/
theorem product_segmented {A : Type u} {B : Type v} {SegA : Type w} {SegB : Type z}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    {σA : A → SegA} {σB : B → SegB}
    (hA : SegmentedIConfluent σA IA) (hB : SegmentedIConfluent σB IB) :
    SegmentedIConfluent (S := A × B) (fun p => (σA p.1, σB p.2))
      (fun p => IA p.1 ∧ IB p.2) := by
  intro x y hσ hx hy
  have h1 : σA x.1 = σA y.1 := congrArg Prod.fst hσ
  have h2 : σB x.2 = σB y.2 := congrArg Prod.snd hσ
  have hA1 := hA x.1 y.1 h1 hx.1 hy.1
  have hB1 := hB x.2 y.2 h2 hx.2 hy.2
  refine ⟨⟨hA1.1, hB1.1⟩, ?_⟩
  show (σA (x.1 ⊔ y.1), σB (x.2 ⊔ y.2)) = (σA x.1, σB x.2)
  rw [hA1.2, hB1.2]

/-- **The keyed lift for seams** — the mirror of `Confluence.pi_iconfluent`. A
per-key invariant seamed at every key is seamed over the whole map, with the
seam being the *vector* of per-key seams. Note what that says operationally: a
map of independently-seamed entries coordinates per entry, and the document's
seam is as wide as its key set. -/
theorem pi_segmented {K : Type u} {V : Type v} {Seg : Type w} [MergeState V]
    {J : K → Invariant V} {σ : K → V → Seg}
    (h : ∀ k, SegmentedIConfluent (σ k) (J k)) :
    SegmentedIConfluent (S := K → V) (fun f k => σ k (f k))
      (fun f => ∀ k, J k (f k)) := by
  intro x y hσ hx hy
  refine ⟨fun k => (h k (x k) (y k) (congrFun hσ k) (hx k) (hy k)).1, ?_⟩
  funext k
  show σ k (x k ⊔ y k) = σ k (x k)
  exact (h k (x k) (y k) (congrFun hσ k) (hx k) (hy k)).2

/-- **Conjunction on the same state, over the same seam** — the mirror of
`Confluence.and_iconfluent`. Two invariants that coordinate at the *same* seam
still coordinate only there. -/
theorem and_segmented {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I J : Invariant S}
    (hI : SegmentedIConfluent σ I) (hJ : SegmentedIConfluent σ J) :
    SegmentedIConfluent σ (fun s => I s ∧ J s) :=
  fun x y hσ hx hy =>
    ⟨⟨(hI x y hσ hx.1 hy.1).1, (hJ x y hσ hx.2 hy.2).1⟩, (hI x y hσ hx.1 hy.1).2⟩

/-! ## §2. Refinement — ⚠ a finer seam is NOT automatically a seam. -/

/-- `τ` is **finer than** `σ`: it distinguishes at least as much, so `σ`
factors through it as far as fibers are concerned. Operationally, a finer seam
is one you coordinate on *more* often. -/
def Finer {S : Type u} {Seg : Type v} {T : Type w} (τ : S → T) (σ : S → Seg) : Prop :=
  ∀ x y : S, τ x = τ y → σ x = σ y

/-- Factoring is the usual way to exhibit refinement: if `σ = f ∘ τ` then `τ`
is finer than `σ`. -/
theorem finer_of_factors {S : Type u} {Seg : Type v} {T : Type w}
    {τ : S → T} {σ : S → Seg} (f : T → Seg) (h : ∀ s, σ s = f (τ s)) :
    Finer τ σ :=
  fun x y hxy => (h x).trans ((congrArg f hxy).trans (h y).symm)

/-- **The half that does transport.** Coordinating *more* never breaks
invariant preservation: same-fiber states of a finer projection are same-fiber
states of the coarser seam, so their merge is legal. This is the honest content
of "a finer seam coordinates more often but is still safe" — and it is only
half of the judgement. -/
theorem refine_freeWithinSeam {S : Type u} {Seg : Type v} {T : Type w} [MergeState S]
    {σ : S → Seg} {τ : S → T} {I : Invariant S}
    (hseg : SegmentedIConfluent σ I) (hfiner : Finer τ σ)
    {x y : S} (hτ : τ x = τ y) (hx : I x) (hy : I y) : I (x ⊔ y) :=
  (hseg x y (hfiner x y hτ) hx hy).1

/-- **The repair, with the missing ingredient named.** Refinement transports
the whole judgement as soon as the finer projection is itself fiber-stable —
which is exactly what `refinement_fails` shows is not automatic. -/
theorem segmented_of_finer {S : Type u} {Seg : Type v} {T : Type w} [MergeState S]
    {σ : S → Seg} {τ : S → T} {I : Invariant S}
    (hseg : SegmentedIConfluent σ I) (hfiner : Finer τ σ)
    (hstable : SeamStableOn I τ) : SegmentedIConfluent τ I :=
  fun x y hτ hx hy => ⟨(hseg x y (hfiner x y hτ) hx hy).1, hstable x y hx hy hτ⟩

/-- A candidate finer seam for the schema store: the version, **plus** the
derived flag "records 0 and 1 are both present". It is a perfectly ordinary
projection, it is finer than the version seam (`versionAndBoth_finer`), and it
is not a seam — the conjunctive observation is not merge-closed, because two
replicas can each hold one half of it. -/
def versionAndBoth (s : SchemaState) : Nat × Bool := (s.1, s.2 0 && s.2 1)

theorem versionAndBoth_finer : Finer versionAndBoth (Prod.fst : SchemaState → Nat) :=
  finer_of_factors Prod.fst (fun _ => rfl)

/-- ⚠ **THE REFUTATION: segmentation does not descend along refinement.**
`SchemaWF` is segmented over the version (`Seams.schema_segmented`), and
`versionAndBoth` is finer than the version — yet the invariant is *not*
segmented over it. Two version-1 replicas, one holding record 0 and the other
record 1, agree on the finer projection (neither has both records, so the flag
is `false` on each) and are each perfectly legal; their merge holds both
records, the flag flips to `true`, and the merge has left the fiber. Nothing
about the invariant broke — `SchemaWF` still holds — it is the *seam* that
failed, which is why the second conjunct of `SegmentedIConfluent` is
load-bearing and why the law needs `SeamStableOn` (`segmented_of_finer`).

Design rule extracted: a seam must be a merge-closed projection. Any seam
built from a *conjunctive* observation over grow-only fields ("both flags
set", "the set is still empty", "no conflict yet") is not one, and refining a
good seam with such an observation destroys it. -/
theorem refinement_fails :
    ¬ SegmentedIConfluent (S := SchemaState) versionAndBoth (SchemaWF tightBound) := by
  intro h
  have hbad := (h (1, fun n => n == 0) (1, fun n => n == 1) (by decide)
    (fun n hn => by simp at hn; subst hn; decide)
    (fun n hn => by simp at hn; subst hn; decide)).2
  exact absurd hbad (by decide)

/-- The positive half of §2, on the same pair that refutes the negative half:
the merge really is legal — it is only the fiber that was left. -/
example : SchemaWF tightBound (((1, fun n => n == 0) : SchemaState) ⊔ (1, fun n => n == 1)) :=
  refine_freeWithinSeam (schema_segmented tightBound) versionAndBoth_finer
    (by decide)
    (fun n hn => by simp at hn; subst hn; decide)
    (fun n hn => by simp at hn; subst hn; decide)

/-! ## §3. THE PRIZE — when two seams become one coordination point. -/

/-- **The seam-substitution engine.** A seam `σ` may be replaced by a
projection `τ` as soon as, on legal states, (i) `τ` **determines** `σ` — same
`τ`-fiber implies same `σ`-fiber, so `σ`'s preservation guarantee is inherited
— and (ii) `τ` is **fiber-stable**, so the replacement is a seam and not just a
partition. Every merging result below is this theorem plus a way of discharging
(i).

Note the shape: (i) is refinement relativised to legal states, and (ii) is the
ingredient §2 proves is not free. `segmented_of_finer` is the special case
where (i) holds for all states. (ii) is not merely sufficient but *necessary*
— `seamStableOn_of_segmented` — whereas (i) is only sufficient, which is why
this is an implication and not an equivalence. -/
theorem seam_substitute {S : Type u} {Seg : Type v} {T : Type w} [MergeState S]
    {σ : S → Seg} {τ : S → T} {I : Invariant S}
    (hseg : SegmentedIConfluent σ I)
    (hdet : ∀ x y : S, I x → I y → τ x = τ y → σ x = σ y)
    (hstable : SeamStableOn I τ) : SegmentedIConfluent τ I :=
  fun x y hτ hx hy => ⟨(hseg x y (hdet x y hx hy hτ) hx hy).1, hstable x y hx hy hτ⟩

/-- The **linked** two-field invariant: each field legal, *and* field B's seam
value pinned to a function of field A's. The third conjunct is a genuinely
cross-field invariant — the shape `Spec.cross` exists to say gets no free ride
— and it is the entire mechanism of §3: it is what makes field A's seam
sufficient to know field B's. -/
def LinkedInv {A : Type u} {B : Type v} {SegA : Type w} {SegB : Type z}
    (IA : Invariant A) (IB : Invariant B) (σA : A → SegA) (σB : B → SegB)
    (g : SegA → SegB) : Invariant (A × B) :=
  fun p => IA p.1 ∧ IB p.2 ∧ σB p.2 = g (σA p.1)

/-- The linked invariant is segmented over the **pair** seam — the product law
(§1) extended across the link. The link survives because *both* component
seams are stable inside their fibers: `σ_B` of the merge is `σ_B x.2`, `σ_A` of
the merge is `σ_A x.1`, and the equation between them is carried along
unchanged. (This is why the link is not separately liftable: on its own it has
no closure half, and it rides on the other two conjuncts'.) -/
theorem linked_pair_segmented {A : Type u} {B : Type v} {SegA : Type w} {SegB : Type z}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    {σA : A → SegA} {σB : B → SegB} (g : SegA → SegB)
    (hA : SegmentedIConfluent σA IA) (hB : SegmentedIConfluent σB IB) :
    SegmentedIConfluent (S := A × B) (fun p => (σA p.1, σB p.2))
      (LinkedInv IA IB σA σB g) := by
  intro x y hσ hx hy
  have h1 : σA x.1 = σA y.1 := congrArg Prod.fst hσ
  have h2 : σB x.2 = σB y.2 := congrArg Prod.snd hσ
  have hA1 := hA x.1 y.1 h1 hx.1 hy.1
  have hB1 := hB x.2 y.2 h2 hx.2.1 hy.2.1
  refine ⟨⟨hA1.1, hB1.1, ?_⟩, ?_⟩
  · show σB (x.2 ⊔ y.2) = g (σA (x.1 ⊔ y.1))
    rw [hB1.2, hA1.2]
    exact hx.2.2
  · show (σA (x.1 ⊔ y.1), σB (x.2 ⊔ y.2)) = (σA x.1, σB x.2)
    rw [hA1.2, hB1.2]

/-- **THE SEAM-MERGING THEOREM — two coordination points collapse into one.**

If field A is segmented over `σ_A`, field B over `σ_B`, and well-formedness
**links** them — `σ_B (field B) = g (σ_A (field A))` for some function `g` —
then the whole document is segmented over `σ_A` *alone*. Field B's seam is not
a second coordination point: holding `σ_A` fixed already holds `σ_B` fixed, so
B's re-seaming happens *at* A's coordination event and nowhere else.

This is the answer to the question a schema asks, and the condition is
checkable by reading the schema: **is some field's seam value determined by
another field's?** If yes, that other field's seam is the document's single
coordination point. If no — if the document is a plain conjunction of two
clashing fields — `left_only_seam_iff` says no single-field seam exists at all,
so the choice is to add the link or to coordinate twice.

The proof is `seam_substitute` applied to `linked_pair_segmented`: the link
discharges "determines" (equal `σ_A` forces equal `σ_B`), and `hA` discharges
stability. The price is stated in §7: the link is a real constraint, and the
states it forbids are the cost of the saving. -/
theorem linked_segmented {A : Type u} {B : Type v} {SegA : Type w} {SegB : Type z}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    {σA : A → SegA} {σB : B → SegB} (g : SegA → SegB)
    (hA : SegmentedIConfluent σA IA) (hB : SegmentedIConfluent σB IB) :
    SegmentedIConfluent (S := A × B) (fun p => σA p.1)
      (LinkedInv IA IB σA σB g) := by
  refine seam_substitute (linked_pair_segmented g hA hB) ?_ ?_
  · intro x y hx hy hτ
    show (σA x.1, σB x.2) = (σA y.1, σB y.2)
    rw [hx.2.2, hy.2.2, hτ]
  · intro x y hx hy hτ
    show σA (x.1 ⊔ y.1) = σA x.1
    exact (hA x.1 y.1 hτ hx.1 hy.1).2

/-- The dual reading of the same theorem: a *dominated* seam is one whose value
is recoverable from the dominating seam, and a dominated field never needs its
own coordination event — agreement on `σ_A` alone already pins `σ_B` through
the merge. Note the hypothesis that is *absent*: field A's segmentation plays
no part in this half, because the link does all the work. -/
theorem dominated_seam_needs_no_coordination
    {A : Type u} {B : Type v} {SegA : Type w} {SegB : Type z}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    {σA : A → SegA} {σB : B → SegB} (g : SegA → SegB)
    (hB : SegmentedIConfluent σB IB)
    {x y : A × B} (hτ : σA x.1 = σA y.1)
    (hx : LinkedInv IA IB σA σB g x) (hy : LinkedInv IA IB σA σB g y) :
    σB (x ⊔ y).2 = σB x.2 :=
  (hB x.2 y.2 (by rw [hx.2.2, hy.2.2, hτ]) hx.2.1 hy.2.1).2

/-! ## §4. Free absorption — and the ⚠ standalone version that fails. -/

/-- **Free rides a seam for nothing.** An I-confluent invariant conjoined with a
segmented one is segmented over the *same* seam: the free conjunct is preserved
by every merge whatsoever, and the segmented conjunct donates the fiber-closure
half. Adding a coordination-free field to a seamed document costs no new
coordination — the expected law, and it holds. -/
theorem absorb_iconfluent {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I J : Invariant S}
    (hI : SegmentedIConfluent σ I) (hJ : IConfluent J) :
    SegmentedIConfluent σ (fun s => I s ∧ J s) :=
  fun x y hσ hx hy =>
    ⟨⟨(hI x y hσ hx.1 hy.1).1, hJ x y hx.2 hy.2⟩, (hI x y hσ hx.1 hy.1).2⟩

/-- The product-shaped absorption: a free *field* alongside a seamed field
keeps the seamed field's seam, unchanged. (The pair seam of §1 would report
`(σ_A, ())`; this says the `()` may be dropped, which is the whole content of
"free fields are not coordination points".) -/
theorem absorb_free_field {A : Type u} {B : Type v} {SegA : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    {σA : A → SegA} (hA : SegmentedIConfluent σA IA) (hB : IConfluent IB) :
    SegmentedIConfluent (S := A × B) (fun p => σA p.1) (fun p => IA p.1 ∧ IB p.2) :=
  fun x y hσ hx hy =>
    ⟨⟨(hA x.1 y.1 hσ hx.1 hy.1).1, hB x.2 y.2 hx.2 hy.2⟩, (hA x.1 y.1 hσ hx.1 hy.1).2⟩

/-- ⚠ **A coordination-free invariant is NOT segmented over an arbitrary seam.**
`SchemaWF (fun v => 10 * (v + 1))` is the widening migration —
`Seams.widening_needs_no_seam` proves it needs no coordination at all — and it
is still not `SegmentedIConfluent` over `versionAndBoth`. The invariant half is
trivially fine; it is the fiber that is left.

The moral, and the reason "free things ride any seam for nothing" is stated
only in its conjoined form (`absorb_iconfluent`): the closure conjunct is a
fact about the **seam**, not about the invariant, and a free invariant has no
closure half of its own to donate. A free conjunct rides a *seam that is
already stable*; it cannot make a bad projection into a seam. -/
theorem free_alone_not_segmented :
    ¬ SegmentedIConfluent (S := SchemaState) versionAndBoth
      (SchemaWF (fun v => 10 * (v + 1))) := by
  intro h
  have hbad := (h (1, fun n => n == 0) (1, fun n => n == 1) (by decide)
    (fun n hn => by simp at hn; subst hn; decide)
    (fun n hn => by simp at hn; subst hn; decide)).2
  exact absurd hbad (by decide)

/-- The repair for the standalone form: a free invariant *is* segmented over
any seam whose fibers are merge-closed. With `seamStableOn_of_segmented` for
the converse this pins the law exactly — for an I-confluent `I`, stability of
`σ` is necessary *and* sufficient for `SegmentedIConfluent σ I`, so
`free_alone_not_segmented` is not a curiosity but the generic case for a badly
chosen projection. -/
theorem iconfluent_segmented_of_seamStable {S : Type u} {Seg : Type v} [MergeState S]
    {σ : S → Seg} {I : Invariant S} (hI : IConfluent I) (hσ : SeamStableOn I σ) :
    SegmentedIConfluent σ I :=
  fun x y hfib hx hy => ⟨hI x y hx hy, hσ x y hx hy hfib⟩

/-! ## §5. The negative worth having — a seam must separate every clash. -/

/-- **A seam is refuted by any fiber containing a clash.** If two legal
field-B states whose merge is illegal sit in a single `τ`-fiber (with a common
legal field-A value), then `τ` is not a seam for the conjunction — the fiber
promised free merging and the merge is illegal.

This is the engine of every impossibility below, and its contrapositive is the
useful design statement: **every valid joint seam must separate every clash
pair the document can embed.** -/
theorem seam_must_separate_right {A : Type u} {B : Type v} {T : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    (τ : A × B → T) (a : A) (ha : IA a) (b₁ b₂ : B)
    (h₁ : IB b₁) (h₂ : IB b₂) (hbad : ¬ IB (b₁ ⊔ b₂))
    (hτ : τ (a, b₁) = τ (a, b₂)) :
    ¬ SegmentedIConfluent τ (fun p : A × B => IA p.1 ∧ IB p.2) := by
  intro h
  exact hbad ((h (a, b₁) (a, b₂) hτ ⟨ha, h₁⟩ ⟨ha, h₂⟩).1).2

/-- The mirror: a clash in the **left** field refutes any seam that fails to
separate it. -/
theorem seam_must_separate_left {A : Type u} {B : Type v} {T : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    (τ : A × B → T) (b : B) (hb : IB b) (a₁ a₂ : A)
    (h₁ : IA a₁) (h₂ : IA a₂) (hbad : ¬ IA (a₁ ⊔ a₂))
    (hτ : τ (a₁, b) = τ (a₂, b)) :
    ¬ SegmentedIConfluent τ (fun p : A × B => IA p.1 ∧ IB p.2) := by
  intro h
  exact hbad ((h (a₁, b) (a₂, b) hτ ⟨h₁, hb⟩ ⟨h₂, hb⟩).1).1

/-- **No seam that reads only field A can segment a document whose field B
clashes** — for every target type `T`, in every universe, and every projection
`τ` of field A. A seam blind to field B keeps B's whole clash pair in one
fiber, and the fiber's promise is exactly what fails.

This is the precise sense in which two coordination points can be *necessary*:
not "we could not find one seam", but "no projection of a single field is
one". -/
theorem no_left_only_seam {A : Type u} {B : Type v} {T : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    (τ : A → T) (a : A) (ha : IA a) (b₁ b₂ : B)
    (h₁ : IB b₁) (h₂ : IB b₂) (hbad : ¬ IB (b₁ ⊔ b₂)) :
    ¬ SegmentedIConfluent (fun p : A × B => τ p.1)
      (fun p : A × B => IA p.1 ∧ IB p.2) :=
  seam_must_separate_right _ a ha b₁ b₂ h₁ h₂ hbad rfl

/-- The mirror: no seam reading only field B segments a document whose field A
clashes. -/
theorem no_right_only_seam {A : Type u} {B : Type v} {T : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    (τ : B → T) (b : B) (hb : IB b) (a₁ a₂ : A)
    (h₁ : IA a₁) (h₂ : IA a₂) (hbad : ¬ IA (a₁ ⊔ a₂)) :
    ¬ SegmentedIConfluent (fun p : A × B => τ p.2)
      (fun p : A × B => IA p.1 ∧ IB p.2) :=
  seam_must_separate_left _ b hb a₁ a₂ h₁ h₂ hbad rfl

/-- **The characterisation — exactly when one coordination point suffices for a
plain two-field conjunction.** A seam that reads only field A segments the
document **iff** it is a seam for field A *and field B is coordination-free
outright*. There is no third possibility: for an unlinked conjunction, "one
coordination point" is not a cleverer choice of projection, it is the statement
that the other field never needed coordination at all.

Both inhabitance hypotheses are load-bearing and are exactly the right ones —
each direction of the forward implication plants the *other* field at a legal
value, and with an uninhabited invariant there is nothing to plant and the
claim is vacuous.

Read against §3: the two ways out of "two coordination points" are now both
theorems and they are disjoint. Either the second field is free (this theorem,
`←` direction, i.e. `absorb_free_field`), or the invariant itself is changed to
link the seams (`linked_segmented`) — which buys the saving with states you may
no longer represent (`link_is_a_real_constraint`). Nothing else works. -/
theorem left_only_seam_iff {A : Type u} {B : Type v} {T : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    (τ : A → T) {a₀ : A} {b₀ : B} (ha₀ : IA a₀) (hb₀ : IB b₀) :
    SegmentedIConfluent (fun p : A × B => τ p.1) (fun p : A × B => IA p.1 ∧ IB p.2)
      ↔ (SegmentedIConfluent τ IA ∧ IConfluent IB) := by
  constructor
  · intro h
    constructor
    · intro x y hτ hx hy
      have hm := h (x, b₀) (y, b₀) hτ ⟨hx, hb₀⟩ ⟨hy, hb₀⟩
      exact ⟨hm.1.1, hm.2⟩
    · intro x y hx hy
      exact (h (a₀, x) (a₀, y) rfl ⟨ha₀, hx⟩ ⟨ha₀, hy⟩).1.2
  · intro h
    exact absorb_free_field h.1 h.2

/-- The mirror characterisation, for a seam that reads only field B. -/
theorem right_only_seam_iff {A : Type u} {B : Type v} {T : Type w}
    [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}
    (τ : B → T) {a₀ : A} {b₀ : B} (ha₀ : IA a₀) (hb₀ : IB b₀) :
    SegmentedIConfluent (fun p : A × B => τ p.2) (fun p : A × B => IA p.1 ∧ IB p.2)
      ↔ (IConfluent IA ∧ SegmentedIConfluent τ IB) := by
  constructor
  · intro h
    constructor
    · intro x y hx hy
      exact (h (x, b₀) (y, b₀) rfl ⟨hx, hb₀⟩ ⟨hy, hb₀⟩).1.1
    · intro x y hτ hx hy
      have hm := h (a₀, x) (a₀, y) hτ ⟨ha₀, hx⟩ ⟨ha₀, hy⟩
      exact ⟨hm.1.2, hm.2⟩
  · intro h x y hτ hx hy
    have hB := h.2 x.2 y.2 hτ hx.2 hy.2
    exact ⟨⟨h.1 x.1 y.1 hx.1 hy.1, hB.1⟩, hB.2⟩

end Uwueave.SeamAlgebra

/-! ## §6. The combinators — `SegVerdict` transport, mirroring `Spec`'s.

These extend `Spec`'s `SegVerdict` namespace from this file (no edit to
`Spec.lean`), so a schema author writes `vA.prodSeams vB` and
`vA.linkedSeam …` in the same fluent style as `Verdict.prodClashLeft`. Each
carries the *global clash* forward as well as the seam — a `SegVerdict` that
lost its clash would be claiming freedom it has not got. -/

namespace Uwueave.Spec.SegVerdict

open Uwueave Uwueave.Segmented Uwueave.SeamAlgebra

universe u v w z

variable {A : Type u} {B : Type v} {SegA : Type w} {SegB : Type z}
  [MergeState A] [MergeState B] {IA : Invariant A} {IB : Invariant B}

/-- **Two seamed fields, composed** — `product_segmented` as a combinator, with
field A's clash transported through the record (field B held at a legal value,
`vB.x`, exactly as `Verdict.prodClashLeft` does). The resulting seam is the
pair: **two coordination points**, and §5 says that is not an artefact of the
combinator when both fields clash. -/
def prodSeams (vA : SegVerdict IA SegA) (vB : SegVerdict IB SegB) :
    SegVerdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) (SegA × SegB) where
  σ := fun p => (vA.σ p.1, vB.σ p.2)
  seamFree := product_segmented vA.seamFree vB.seamFree
  x := (vA.x, vB.x)
  y := (vA.y, vB.x)
  hx := ⟨vA.hx, vB.hx⟩
  hy := ⟨vA.hy, vB.hx⟩
  hbad := fun h => vA.hbad h.1

/-- The same composition reporting field B's clash instead — the repro a schema
author gets should name the field they are asking about. -/
def prodSeamsRight (vA : SegVerdict IA SegA) (vB : SegVerdict IB SegB) :
    SegVerdict (S := A × B) (fun p => IA p.1 ∧ IB p.2) (SegA × SegB) where
  σ := fun p => (vA.σ p.1, vB.σ p.2)
  seamFree := product_segmented vA.seamFree vB.seamFree
  x := (vA.x, vB.x)
  y := (vA.x, vB.y)
  hx := ⟨vA.hx, vB.hx⟩
  hy := ⟨vA.hx, vB.hy⟩
  hbad := fun h => vB.hbad h.2

/-- **Absorb a free invariant** — `absorb_iconfluent` as a combinator. The seam
is unchanged, which is the point: adding a coordination-free conjunct adds no
coordination. The two legality side-conditions are honest — the free conjunct
must actually hold at the carried clash pair, or the clash is not a clash of
the conjunction. -/
def absorbFree {S : Type u} {Seg : Type v} [MergeState S] {I J : Invariant S}
    (v : SegVerdict I Seg) (hJ : IConfluent J) (hJx : J v.x) (hJy : J v.y) :
    SegVerdict (fun s => I s ∧ J s) Seg where
  σ := v.σ
  seamFree := absorb_iconfluent v.seamFree hJ
  x := v.x
  y := v.y
  hx := ⟨v.hx, hJx⟩
  hy := ⟨v.hy, hJy⟩
  hbad := fun h => v.hbad h.1

/-- **Change the seam** — `seam_substitute` as a combinator: re-report an
existing verdict against a different coordination point, given that the new one
determines the old and is fiber-stable. The clash is carried unchanged (it
refutes global freedom regardless of which seam is being reported). -/
def reseam {S : Type u} {Seg : Type v} {T : Type w} [MergeState S] {I : Invariant S}
    (v : SegVerdict I Seg) (τ : S → T)
    (hdet : ∀ x y : S, I x → I y → τ x = τ y → v.σ x = v.σ y)
    (hstable : SeamStableOn I τ) : SegVerdict I T where
  σ := τ
  seamFree := seam_substitute v.seamFree hdet hstable
  x := v.x
  y := v.y
  hx := v.hx
  hy := v.hy
  hbad := v.hbad

/-- **THE MERGE COMBINATOR** — `linked_segmented` as a combinator: a seamed
field A, a seamed field B, and a link pinning B's seam to `g` of A's, reported
as **one** coordination point (field A's seam). The clash is field A's,
transported with a legal, correctly-linked B value at each side — which is why
`b₁`/`b₂` and their link equations are arguments rather than being derived:
under the link, a single field-B value is legal on both sides only when `g`
happens to agree on the two clash states' seams, so `prodSeams`' hold-B-fixed
transport does not apply and the caller supplies the two linked partners. -/
def linkedSeam (vA : SegVerdict IA SegA) (σB : B → SegB)
    (hB : SegmentedIConfluent σB IB) (g : SegA → SegB)
    (b₁ b₂ : B) (hb₁ : IB b₁) (hb₂ : IB b₂)
    (hl₁ : σB b₁ = g (vA.σ vA.x)) (hl₂ : σB b₂ = g (vA.σ vA.y)) :
    SegVerdict (S := A × B) (LinkedInv IA IB vA.σ σB g) SegA where
  σ := fun p => vA.σ p.1
  seamFree := linked_segmented g vA.seamFree hB
  x := (vA.x, b₁)
  y := (vA.y, b₂)
  hx := ⟨vA.hx, hb₁, hl₁⟩
  hy := ⟨vA.hy, hb₂, hl₂⟩
  hbad := fun h => vA.hbad h.1

end Uwueave.Spec.SegVerdict

namespace Uwueave.SeamAlgebra

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Spec Uwueave.Seams

/-! ## §7. The two documents the algebra distinguishes.

Both are the *same two fields* — the versioned store of `Seams.lean` §2 and the
budgeted quota of `Segmented.lean` — and they differ only in whether
well-formedness links them. One needs two coordination points; the other needs
one. That difference is the whole practical content of this file. -/

/-- A two-field document: a versioned record store, and a budgeted quota with
per-device spends. -/
abbrev TwoFieldDoc := SchemaState × QuotaState

/-- The unlinked well-formedness: each field legal, no relation between them.
The version and the allocation move independently. -/
def twoFieldInv : Invariant TwoFieldDoc := fun p =>
  SchemaWF tightBound p.1 ∧ BudgetInv 10 p.2

/-- A legal store to hold fixed: version 1, empty. -/
def okSchema : SchemaState := (1, fun _ => false)

theorem okSchema_wf : SchemaWF tightBound okSchema := by
  intro n hn
  simp [okSchema] at hn

/-- A legal quota to hold fixed: the whole budget allocated to device `true`,
nothing spent. -/
def okQuota : QuotaState := ((fun b => if b then 10 else 0), (fun _ => 0))

theorem okQuota_wf : BudgetInv 10 okQuota := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide

/-- **Two seams suffice** — the pair `(version, allocation)` segments the
unlinked document, by `product_segmented` over `Seams.schema_segmented` and
`Segmented.budget_segmented`. Same-version, same-allocation replicas gossip
freely. -/
theorem twoField_segmented :
    SegmentedIConfluent (S := TwoFieldDoc) (fun p => (p.1.1, p.2.1)) twoFieldInv :=
  product_segmented (schema_segmented tightBound) (budget_segmented 10)

/-- **Any joint seam must separate the two allocations** — the contrapositive
of `seam_must_separate_right` on the budget clash (`Spec.budgetSegVerdict`'s
witness pair: 10+0 and 0+10 against budget 10). A seam that put both in one
fiber would be promising a free merge that busts the budget. -/
theorem twoField_seam_separates_allocations {T : Type w} (τ : TwoFieldDoc → T)
    (h : SegmentedIConfluent τ twoFieldInv) :
    τ (okSchema, budgetSegVerdict.x) ≠ τ (okSchema, budgetSegVerdict.y) :=
  fun heq =>
    seam_must_separate_right τ okSchema okSchema_wf
      budgetSegVerdict.x budgetSegVerdict.y
      budgetSegVerdict.hx budgetSegVerdict.hy budgetSegVerdict.hbad heq h

/-- **Any joint seam must separate the two versions** — the same, on the schema
clash (`Seams.schemaSegVerdict`'s witness pair: a legal version-0 record of 20
against a version-1 store). -/
theorem twoField_seam_separates_versions {T : Type w} (τ : TwoFieldDoc → T)
    (h : SegmentedIConfluent τ twoFieldInv) :
    τ (schemaSegVerdict.x, okQuota) ≠ τ (schemaSegVerdict.y, okQuota) :=
  fun heq =>
    seam_must_separate_left τ okQuota okQuota_wf
      schemaSegVerdict.x schemaSegVerdict.y
      schemaSegVerdict.hx schemaSegVerdict.hy schemaSegVerdict.hbad heq h

/-- ⚠ **No seam that reads only the store segments this document** — for every
type `T` in every universe and every projection `τ` of the store field. Watch
the version alone and the budget's clash sits inside one of your fibers. -/
theorem no_schema_only_seam {T : Type w} (τ : SchemaState → T) :
    ¬ SegmentedIConfluent (fun p : TwoFieldDoc => τ p.1) twoFieldInv :=
  fun h => twoField_seam_separates_allocations _ h rfl

/-- ⚠ **No seam that reads only the quota segments this document** — likewise,
for every `T` and every `τ`. Watch the allocation alone and the schema's flag
day sits inside one of your fibers. -/
theorem no_quota_only_seam {T : Type w} (τ : QuotaState → T) :
    ¬ SegmentedIConfluent (fun p : TwoFieldDoc => τ p.2) twoFieldInv :=
  fun h => twoField_seam_separates_versions _ h rfl

/-- **The unlinked document, packaged**: one `SegVerdict`, seam
`(version, allocation)`, clash carried from the store field. Read with
`no_schema_only_seam` / `no_quota_only_seam`: this seam cannot be narrowed to
either field, so the document has **two** coordination points. -/
def twoFieldSegVerdict : SegVerdict twoFieldInv (Nat × (Bool → Nat)) :=
  schemaSegVerdict.prodSeams budgetSegVerdict

/-! ### The linked document — the same two fields, coordinated once. -/

/-- The allocation policy, as a function of the schema version: version 0 gives
the whole budget to device `true`, every later version to device `false`. Sums
to the budget either way, so it is a legal policy at every version — and it
makes the allocation *derivable from the version*, which is the hypothesis of
`linked_segmented`. -/
def allocOf : Nat → (Bool → Nat) := fun v =>
  if v = 0 then (fun b => if b then 10 else 0) else (fun b => if b then 0 else 10)

/-- The linked well-formedness: store legal, quota legal, **and the allocation
is the one the current schema version dictates**. -/
def LinkedWF : Invariant TwoFieldDoc :=
  LinkedInv (SchemaWF tightBound) (BudgetInv 10) Prod.fst Prod.fst allocOf

/-- **One seam — the version — segments the linked document.** The
re-allocation is no longer a coordination point of its own: it can only happen
where the version changes, which is the flag day the store already pays for.
Two seams, one coordination event.

This is `linked_segmented` at the two-field instance, and it is the file's
punchline: the *same two fields* that need two coordination points unlinked
(`no_schema_only_seam`, `no_quota_only_seam`) need one when the schema dictates
the allocation. -/
theorem linked_flagDay_segmented :
    SegmentedIConfluent (S := TwoFieldDoc) (fun p => p.1.1) LinkedWF :=
  linked_segmented allocOf (schema_segmented tightBound) (budget_segmented 10)

/-- ⚠ **What the saving is, exactly.** On linked-legal states the version seam
and the pair seam have the *same* fibers — agreeing on the version already
forces agreement on the allocation. So the saving is not a coarser partition of
the state space: it is that there is only **one class of coordination event**
left to pay for. Re-allocation stopped being an event of its own; it is
something the flag day does. Stated here rather than left for a reader to
mis-infer "one seam" as "coordinate less often within a version". -/
theorem linked_version_seam_pins_the_pair (p q : TwoFieldDoc)
    (hp : LinkedWF p) (hq : LinkedWF q) (h : p.1.1 = q.1.1) :
    (p.1.1, p.2.1) = (q.1.1, q.2.1) := by
  rw [hp.2.2, hq.2.2, h]

/-- The link is a **strengthening** of the unlinked well-formedness — the
saving is paid for in states, not conjured. -/
theorem linkedWF_strengthens (p : TwoFieldDoc) (h : LinkedWF p) : twoFieldInv p :=
  ⟨h.1, h.2.1⟩

/-- ⚠ And it is a *real* strengthening: a document with the whole budget on
device `true` at version 1 is unlinked-legal and linked-illegal. This is the
price of the single coordination point, exhibited — you may no longer represent
an allocation the version does not dictate. -/
theorem link_is_a_real_constraint :
    twoFieldInv (okSchema, okQuota) ∧ ¬ LinkedWF (okSchema, okQuota) :=
  ⟨⟨okSchema_wf, okQuota_wf⟩,
   fun h => absurd (congrFun h.2.2 true) (by decide)⟩

/-- **The linked document, packaged**: one `SegVerdict`, seam = the version
*alone*, clash carried from the store field (a legal version-0 record of 20
merging into a version-1 store), each side holding the allocation its own
version dictates. -/
def flagDaySegVerdict : SegVerdict LinkedWF Nat :=
  schemaSegVerdict.linkedSeam Prod.fst (budget_segmented 10) allocOf
    (allocOf 0, (fun _ => 0)) (allocOf 1, (fun _ => 0))
    (by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide)
    (by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide)
    rfl rfl

/-! ### The readings the seam row is for. -/

/-- Both documents still escalate globally — a `SegVerdict` never claims
freedom. -/
example : ¬ IConfluent twoFieldInv := twoFieldSegVerdict.escalatesGlobally
example : ¬ IConfluent LinkedWF := flagDaySegVerdict.escalatesGlobally

/-- The seam row, evaluated: neither document is free for a binary consumer. -/
example : (twoFieldSegVerdict.toClash.isFree, flagDaySegVerdict.toClash.isFree)
    = (false, false) := rfl

/-- Free-running reading for the linked document, and the payoff spelled out:
**agreeing on the version alone** is enough for a safe merge — the quota field
comes along, with no separate agreement about the allocation. -/
example (a b : TwoFieldDoc) (hσ : a.1.1 = b.1.1)
    (ha : LinkedWF a) (hb : LinkedWF b) : LinkedWF (a ⊔ b) :=
  flagDaySegVerdict.freeWithinSeam hσ ha hb

/-- Closure reading for the linked document: a same-version sync can neither
bump the schema nor re-allocate behind your back. -/
example (a b : TwoFieldDoc) (hσ : a.1.1 = b.1.1)
    (ha : LinkedWF a) (hb : LinkedWF b) : (a ⊔ b).1.1 = a.1.1 :=
  flagDaySegVerdict.staysInSeam hσ ha hb

/-- … and the allocation is carried by the link, not by a second agreement —
`dominated_seam_needs_no_coordination` at this instance. -/
example (a b : TwoFieldDoc) (hσ : a.1.1 = b.1.1)
    (ha : LinkedWF a) (hb : LinkedWF b) : (a ⊔ b).2.1 = a.2.1 :=
  dominated_seam_needs_no_coordination allocOf (budget_segmented 10) hσ ha hb

/-- The unlinked document, by contrast, needs agreement on both fields' seams
— that is what its seam *is*. -/
example (a b : TwoFieldDoc) (hσ : (a.1.1, a.2.1) = (b.1.1, b.2.1))
    (ha : twoFieldInv a) (hb : twoFieldInv b) : twoFieldInv (a ⊔ b) :=
  (twoField_segmented a b hσ ha hb).1

end Uwueave.SeamAlgebra
