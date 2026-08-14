/-
# Uwueave.MinimalSummary — the coarsest future-sufficient summary, constructed.

**This file exists because the same external reviewer (codex) who produced
`JoinHom.lean`'s defect came back with the synthesis question that file opened
and left unresolved.** `JoinHom.lean` decides whether a *supplied* summary may
be shipped (`summaryFold_iff_joinHom`: exactly when it is a join
homomorphism), and its own honest boundary says what it cannot do:

> `count_summary_must_distinguish` shows a join-homomorphic summary computing
> the count must separate `sawA` from `sawB`; it does not characterise the
> *least* such summary. "How much provenance is enough" is a real question
> with no theorem here.

Codex's construction answers it. For a query `f : S → R`, define **contextual
equivalence**

    x ≈_f y  ⟺  f x = f y  ∧  ∀ z, f (x ⊔ z) = f (y ⊔ z)

— two states are equivalent when no future merge context can make the query
distinguish them. `CtxEquiv` below is that relation verbatim.

## Why this is the right relation, in three theorems

  1. **It is a congruence for the join** (`ctxEquiv_join`, `ctxEquiv_join₂`).
     This is the load-bearing lemma. It is why `Quotient (ctxSetoid f)` is not
     merely a set of classes but carries a `MergeState` of its own
     (`instMergeStateCtxQuot`), and why the class map is a `JoinHom`
     (`ctxMk_joinHom`). **Sufficiency and mergeability therefore never trade
     off:** the coarsest evidence that answers `f` is automatically shippable
     and foldable, with no extra hypothesis. `ctxQuot_fold_answers` is the whole
     architecture in one line — ship the class, fold with the quotient's join,
     decode with `ctxAnswer`, and land exactly on `f` of the merged evidence.
  2. **One context is all the contexts** (`ctxEquiv_history`). The definition
     looks at a single `⊔ z`; associativity means an entire gossip history
     `Delta.joinAll` is one join, so equivalent states are indistinguishable
     under *every* future delivery sequence, not merely one merge.
  3. **The universal property holds — "coarsest" is proved, not asserted.**
     `ctxMk_sufficient` says the class map is a sufficient summary;
     `sufficient_refines_ctxQuot` says *every* sufficient summary refines it
     (equal summaries ⇒ equal classes), and `ctxFactor_spec` produces the map
     that factors it, for inhabited carriers. Terminal among sufficient
     summaries in the partition order. That is the sense of "coarsest" claimed
     here and nothing more — see the boundary on representation.

## The connection to `JoinHom.lean`, by theorem and not by prose

`Sufficient f f` — "the answer is its own sufficient summary" — is **exactly**
`JoinHom.lean`'s fourth verdict: `selfSufficient_iff_resultDetermined` and
`selfSufficient_iff_incrementallyMergeable` prove
`Sufficient f f ↔ ResultDetermined f ↔ IncrementallyMergeable f`. So this file's
`card_not_self_sufficient` **implies** `JoinHom.card_not_incrementallyMergeable`
(`card_not_incrementallyMergeable_of_summary`, which re-derives that file's
headline impossibility from this file's pole). The traffic runs both ways:
`sufficient_fold_answers` and `ctxQuot_fold_answers` *use*
`JoinHom.summaryFold_iff_joinHom` — the fold of shipped summaries is licensed by
that iff and by nothing this file adds.

## The three poles

  * **Collapse — an existential ships as one bit.** For `s target` (membership
    in a G-Set), `mem_ctxEquiv_iff` proves `x ≈_f y ↔ x target = y target`: the
    entire set collapses to the answer. `mem_quot_bit` and `mem_quot_ofBit`
    exhibit the quotient in bijection with `Bool`, and `mem_quot_merge_is_or`
    shows the quotient's own join *is* `||`. Two classes, and the summary
    lattice is a bit.
  * **No collapse — an exact count keeps everything.** `card_ctxEquiv_iff`
    proves `x ≈_card y ↔ x = y` over the two-element universe: the quotient is
    the carrier, with no compression at all. Hence
    `card_sufficient_injective` — every sufficient summary for the count is
    injective — and `no_count_derived_summary_sufficient`: **no summary computed
    from the count is sufficient, for any target type whatsoever.** That is the
    upgrade over `no_count_merge_without_provenance`, which ranged over
    combiners `m : Nat → Nat → Nat`; this ranges over *coarsenings*, needs no
    `JoinHom` hypothesis, and yields the combiner result as a corollary.
  * **Interpolation — a threshold is neither.** `|s| ≥ 2` over a three-element
    universe has exactly five classes (`threshold_classes_complete` +
    `threshold_classes_distinct`): the four below-threshold states lie in four
    different classes, and everything from the threshold up lies in a single
    fifth one (`atLeast2_top`). So the construction has content — it is not an
    all-or-nothing dichotomy between "one bit" and "the whole state".

⚠ **The obvious guess about the threshold quotient is false.** A capped count
`min |s| k` is *not* what the quotient computes:
`threshold_quotient_not_cappedCount` exhibits `{0}` and `{1}`, which have the
same capped count and are separated by the context `{1}` (`{0} ∪ {1}` reaches
the threshold, `{1} ∪ {1}` does not). Overlap between the state and the future
context is observable, so a set-valued carrier does not degrade to a counter.

## Honest boundary

  * **The global quotient still has no unrestricted message representation.**
    ⟨DONE downstream in `FiniteSummaryCodec` for an explicit finite state
    universe and a complete finite context universe⟩ `CompleteSpec` turns the
    duplicate-free contextual class table into exactly `Fin classCount`:
    `class_count_exact`, `decode_encode_key`, and `encode_decode_index` prove
    the two representations equivalent, while
    `fixedWidth_information_lower_bound` proves the honest fixed-width
    information bound. The scope is deliberately finite and completeness is
    proof data; none of these results encodes an unrestricted `CtxQuot f` or
    supplies a global cost model. The membership pole remains the one global
    case where the class itself is exhibited as a `Bool` (`mem_quot_bit`).
  * **`decodeSummary` is `Classical.choice`, not a global algorithm.**
    ⟨SCOPE U-0111 beyond an explicit finite universe⟩ Same caveat as
    `JoinHom.canonicalCombine`: it witnesses that a decoder exists. The
    quotient's own decoder `ctxAnswer` is choice-free (`Quotient.lift f`), and
    `ContextCompiler.Spec.representative?` now gives a second, executable,
    choice-free decoder by selecting the first state in a caller-supplied finite
    enumeration; `representative_sound`, `representative_complete`, and
    `encode_decode_exact` state its exact scope.
  * **`∀ z` still ranges over the whole carrier, including unreachable
    states.** ⟨UNDONE U-0112 beyond a supplied finite context universe⟩
    `ContextCompiler` can instead compile exactly the contexts a caller lists;
    `signature_eq_iff` proves exactness for that relative relation, and
    `restricted_contexts_can_coarsen` exhibits `{0}` and `{1}` collapsing when
    the separating context is unavailable. What remains is deriving a complete
    reachable-context enumeration from an actual shipping API, rather than
    trusting the caller's list.
  * **Finite homogeneous query families have their common refinement.**
    ⟨TERMINAL at the supplied finite universe⟩ `ContextCompiler.signature`
    is the contextual answer matrix for a finite `List (S → R)`;
    `signature_eq_iff` is its exact multi-query relation,
    `signature_eq_iff_all_ctxEquiv_of_complete` identifies it with the common
    refinement of the global quotients when the context enumeration is
    complete, and `sufficient_refines_signature` proves the partition-order
    universal property. Heterogeneous or infinite query families are outside
    that compiler's claim.
  * **No syntax, so no classifier.** ⟨UNDONE U-0113⟩ `f` is an arbitrary Lean
    function; the quotient is computed per query by hand. Exactly the unbuilt
    part named in `Holes.lean` and `JoinHom.lean`, unchanged.
  * **The counted quotients are for the exhibited carriers only.** ⟨TERMINAL
    for the refutations, ⟨UNDONE U-0114⟩ for a formula⟩ Two- and three-element
    universes: a counterexample only needs to be a counterexample, and the
    positive results (§1–§3) carry no carrier assumption. But "five classes"
    is a fact about `|U| = 3, k = 2`; no general formula for the threshold
    quotient's size is proved.
  * **Single-context is not a weakness of the definition** — ⟨TERMINAL⟩ by
    `ctxEquiv_history`, which shows an arbitrary future history collapses to
    one context. It is a genuine consequence of associativity, not an
    assumption.

Literature: this is Nerode's right congruence with merge-contexts in place of
word suffixes — the Myhill–Nerode construction (quotient the states by "no
future context distinguishes them", get the minimal automaton) transplanted
from concatenation to a join-semilattice; the contextual/observational
equivalence framing is Morris's and Milner's. On the CRDT side, "how much
provenance must a summary retain" is the question behind counting Bloom
filters, PN-counters and `COUNT DISTINCT` sketches — each is an engineering
answer to a question this file states exactly.
-/
import Uwueave.JoinHom

namespace Uwueave

open Uwueave.Catalog

universe u v w

/-! ## §1. Contextual equivalence.

The relation, its equivalence laws, and the congruence property that makes the
quotient a lattice rather than a bare partition. -/

/-- **Contextual equivalence for the query `f`.** Two states are equivalent
when `f` cannot tell them apart *now* and no future merge context can make it
tell them apart later. Codex's construction, verbatim. -/
def CtxEquiv {S : Type u} {R : Type v} [MergeState S] (f : S → R) (x y : S) : Prop :=
  f x = f y ∧ ∀ z : S, f (x ⊔ z) = f (y ⊔ z)

variable {S : Type u} {R : Type v} {T : Type w}

theorem ctxEquiv_refl [MergeState S] (f : S → R) (x : S) : CtxEquiv f x x :=
  ⟨rfl, fun _ => rfl⟩

theorem ctxEquiv_symm [MergeState S] {f : S → R} {x y : S} (h : CtxEquiv f x y) :
    CtxEquiv f y x :=
  ⟨h.1.symm, fun z => (h.2 z).symm⟩

theorem ctxEquiv_trans [MergeState S] {f : S → R} {x y z : S}
    (h₁ : CtxEquiv f x y) (h₂ : CtxEquiv f y z) : CtxEquiv f x z :=
  ⟨h₁.1.trans h₂.1, fun w => (h₁.2 w).trans (h₂.2 w)⟩

/-- Contextual equivalence is an equivalence relation — the `Setoid` this file
quotients by. -/
theorem ctxEquiv_equivalence [MergeState S] (f : S → R) : Equivalence (CtxEquiv f) :=
  ⟨ctxEquiv_refl f, ctxEquiv_symm, ctxEquiv_trans⟩

/-- **The first conjunct is redundant.** Agreeing under every context already
forces agreeing now: instantiate at `z := x` and `z := y` and use idempotence
and commutativity. Kept in the definition because that is how the relation was
proposed and how it reads. -/
theorem ctxEquiv_of_contexts [MergeState S] {f : S → R} {x y : S}
    (h : ∀ z : S, f (x ⊔ z) = f (y ⊔ z)) : CtxEquiv f x y := by
  refine ⟨?_, h⟩
  have hx : f (x ⊔ x) = f (y ⊔ x) := h x
  have hy : f (x ⊔ y) = f (y ⊔ y) := h y
  rw [merge_idem] at hx
  rw [merge_idem] at hy
  rw [hx, merge_comm, hy]

/-- The definition, with the redundancy of the first conjunct discharged. -/
theorem ctxEquiv_iff_contexts [MergeState S] (f : S → R) (x y : S) :
    CtxEquiv f x y ↔ ∀ z : S, f (x ⊔ z) = f (y ⊔ z) :=
  ⟨fun h => h.2, ctxEquiv_of_contexts⟩

/-- **THE LOAD-BEARING LEMMA: contextual equivalence is stable under adding
context.** Learning the same new information on both sides preserves
indistinguishability — so the relation is a congruence for one argument of the
join, which is what a quotient lattice needs. -/
theorem ctxEquiv_join [MergeState S] {f : S → R} {x y : S}
    (h : CtxEquiv f x y) (w : S) : CtxEquiv f (x ⊔ w) (y ⊔ w) := by
  refine ⟨h.2 w, fun z => ?_⟩
  rw [merge_assoc, merge_assoc]
  exact h.2 (w ⊔ z)

/-- The congruence in both arguments — `ctxEquiv_join` twice, through
commutativity. This is the well-definedness obligation for the quotient's
merge. -/
theorem ctxEquiv_join₂ [MergeState S] {f : S → R} {x x' y y' : S}
    (hx : CtxEquiv f x x') (hy : CtxEquiv f y y') :
    CtxEquiv f (x ⊔ y) (x' ⊔ y') := by
  refine ctxEquiv_trans (ctxEquiv_join hx y) ?_
  have h := ctxEquiv_join hy x'
  rw [merge_comm y x', merge_comm y' x'] at h
  exact h

/-- **Contextual equivalence refines plain answer-equality**: the first
conjunct. The converse fails — see `answerEq_not_ctxEquiv`. -/
theorem ctxEquiv_answer [MergeState S] {f : S → R} {x y : S}
    (h : CtxEquiv f x y) : f x = f y := h.1

/-- **One context is all the contexts.** Equivalent states stay
indistinguishable under an entire gossip history, not merely one merge: by
associativity a whole `Delta.joinAll` is a single join, so the definition's
single `⊔ z` loses nothing. -/
theorem ctxEquiv_history [MergeState S] {f : S → R} {x y : S} (h : CtxEquiv f x y) :
    ∀ l : List S, f (Delta.joinAll x l) = f (Delta.joinAll y l)
  | [] => h.1
  | d :: l => by
      rw [Delta.joinAll_cons, Delta.joinAll_cons, Delta.merge_joinAll,
        Delta.merge_joinAll]
      exact h.2 _

/-! ## §2. Sufficiency — what it means to ship `g` instead of the evidence. -/

/-- **`g` is a sufficient summary for `f`**: states with equal summaries are
contextually equivalent for `f`, so a receiver holding only `g` has lost
nothing the query will ever need — now or after any future merge. -/
def Sufficient [MergeState S] (g : S → T) (f : S → R) : Prop :=
  ∀ x y : S, g x = g y → CtxEquiv f x y

/-- Shipping the evidence itself is sufficient — the trivial upper bound the
whole exercise is trying to improve on. -/
theorem sufficient_id [MergeState S] (f : S → R) : Sufficient (fun x => x) f := by
  intro x y h
  have hxy : x = y := h
  subst hxy
  exact ctxEquiv_refl f x

/-- A summary at least as fine as a sufficient one is sufficient. -/
theorem sufficient_of_refines {T' : Type w} [MergeState S] {g : S → T'} {g' : S → T}
    {f : S → R} (hg' : Sufficient g' f)
    (hfine : ∀ x y : S, g x = g y → g' x = g' y) :
    Sufficient g f :=
  fun x y h => hg' x y (hfine x y h)

/-- A sufficient summary determines the answer. -/
theorem sufficient_answer [MergeState S] {g : S → T} {f : S → R}
    (hg : Sufficient g f) {x y : S} (h : g x = g y) : f x = f y :=
  (hg x y h).1

open Classical in
/-- The decoder built from sufficiency: pick *any* state with the given summary
and answer from it. Classical and not an algorithm — see the boundary note; the
quotient's own decoder `ctxAnswer` is choice-free. -/
noncomputable def decodeSummary [MergeState S] (g : S → T) (f : S → R)
    [Inhabited R] (t : T) : R :=
  if h : ∃ x : S, g x = t then f h.choose else default

/-- The decoder is correct on summaries that were actually produced:
`decodeSummary g f (g x) = f x` whenever `g` is sufficient. -/
theorem decodeSummary_spec [MergeState S] {g : S → T} {f : S → R} [Inhabited R]
    (hg : Sufficient g f) (x : S) : decodeSummary g f (g x) = f x := by
  have hex : ∃ x' : S, g x' = g x := ⟨x, rfl⟩
  unfold decodeSummary
  rw [dif_pos hex]
  exact (hg hex.choose x hex.choose_spec).1

/-- **THE MERGEABILITY PAYOFF.** If `g` is sufficient for `f` **and** a join
homomorphism, then a receiver that holds only summaries — folding arrivals with
the summary lattice's own join, exactly `JoinHom.SummaryFoldAgrees` — decodes to
the same answer as recomputing `f` from the merged evidence, for every history.

The `JoinHom` hypothesis enters through `summaryFold_iff_joinHom`, which is
what licenses replacing `g (Delta.joinAll init l)` by the fold of the shipped
summaries; sufficiency is what licenses answering from the summary at all. -/
theorem sufficient_fold_answers [MergeState S] [MergeState T] [Inhabited R]
    {g : S → T} {f : S → R} (hsuf : Sufficient g f) (hj : JoinHom g)
    (init : S) (l : List S) :
    f (Delta.joinAll init l)
      = decodeSummary g f (Delta.joinAll (g init) (l.map g)) := by
  have hfold : JoinHom.SummaryFoldAgrees g :=
    (JoinHom.summaryFold_iff_joinHom g).mpr hj
  rw [← hfold l init]
  exact (decodeSummary_spec hsuf _).symm

/-- The same payoff without `Classical.choice` or `Inhabited`: two receivers
that saw the same summaries — whatever evidence produced them — answer `f` the
same way. -/
theorem sufficient_history_determines [MergeState S] [MergeState T]
    {g : S → T} {f : S → R} (hsuf : Sufficient g f) (hj : JoinHom g)
    (init init' : S) (l l' : List S)
    (hinit : g init = g init') (hl : l.map g = l'.map g) :
    f (Delta.joinAll init l) = f (Delta.joinAll init' l') := by
  have hfold : JoinHom.SummaryFoldAgrees g :=
    (JoinHom.summaryFold_iff_joinHom g).mpr hj
  refine (hsuf _ _ ?_).1
  rw [hfold l init, hfold l' init', hinit, hl]

/-! ### §2.1 Self-sufficiency **is** `JoinHom.lean`'s fourth verdict.

The special case `g = f` — "ship the answer itself" — is not a new property. It
is `ResultDetermined`, hence `IncrementallyMergeable`, on the nose. -/

/-- **The answer is its own sufficient summary exactly when the results
determine the merged result.** `ResultDetermined` is `JoinHom.lean`'s
characterisation of the fourth verdict; this is that verdict restated as a
statement about how coarse `f`'s own partition is. -/
theorem selfSufficient_iff_resultDetermined [MergeState S] (f : S → R) :
    Sufficient f f ↔ ResultDetermined f := by
  constructor
  · intro hs x y x' y' hx hy
    have h1 : f (x ⊔ y) = f (x' ⊔ y) := (hs x x' hx).2 y
    have h2 : f (y ⊔ x') = f (y' ⊔ x') := (hs y y' hy).2 x'
    rw [merge_comm y x', merge_comm y' x'] at h2
    exact h1.trans h2
  · intro hr x y hxy
    exact ⟨hxy, fun z => hr x z y z hxy rfl⟩

/-- **And therefore exactly when `f` is incrementally mergeable from its
results** — `JoinHom.incrementallyMergeable_iff_resultDetermined` composed with
the previous theorem. So the fourth verdict is the `g = f` instance of
sufficiency, and this file's poles are statements about the same question at
finer resolution. -/
theorem selfSufficient_iff_incrementallyMergeable [MergeState S] [Inhabited R]
    (f : S → R) : Sufficient f f ↔ IncrementallyMergeable f :=
  (selfSufficient_iff_resultDetermined f).trans
    (incrementallyMergeable_iff_resultDetermined f).symm

/-! ## §3. The quotient — the coarsest sufficient summary, and its lattice. -/

/-- The setoid of contextual equivalence for `f`. -/
def ctxSetoid [MergeState S] (f : S → R) : Setoid S :=
  ⟨CtxEquiv f, ctxEquiv_equivalence f⟩

/-- **The candidate coarsest evidence domain**: states modulo "no future merge
context makes `f` tell them apart". -/
def CtxQuot [MergeState S] (f : S → R) : Type u := Quotient (ctxSetoid f)

/-- The class map — the summary this file proposes shipping. -/
def ctxMk [MergeState S] (f : S → R) (x : S) : CtxQuot f :=
  Quotient.mk (ctxSetoid f) x

/-- Two states have the same class exactly when they are contextually
equivalent. -/
theorem ctxMk_eq_iff [MergeState S] (f : S → R) (x y : S) :
    ctxMk f x = ctxMk f y ↔ CtxEquiv f x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The join on classes: merge representatives. Well-defined **because**
`ctxEquiv_join₂` — the congruence property — holds. -/
def ctxJoin [MergeState S] (f : S → R) (p q : CtxQuot f) : CtxQuot f :=
  Quotient.lift₂ (s₁ := ctxSetoid f) (s₂ := ctxSetoid f)
    (fun a b => ctxMk f (a ⊔ b))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (ctxEquiv_join₂ h₁ h₂)) p q

/-- **The quotient is itself a mergeable state.** The three CRDT laws descend
from the carrier's, because the class map is surjective and the join was
defined on representatives. -/
instance instMergeStateCtxQuot [MergeState S] (f : S → R) :
    MergeState (CtxQuot f) where
  merge := ctxJoin f
  merge_comm := by
    refine Quotient.ind₂ (motive := fun p q => ctxJoin f p q = ctxJoin f q p) ?_
    intro a b
    show ctxMk f (a ⊔ b) = ctxMk f (b ⊔ a)
    rw [merge_comm]
  merge_assoc := by
    intro p q r
    refine Quotient.inductionOn₃ p q r ?_
    intro a b c
    show ctxMk f ((a ⊔ b) ⊔ c) = ctxMk f (a ⊔ (b ⊔ c))
    rw [merge_assoc]
  merge_idem := by
    refine Quotient.ind (motive := fun p => ctxJoin f p p = p) ?_
    intro a
    show ctxMk f (a ⊔ a) = ctxMk f a
    rw [merge_idem]

/-- The class of a merge is the merge of the classes — `rfl`, by construction. -/
theorem ctxMk_merge [MergeState S] (f : S → R) (x y : S) :
    ctxMk f (x ⊔ y) = ctxMk f x ⊔ ctxMk f y := rfl

/-- **The coarsest summary is automatically shippable.** The class map is a
join homomorphism, so by `summaryFold_iff_joinHom` the summary-replication
architecture is correct for it — with no side condition. Sufficiency and
mergeability do not trade off. -/
theorem ctxMk_joinHom [MergeState S] (f : S → R) : JoinHom (ctxMk f) :=
  fun _ _ => rfl

/-- **The class map is a sufficient summary** — `Quotient.exact`. -/
theorem ctxMk_sufficient [MergeState S] (f : S → R) : Sufficient (ctxMk f) f :=
  fun _ _ h => Quotient.exact h

/-- The quotient's decoder, choice-free: `f` descends to the classes because
contextual equivalence implies answer-equality. -/
def ctxAnswer [MergeState S] (f : S → R) : CtxQuot f → R :=
  Quotient.lift (s := ctxSetoid f) f
    (fun a b h => (show CtxEquiv f a b from h).1)

@[simp] theorem ctxAnswer_ctxMk [MergeState S] (f : S → R) (x : S) :
    ctxAnswer f (ctxMk f x) = f x := rfl

/-- **THE SYNTHESIS THEOREM.** Ship the contextual-equivalence class, fold
arrivals with the quotient's own join, decode — and land exactly on `f` of the
merged evidence, for every gossip history. This is `JoinHom.lean`'s
architecture (ii) run on the coarsest evidence that can possibly support the
query, and it needs no hypothesis on `f` at all. -/
theorem ctxQuot_fold_answers [MergeState S] (f : S → R) (init : S) (l : List S) :
    f (Delta.joinAll init l)
      = ctxAnswer f (Delta.joinAll (ctxMk f init) (l.map (ctxMk f))) := by
  have hfold : JoinHom.SummaryFoldAgrees (ctxMk f) :=
    (JoinHom.summaryFold_iff_joinHom (ctxMk f)).mpr (ctxMk_joinHom f)
  rw [← hfold l init]
  rfl

/-! ### §3.1 The universal property — in what sense "coarsest".

`ctxMk` is sufficient, and every sufficient summary refines it. That is
terminality in the partition order: no sufficient summary can merge two classes
the quotient keeps apart. It is **not** a claim about representation size. -/

/-- **Every sufficient summary refines the quotient.** Equal summaries force
equal classes — so no sufficient summary is coarser than `CtxQuot f`. -/
theorem sufficient_refines_ctxQuot [MergeState S] {g : S → T} {f : S → R}
    (hg : Sufficient g f) (x y : S) (h : g x = g y) : ctxMk f x = ctxMk f y :=
  Quotient.sound (hg x y h)

open Classical in
/-- The map that factors the quotient through a sufficient summary: read the
class off any state carrying the given summary. -/
noncomputable def ctxFactor [MergeState S] [Inhabited S] (g : S → T) (f : S → R)
    (t : T) : CtxQuot f :=
  if h : ∃ x : S, g x = t then ctxMk f h.choose else ctxMk f default

/-- **The factorisation.** For a sufficient `g`, the quotient map *is* `ctxFactor
g f ∘ g`: every sufficient summary already determines the class, and this
exhibits the map that reads it off. With `sufficient_refines_ctxQuot` this is
the universal property in full — `CtxQuot f` is terminal among sufficient
summaries. -/
theorem ctxFactor_spec [MergeState S] [Inhabited S] {g : S → T} {f : S → R}
    (hg : Sufficient g f) (x : S) : ctxFactor g f (g x) = ctxMk f x := by
  have hex : ∃ x' : S, g x' = g x := ⟨x, rfl⟩
  unfold ctxFactor
  rw [dif_pos hex]
  exact Quotient.sound (hg hex.choose x hex.choose_spec)

/-- **The universal property, stated once**: the class map is a sufficient
summary, it is a join homomorphism, and every sufficient summary refines it.
"Coarsest sufficient evidence domain" means exactly these three clauses. -/
theorem ctxQuot_coarsest_sufficient [MergeState S] (f : S → R) :
    Sufficient (ctxMk f) f ∧ JoinHom (ctxMk f)
      ∧ ∀ (T' : Type w) (g : S → T'), Sufficient g f →
          ∀ x y : S, g x = g y → ctxMk f x = ctxMk f y :=
  ⟨ctxMk_sufficient f, ctxMk_joinHom f,
   fun _ _ hg x y h => sufficient_refines_ctxQuot hg x y h⟩

namespace MinimalSummary

open Uwueave.Catalog

/-! ## §4. POLE ONE — an existential ships as one bit.

The query is membership of a fixed element in a grow-only set. Its contextual
equivalence collapses the whole set to the answer, and the quotient is in
bijection with `Bool` — join and all. -/

/-- Membership of a fixed element — the yes/no read of `JoinHom.verdict_exists`,
at a named element. -/
def memQuery {α : Type} (target : α) (s : GSet α) : Bool := s target

/-- **THE COLLAPSE.** Two G-Sets are contextually equivalent for "is `target`
present?" **exactly** when they agree on `target` — every other element is
invisible to every future context. So the coarsest sufficient summary of an
arbitrarily large set, for this query, is one bit. -/
theorem mem_ctxEquiv_iff {α : Type} (target : α) (x y : GSet α) :
    CtxEquiv (memQuery target) x y ↔ x target = y target := by
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, fun z => ?_⟩
    show ((x ⊔ z) target) = ((y ⊔ z) target)
    show (x target || z target) = (y target || z target)
    rw [h]

/-- The answer is its own sufficient summary for a membership read — the
`g = f` case, which by `selfSufficient_iff_incrementallyMergeable` is the
`fromResults` verdict of `JoinHom.lean` §6. -/
theorem mem_self_sufficient {α : Type} (target : α) :
    Sufficient (memQuery target) (memQuery target) :=
  fun x y h => (mem_ctxEquiv_iff target x y).mpr h

/-- The all-`b` set — the representative of each class in the membership
quotient. -/
def ofBit {α : Type} (target : α) (b : Bool) : CtxQuot (memQuery target) :=
  ctxMk (memQuery target) (fun _ => b)

/-- Decoding the class of an all-`b` set returns `b`. -/
theorem mem_quot_bit {α : Type} (target : α) (b : Bool) :
    ctxAnswer (memQuery target) (ofBit target b) = b := rfl

/-- **The quotient IS a bit.** Every class is the class of an all-`b` set, so
with `mem_quot_bit` the membership quotient is in bijection with `Bool`: two
classes, no more. -/
theorem mem_quot_ofBit {α : Type} (target : α) (q : CtxQuot (memQuery target)) :
    ofBit target (ctxAnswer (memQuery target) q) = q := by
  refine Quotient.inductionOn q ?_
  intro s
  exact Quotient.sound ((mem_ctxEquiv_iff target (fun _ => s target) s).mpr rfl)

/-- **And the quotient's merge is boolean OR.** The one-bit summary is not just
small, it is a join-semilattice whose join is `||` — the summary lattice a
delta receiver would actually fold. -/
theorem mem_quot_merge_is_or {α : Type} (target : α)
    (p q : CtxQuot (memQuery target)) :
    ctxAnswer (memQuery target) (p ⊔ q)
      = (ctxAnswer (memQuery target) p || ctxAnswer (memQuery target) q) := by
  refine Quotient.ind₂ (motive := fun p q => ctxAnswer (memQuery target) (p ⊔ q)
      = (ctxAnswer (memQuery target) p || ctxAnswer (memQuery target) q)) ?_ p q
  intro a b
  rfl

/-! ## §5. POLE TWO — an exact count keeps everything.

`JoinHom.card` over the two-element universe, with `JoinHom.sawA`/`sawB` as the
two replicas. The quotient is the carrier: contextual equivalence for an exact
count is *equality of the set*. -/

/-- The indicator is injective: a `bit` recovers the `Bool` it counted. -/
theorem bit_inj {a b : Bool} (h : JoinHom.bit a = JoinHom.bit b) : a = b := by
  cases a <;> cases b <;> simp_all [JoinHom.bit]

/-- **NO COLLAPSE.** Two G-Sets over the two-element universe are contextually
equivalent for the exact count **exactly** when they are equal. The contexts
`sawA`/`sawB` — "the peer already saw the other element" — recover membership
one element at a time, so the count's coarsest sufficient summary is the whole
set. -/
theorem card_ctxEquiv_iff (x y : GSet Bool) :
    CtxEquiv JoinHom.card x y ↔ x = y := by
  constructor
  · intro h
    funext b
    cases b with
    | false =>
      have hz : JoinHom.bit (x false || false) + JoinHom.bit (x true || true)
          = JoinHom.bit (y false || false) + JoinHom.bit (y true || true) :=
        h.2 JoinHom.sawB
      simp only [Bool.or_false, Bool.or_true] at hz
      exact bit_inj (Nat.add_right_cancel hz)
    | true =>
      have hz : JoinHom.bit (x false || true) + JoinHom.bit (x true || false)
          = JoinHom.bit (y false || true) + JoinHom.bit (y true || false) :=
        h.2 JoinHom.sawA
      simp only [Bool.or_true, Bool.or_false] at hz
      exact bit_inj (Nat.add_left_cancel hz)
  · intro h
    rw [h]
    exact ctxEquiv_refl _ y

/-- ⚠ **Contextual equivalence is strictly finer than answer-equality.** The two
replicas of `JoinHom.lean` §4 report the same count and are *not* contextually
equivalent — the context `sawA` separates them (`1` against `2`). So the
refinement `ctxEquiv_answer` is strict, and "equal answers" is not a sufficient
summary in general. -/
theorem answerEq_not_ctxEquiv :
    JoinHom.card JoinHom.sawA = JoinHom.card JoinHom.sawB
      ∧ ¬ CtxEquiv JoinHom.card JoinHom.sawA JoinHom.sawB := by
  refine ⟨by decide, ?_⟩
  intro h
  exact absurd (h.2 JoinHom.sawA) (by decide)

/-- **Every sufficient summary for the count is injective.** Not "must
distinguish `sawA` from `sawB`" (`JoinHom.count_summary_must_distinguish`, which
also assumed the summary was a join homomorphism) — must distinguish
*everything*, with no hypothesis on the summary at all. -/
theorem card_sufficient_injective {T : Type w} (g : GSet Bool → T)
    (hg : Sufficient g JoinHom.card) (x y : GSet Bool) (h : g x = g y) : x = y :=
  (card_ctxEquiv_iff x y).mp (hg x y h)

/-- ⚠ **NO SUMMARY DERIVED FROM THE COUNT IS SUFFICIENT** — for any target type
and any post-processing `k`. This is the upgrade of
`JoinHom.no_count_merge_without_provenance`: that theorem ranged over
*combiners* `Nat → Nat → Nat` and said none is exact; this ranges over
*coarsenings* and says none is even enough evidence to try. A count has
discarded what the future needs, and no function of it can put that back. -/
theorem no_count_derived_summary_sufficient {T : Type w} (g : GSet Bool → T)
    (hfac : ∃ k : Nat → T, ∀ s, g s = k (JoinHom.card s)) :
    ¬ Sufficient g JoinHom.card := by
  intro hsuf
  obtain ⟨k, hk⟩ := hfac
  have heq : g JoinHom.sawA = g JoinHom.sawB := by
    rw [hk, hk, JoinHom.card_sawA, JoinHom.card_sawB]
  have hbad : JoinHom.sawA = JoinHom.sawB :=
    card_sufficient_injective g hsuf _ _ heq
  exact absurd (congrFun hbad false) (by decide)

/-- ⚠ **The count is not a sufficient summary for itself** — the `g = f`
instance, i.e. `JoinHom.lean`'s `needsEvidence` verdict in this file's
vocabulary. -/
theorem card_not_self_sufficient : ¬ Sufficient JoinHom.card JoinHom.card :=
  no_count_derived_summary_sufficient JoinHom.card ⟨fun n => n, fun _ => rfl⟩

/-- **`JoinHom.card_not_incrementallyMergeable`, re-derived from this file's
pole.** The fourth verdict for counting is a corollary of "the count's coarsest
sufficient summary is the whole set", via
`selfSufficient_iff_incrementallyMergeable`. The two files are connected by
theorem, not by narration. -/
theorem card_not_incrementallyMergeable_of_summary :
    ¬ IncrementallyMergeable JoinHom.card :=
  fun h => card_not_self_sufficient
    ((selfSufficient_iff_incrementallyMergeable JoinHom.card).mpr h)

/-- The quotient's representative map for the count: the class *is* the state. -/
def cardRep : CtxQuot JoinHom.card → GSet Bool :=
  Quotient.lift (s := ctxSetoid JoinHom.card) (fun s => s)
    (fun a b h => (card_ctxEquiv_iff a b).mp h)

theorem cardRep_ctxMk (x : GSet Bool) : cardRep (ctxMk JoinHom.card x) = x := rfl

/-- **The count's quotient is the carrier itself** — `cardRep` and `ctxMk` are
mutually inverse, so contextual equivalence compresses an exact count by exactly
nothing. -/
theorem ctxMk_cardRep (q : CtxQuot JoinHom.card) :
    ctxMk JoinHom.card (cardRep q) = q := by
  refine Quotient.inductionOn q ?_
  intro s
  rfl

/-! ## §6. THE INTERPOLATION — a threshold is neither pole.

Three elements, and the query "does the set have at least two of them?". The
quotient collapses everything at or above the threshold into one class and keeps
everything below it exactly: coarser than the state, finer than the answer. -/

/-- The count over a three-element universe. -/
def card3 (s : GSet (Fin 3)) : Nat :=
  JoinHom.bit (s 0) + JoinHom.bit (s 1) + JoinHom.bit (s 2)

/-- The threshold query: "has the set reached `k` elements?" -/
def atLeast (k : Nat) (s : GSet (Fin 3)) : Bool := decide (k ≤ card3 s)

/-- The singleton `{i}`. -/
def pick (i : Fin 3) : GSet (Fin 3) := fun j => j == i

/-- The empty set. -/
def empty3 : GSet (Fin 3) := fun _ => false

/-- The full set. -/
def full3 : GSet (Fin 3) := fun _ => true

/-- Merging only adds elements, so the indicator only rises. -/
theorem bit_le_or (a b : Bool) : JoinHom.bit a ≤ JoinHom.bit (a || b) := by
  cases a <;> cases b <;> decide

/-- The three-element count is monotone under merge. -/
theorem card3_le_merge (x z : GSet (Fin 3)) : card3 x ≤ card3 (x ⊔ z) :=
  Nat.add_le_add (Nat.add_le_add (bit_le_or (x 0) (z 0)) (bit_le_or (x 1) (z 1)))
    (bit_le_or (x 2) (z 2))

/-- **The top of a threshold collapses, in general.** For *any* carrier and any
monotone count, two states that have both reached the threshold are contextually
equivalent for it: the answer is already `true` and no context can lower it.
This is the half of the interpolation that needs no finiteness. -/
theorem ctxEquiv_threshold_top {S : Type u} [MergeState S] (c : S → Nat)
    (hmono : ∀ x z : S, c x ≤ c (x ⊔ z)) (k : Nat) {x y : S}
    (hx : k ≤ c x) (hy : k ≤ c y) :
    CtxEquiv (fun s => decide (k ≤ c s)) x y := by
  constructor
  · show decide (k ≤ c x) = decide (k ≤ c y)
    rw [decide_eq_true hx, decide_eq_true hy]
  · intro z
    show decide (k ≤ c (x ⊔ z)) = decide (k ≤ c (y ⊔ z))
    rw [decide_eq_true (Nat.le_trans hx (hmono x z)),
      decide_eq_true (Nat.le_trans hy (hmono y z))]

/-- The threshold's top class, at `k = 2` over three elements. -/
theorem atLeast2_top {x y : GSet (Fin 3)} (hx : 2 ≤ card3 x) (hy : 2 ≤ card3 y) :
    CtxEquiv (atLeast 2) x y :=
  ctxEquiv_threshold_top card3 card3_le_merge 2 hx hy

/-- A context that separates two states refutes their equivalence. -/
theorem not_ctxEquiv_of_context {k : Nat} {x y : GSet (Fin 3)} (z : GSet (Fin 3))
    (h : atLeast k (x ⊔ z) ≠ atLeast k (y ⊔ z)) : ¬ CtxEquiv (atLeast k) x y :=
  fun he => h (he.2 z)

/-- ⚠ **STRICTLY COARSER THAN THE STATE.** `{0,1}` and the full set are
different states that no future context can separate — both have already reached
the threshold. So unlike the count (§5), the threshold quotient genuinely
compresses. -/
theorem threshold_coarser_than_state :
    pick 0 ⊔ pick 1 ≠ full3 ∧ CtxEquiv (atLeast 2) (pick 0 ⊔ pick 1) full3 :=
  ⟨fun h => absurd (congrFun h 2) (by decide), atLeast2_top (by decide) (by decide)⟩

/-- ⚠ **STRICTLY FINER THAN THE ANSWER.** `{0}` and `{1}` give the same answer
now (`false` — neither has two elements) and the context `{1}` separates them:
`{0} ∪ {1}` reaches the threshold, `{1} ∪ {1}` does not. So unlike membership
(§4), the answer bit is *not* a sufficient summary here. -/
theorem threshold_finer_than_answer :
    atLeast 2 (pick 0) = atLeast 2 (pick 1)
      ∧ ¬ CtxEquiv (atLeast 2) (pick 0) (pick 1) :=
  ⟨by decide, not_ctxEquiv_of_context (pick 1) (by decide)⟩

/-- ⚠ **THE OBVIOUS GUESS IS FALSE: the quotient is not a capped count.**
`{0}` and `{1}` have the same capped count `min |s| 2 = 1` and are *not*
contextually equivalent. The overlap between the state and the future context is
observable, so a set does not degrade to a counter under a threshold query; what
the quotient actually does is collapse the top and keep the bottom exactly
(§6.1). -/
theorem threshold_quotient_not_cappedCount :
    Nat.min (card3 (pick 0)) 2 = Nat.min (card3 (pick 1)) 2
      ∧ ¬ CtxEquiv (atLeast 2) (pick 0) (pick 1) :=
  ⟨by decide, threshold_finer_than_answer.2⟩

/-- **Where the threshold sits, in one statement.** Membership admits no
distinctions beyond its answer; the count admits every distinction; the
threshold admits some and not others. The construction interpolates. -/
theorem three_poles :
    (∀ x y : GSet Bool, memQuery true x = memQuery true y
        → CtxEquiv (memQuery true) x y)
      ∧ (∀ x y : GSet Bool, CtxEquiv JoinHom.card x y → x = y)
      ∧ (pick 0 ⊔ pick 1 ≠ full3 ∧ CtxEquiv (atLeast 2) (pick 0 ⊔ pick 1) full3)
      ∧ (atLeast 2 (pick 0) = atLeast 2 (pick 1)
          ∧ ¬ CtxEquiv (atLeast 2) (pick 0) (pick 1)) :=
  ⟨mem_self_sufficient true, fun x y h => (card_ctxEquiv_iff x y).mp h,
   threshold_coarser_than_state, threshold_finer_than_answer⟩

/-! ### §6.1 The threshold quotient, counted: exactly five classes. -/

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  match i with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
  | ⟨n + 3, h⟩ => exact absurd h (by omega)

/-- Two three-element sets agreeing at each index are equal. -/
theorem gset3_ext {x y : GSet (Fin 3)} (h0 : x 0 = y 0) (h1 : x 1 = y 1)
    (h2 : x 2 = y 2) : x = y := by
  funext i
  rcases fin3_cases i with h | h | h <;> rw [h]
  · exact h0
  · exact h1
  · exact h2

/-- **Completeness, in the sharp form: below the threshold a state is kept
exactly, and from the threshold up every state joins one class.** Each of the
four sub-threshold cases returns an *equality* — the quotient has not merged
anything down there — and the four above-threshold cases return contextual
equivalence to the full set. With `threshold_classes_distinct`, that is exactly
five classes. -/
theorem threshold_classes_complete (s : GSet (Fin 3)) :
    s = empty3 ∨ s = pick 0 ∨ s = pick 1 ∨ s = pick 2
      ∨ CtxEquiv (atLeast 2) s full3 := by
  have htop : ∀ _ : 2 ≤ card3 s, CtxEquiv (atLeast 2) s full3 :=
    fun h => atLeast2_top h (by decide)
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  · exact Or.inl (gset3_ext (y := empty3) h0 h1 h2)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (gset3_ext (y := pick 2) h0 h1 h2))))
  · exact Or.inr (Or.inr (Or.inl (gset3_ext (y := pick 1) h0 h1 h2)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (htop (by simp only [card3, h0, h1, h2]; decide)))))
  · exact Or.inr (Or.inl (gset3_ext (y := pick 0) h0 h1 h2))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (htop (by simp only [card3, h0, h1, h2]; decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (htop (by simp only [card3, h0, h1, h2]; decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (htop (by simp only [card3, h0, h1, h2]; decide)))))

/-- **Distinctness: the five are pairwise inequivalent** — six separations by an
explicit context among the below-threshold states, four by the answer itself
against the top class. With `threshold_classes_complete`, the quotient of a
three-element universe under `|s| ≥ 2` has exactly five elements — more than the
membership quotient's two (§4), and, unlike the count quotient (§5) which is the
identity partition, strictly coarser than the states it partitions
(`threshold_coarser_than_state`). That is the sense in which it interpolates. -/
theorem threshold_classes_distinct :
    ¬ CtxEquiv (atLeast 2) empty3 (pick 0) ∧ ¬ CtxEquiv (atLeast 2) empty3 (pick 1)
      ∧ ¬ CtxEquiv (atLeast 2) empty3 (pick 2) ∧ ¬ CtxEquiv (atLeast 2) empty3 full3
      ∧ ¬ CtxEquiv (atLeast 2) (pick 0) (pick 1)
      ∧ ¬ CtxEquiv (atLeast 2) (pick 0) (pick 2)
      ∧ ¬ CtxEquiv (atLeast 2) (pick 1) (pick 2)
      ∧ ¬ CtxEquiv (atLeast 2) (pick 0) full3
      ∧ ¬ CtxEquiv (atLeast 2) (pick 1) full3
      ∧ ¬ CtxEquiv (atLeast 2) (pick 2) full3 :=
  ⟨not_ctxEquiv_of_context (pick 1) (by decide),
   not_ctxEquiv_of_context (pick 0) (by decide),
   not_ctxEquiv_of_context (pick 0) (by decide),
   fun h => absurd h.1 (by decide),
   not_ctxEquiv_of_context (pick 1) (by decide),
   not_ctxEquiv_of_context (pick 2) (by decide),
   not_ctxEquiv_of_context (pick 2) (by decide),
   fun h => absurd h.1 (by decide),
   fun h => absurd h.1 (by decide),
   fun h => absurd h.1 (by decide)⟩

end MinimalSummary

end Uwueave
