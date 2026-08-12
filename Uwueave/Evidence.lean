/-
# Uwueave.Evidence — two dimensions, four states, and the future-exclusion theorem.

`Holes.lean` replicated a *computation* and gave its answer a carrier:
`Partial α = GSet α`, a grow-only set of candidate values. This file corrects
that carrier and states the theorem `Holes.lean` did not have.

## Origin: an external review, and the two corrections it made

Both corrections below are **codex's**, from a review of this library's
hole calculus. This file is their execution; the credit for the diagnosis is
not ours.

### Correction 1 — one carrier was carrying two independent facts

`Partial α = GSet α` conflates *observed incompatible candidates* with *unseen
admissible future information*. Four situations must be distinguishable and
that carrier distinguishes two of them:

| candidates | future closed? | the honest result           |
|------------|----------------|-----------------------------|
| one        | yes            | `47` — exact                |
| one        | no             | `47 + ⟨pending⟩` — open     |
| several    | yes            | `fork {47, 49}` — waiting will NOT fix it |
| several    | no             | open fork                   |

The closed fork is the one the old carrier could not say, and it is the one an
interface most needs: it is the difference between a spinner and a prompt.
`ResultEvidence α` (§1) therefore carries **three** grow-only components —
`candidates`, `obligations`, `certificates` — and `render` (§4) computes which
of the four (plus the empty `vacuous`) a piece of evidence is in. §5 inhabits
all four with named witnesses, because a distinction nothing inhabits is
decoration.

### Correction 2 — the headline we proposed was false in both directions

The proposed headline was: *a hole persists across all gossip-only extensions
**iff** the expression is non-monotone at that position.* Codex refuted it both
ways, citing Power–Koutris–Hellerstein, "The Free Termination Property of
Queries Over Time" (arXiv:2502.00222):

  * **(a) a non-monotone query can already be final.** The paper's §4.1
    example: `Q() = R(c) ∧ ¬S(c)` is neither monotone nor antitone, yet "it has
    free termination states: these are the states in which the tuple `S(c)` is
    in the instance" — once `S(c)` has arrived, `Q` is false and pinned.
  * **(b) a monotone query can stay non-final forever.** A threshold query
    (`|R| > 10`) is monotone and offers free termination *only where the answer
    is true*; below the threshold "a machine cannot know if there is some
    additional element out there" — every false state is non-final, forever.

So **global monotonicity and state-relative finality are different notions**,
and neither implies the other. §11 proves exactly that — `qNonMono` (this
library's `R(c) ∧ ¬S(c)`) is non-monotone with free-termination states;
`qMono` is monotone with none at any false state — so the false iff is refuted
in both directions without ever being restated as if it might hold.

The paper's Definition 3 supplies the notion that replaces it: a **free
termination state** is *state-relative* — `s` is one for `Q` when every state
reachable from `s` gives `Q` the same value. That is `FreeTermination` in §7,
and it is what "final" means everywhere below.

## The corrected headline

`divergent_futures_force_nonexact` (§9):

    two admissible reachable futures that give different answers at a result
    position ⇒ no sound evaluator may report that position exact.

with its positive companion `exact_sound`: an exact value survives every
permitted future. The slogan, which is what the pair means together:

> **no exact value without stability evidence; no hidden fork after reachable
> divergence.**

"Sound" is two independently meaningful properties (§8's `SoundEvaluator`), not
a restatement of the conclusion: an exact report is *true where it is made*
(`correct`), and it is *never retracted* along a permitted future
(`irrevocable`). The theorem is that those two cannot survive a reachable
divergence — the shape of the paper's Theorem 22 argument, where an algorithm
that sets `ready` must still be right at every larger instance it may yet see.

## What is earned rather than assumed

`Holes.lean`'s boundary listed "the `Stable` → `Era` bridge is prose" as
⟨UNDONE⟩: its collapse licence `Stable Arriving P` was abstract in what may
still arrive. Here the licence is **read off the evidence**: `Closed e` says
every source `e` is still waiting on carries a closure certificate, and
`closed_freezes` (§8) proves that a closed evidence's candidate set cannot move
under any admissible future. That is the licence as a theorem about the
evidence rather than a hypothesis handed in — and `render` is then a genuinely
non-trivial `SoundEvaluator` (§8), not a vacuous one.

Two prices are paid in public, not deferred:

  * **`render` retracts if membership is open** (⚠ `render_retracts_when_a_new_source_appears`).
    A certificate closes the sources you *know about*. If a new source may still
    appear, an evidence that rendered `exact` re-opens to `provisional` — a
    retraction, so `render` is **not** sound for the plain extension future.
    Soundness holds for `SealedFuture`, which closes the source set too. This is
    exactly `Holes.lean` §6's "closed membership" caveat, now a theorem with a
    witness rather than a parenthesis.
  * **Closure merges; determinacy does not.** `closed_iconfluent` (§3) says two
    closed evidences merge to a closed one — coordination-free, by
    `Confluence.lean`'s own judgement. The fork/exact axis is the opposite:
    `Holes.determinacy_not_iconfluent` prices it. The two dimensions of
    correction 1 have *opposite* coordination verdicts, which is the sharpest
    argument that they are two dimensions.

## Literature — what each is for here

  * **Free Termination** (Power, Koutris, Hellerstein, arXiv:2502.00222; PDF in
    `~/paperbin/uweave/`) — state-relative finality (Def. 3), the two refutations
    of §11, and Theorem 22's shape for §9. Their §1.1 also states the gap this
    file is about: CRDTs give *quiescence*, not free termination — you cannot
    locally tell that you have heard everything.
  * **Complete CALM** (Hellerstein, arXiv:2602.09435) — the broad semantic
    ancestor. A specification is monotone when "every admissible outcome at a
    history has a compatible refinement at every causal extension"; ours is that
    condition made **instance- and position-shaped**: this evidence, this result
    position, these two reachable futures. Complete CALM quantifies over
    histories and outcome structures; §9 is one instance of that pattern with a
    concrete carrier, and claims nothing about the general theorem.
  * **λ∨** (Rioux, Zdancewic, arXiv:2504.02975) — the approximation-order and
    ambiguity prior art: values grow along a *streaming order* that coincides
    with the Scott approximation order, and their `f x = {1} if x ∋ 2 but ∌ 4`
    is precisely an observation that is unsafe to act on because a later state
    revokes it. `provisional` is that reading with the revocability made
    explicit in the type instead of left to the programmer.
  * **Timely progress tracking** (Brun, Decova, Lattuada, Traytel, ITP 2021) —
    the better model for `obligations` than "a set of absent peers". Timely's
    frontiers are *antichains of timestamps that lower-bound what may still
    appear at an input*; an operator retires a range of timestamps when the
    frontier passes it. `obligations` is that frontier at our carrier and
    `certificates` is its advance; the antichain structure itself is not
    modelled here (see the boundary).
  * **LVars** (Kuper, Newton, FHPC'13) and **Hazel** (Omar et al., POPL'19) —
    inherited from `Holes.lean`: `certificates` is LVars' freeze with the
    blocking removed, and `provisional` is Hazel's hole carried as a value.
  * **ERA** (Dougal, PaPoC 2026; `Era.lean`) — the pattern §6 mirrors:
    arbitration **adds** an announcement and never deletes an event, and the
    verdict is derived from the resulting order. `certify` is that move at this
    carrier: `arbitration_adds_a_certificate` changes the rendered view while
    the candidate set is *equal*, not smaller.

## Honest boundary

⟨TERMINAL⟩ = a theorem of the model; ⟨UNDONE⟩ = work wearing a caveat's
clothes.

  * **`obligations` here is a flat set of source names, not an antichain of
    timestamps.** `Uwueave.Frontier` now supplies genuine timestamp antichains,
    range retirement, the flat-model separation, and — under explicit world
    well-formedness, completeness, and settlement hypotheses — stability of
    `Evidence.values`. ⟨UNDONE for this old carrier and deployment⟩
    `ResultEvidence` still stores no timestamp, progress messages are neither
    generated nor authenticated, and the successor proves neither full `render`
    stability nor that a runtime honestly advances its frontier.
  * **A certificate is trusted, not verified.** ⟨UNDONE⟩ Nothing here says a
    certificate was *earned*: `certify` adds one unconditionally, exactly as
    `Era.advance` announces a cut unconditionally, and the price is the same
    trust in the arbiter that `Era.lean`'s §5.1 prices. The transport from
    `Era.final_view_immune` (a finalised prefix stops moving) into a
    `certificates` bit is still prose — `Holes.lean` listed that bridge as
    unbuilt and this file narrows it to one component rather than closing it.
  * **`SealedFuture` closes the source set by fiat.** ⟨TERMINAL for soundness,
    ⟨UNDONE⟩ as deployment⟩ The retraction theorem shows why the restriction is
    needed; what is *not* built is any mechanism that establishes membership
    closure in a running system. A deployment that cannot close its source set
    gets `provisional`, correctly, forever. `Uwueave.WorldFuture` is the next
    model rung: it makes the issued pool, roster, frontier and epoch explicit and
    proves quiescence is a sound world-indexed certificate. It still does not
    manufacture closure or eventual delivery in a running system.
  * **`render` is noncomputable.** ⟨TERMINAL at this carrier⟩ "Is there exactly
    one candidate value" quantifies over an unbounded type, so `render` takes
    the decisions classically, exactly as `Holes.evalSet` does. `Classical.choice`
    is inside the audit floor. The list-shaped computable analogue that
    `Holes.evalSet_ofList` gives for the image is not built for `render`.
  * **The completeness half of §10 is a hypothesis with one inhabitant.**
    ⟨TERMINAL⟩ Soundness *alone* licenses no converse — `blindEval`, which
    always answers `vacuous`, is a sound evaluator that reports `exact`
    nowhere (`completeness_is_load_bearing`). So the iff of §10 is stated under
    a `CanonicalEvaluator` premise, and that premise is discharged for `render`
    (`render_canonical`) rather than left hanging.
  * **Typed expression positions now have an adapter.** ⟨DONE for `Preo.Expr`;
    terminal for arbitrary evidence producers⟩ `Preo.DerivedProgram` exposes
    exact child-path holes and their erased field reads, proves evaluation
    locality from either view, and materializes the result through this
    evidence carrier with an exact candidate/source membership theorem.
    `ResultEvidence` itself remains producer-agnostic and therefore carries no
    syntax tree internally.
-/
import Uwueave.Holes

namespace Uwueave.Evidence

open Uwueave Uwueave.Catalog

/-! ## §1. The evidence — three grow-only components, one inherited merge.

A **source** names something that may still speak: a peer, an epoch, a
frontier point. `ResultEvidence α` is the product of three grow-only sets:

  * `candidates` — observed candidate values, each *attributed* to the source
    that justified it (attribution is what lets a certificate bite in §8);
  * `obligations` — sources whose future contributions are still admissible.
    Timely's frontier: a lower bound on what may still appear;
  * `certificates` — sources declared closed. An arbiter's cut, a frontier
    advance, an LVars freeze.

The carrier is literally a product of `GSet`s, so the `MergeState` is the
product/G-Set lift — **componentwise, inherited, zero new merge proofs**. -/

/-- A source of future evidence: a peer, an epoch, a frontier point. -/
abbrev Source := Nat

/-- **The evidence behind one result position.** Candidates attributed to
sources; the sources still owed; the sources certified closed. -/
abbrev ResultEvidence (α : Type) : Type :=
  GSet (α × Source) × GSet Source × GSet Source

/-- Observed candidate values, each attributed to the source that justified it. -/
abbrev candidates {α : Type} (e : ResultEvidence α) : GSet (α × Source) := e.1

/-- The sources whose future contributions are still admissible. -/
abbrev obligations {α : Type} (e : ResultEvidence α) : GSet Source := e.2.1

/-- The sources declared closed. -/
abbrev certificates {α : Type} (e : ResultEvidence α) : GSet Source := e.2.2

/-- The merge is the product/G-Set lift: **componentwise, and inherited**. All
three components are grow-only, so the three CvRDT laws on evidence are the
three laws the components were replicated with — nothing new is proved. -/
example {α : Type} : MergeState (ResultEvidence α) := inferInstance

/-- The induced order is componentwise on the candidates. -/
theorem candidates_mono {α : Type} {s t : ResultEvidence α} (h : s ⊑ t) :
    candidates s ⊑ candidates t := congrArg Prod.fst h

/-- The induced order is componentwise on the obligations. -/
theorem obligations_mono {α : Type} {s t : ResultEvidence α} (h : s ⊑ t) :
    obligations s ⊑ obligations t := congrArg Prod.fst (congrArg Prod.snd h)

/-- The induced order is componentwise on the certificates. -/
theorem certificates_mono {α : Type} {s t : ResultEvidence α} (h : s ⊑ t) :
    certificates s ⊑ certificates t := congrArg Prod.snd (congrArg Prod.snd h)

theorem candidates_grow {α : Type} {s t : ResultEvidence α} (h : s ⊑ t)
    {p : α × Source} (hp : candidates s p = true) : candidates t p = true :=
  (Holes.gset_leq_iff_subset _ _).mp (candidates_mono h) p hp

theorem certificates_grow {α : Type} {s t : ResultEvidence α} (h : s ⊑ t)
    {o : Source} (ho : certificates s o = true) : certificates t o = true :=
  (Holes.gset_leq_iff_subset _ _).mp (certificates_mono h) o ho

/-- …and the order is *built* componentwise too: three component inclusions
make an evidence step. -/
theorem leq_of_components {α : Type} {s t : ResultEvidence α}
    (h1 : candidates s ⊑ candidates t) (h2 : obligations s ⊑ obligations t)
    (h3 : certificates s ⊑ certificates t) : s ⊑ t := by
  show (candidates s ⊔ candidates t,
        obligations s ⊔ obligations t, certificates s ⊔ certificates t) = t
  rw [h1, h2, h3]

/-! ## §2. The value axis — and the bridge back to `Holes.evalSet`.

`values e` forgets the attribution: the plain candidate *values*, which is
exactly `Holes.Partial α`. The point of §2 is that this is not a new model:
for evidence whose candidates come from a candidate-world image, `values` is
**equal** to `Holes.evalSet` (`values_fromWorlds`), and the headline
homomorphism transports with no reproof (`fromWorlds_candidates_hom`). -/

/-- The values behind an attributed candidate set. Classical for the same
reason `Holes.evalSet` is: the existential ranges over an unbounded type. -/
noncomputable def valuesOf {α : Type} (c : GSet (α × Source)) : Holes.Partial α :=
  fun a => Holes.truth (∃ o, c (a, o) = true)

/-- The candidate **values** of a piece of evidence: attribution forgotten. -/
noncomputable def values {α : Type} (e : ResultEvidence α) : Holes.Partial α :=
  valuesOf (candidates e)

theorem mem_values {α : Type} (e : ResultEvidence α) (a : α) :
    values e a = true ↔ ∃ o, candidates e (a, o) = true := Holes.truth_eq_true

/-- Equal candidate sets have equal values — the value axis is a function of
the candidates alone. -/
theorem values_congr {α : Type} {s t : ResultEvidence α}
    (h : candidates t = candidates s) : values t = values s := congrArg valuesOf h

/-- Evidence built from `Holes.lean`'s candidate worlds: the image of a
deterministic computation `f`, each answer attributed by `src` to the source
that justified the world it came from. This is `Holes.evalProv`'s shape with a
source name where the clock was. -/
noncomputable def fromWorlds {α : Type} (f : Holes.World → α)
    (src : Holes.World → Source) (W : GSet Holes.World)
    (obl cert : GSet Source) : ResultEvidence α :=
  (Holes.evalSet (fun w => (f w, src w)) W, obl, cert)

/-- **`Holes.evalSet_hom` transports to the evidence carrier, unreproved.** The
candidate component of evidence built from candidate worlds is a
join-homomorphism in the worlds: compute-then-merge = merge-then-compute, on
the new carrier, by the old theorem. -/
theorem fromWorlds_candidates_hom {α : Type} (f : Holes.World → α)
    (src : Holes.World → Source) (W₁ W₂ : GSet Holes.World)
    (obl cert : GSet Source) :
    candidates (fromWorlds f src (W₁ ⊔ W₂) obl cert)
      = candidates (fromWorlds f src W₁ obl cert)
        ⊔ candidates (fromWorlds f src W₂ obl cert) :=
  Holes.evalSet_hom _ W₁ W₂

/-- **The value axis IS `Holes.lean`'s answer.** For evidence built from
candidate worlds, forgetting the attribution recovers `Holes.evalSet f W` on
the nose. So `ResultEvidence` adds two dimensions to the old carrier without
disturbing the one it had, and every theorem of `Holes.lean` about the answer
applies to `values` verbatim. -/
theorem values_fromWorlds {α : Type} (f : Holes.World → α)
    (src : Holes.World → Source) (W : GSet Holes.World) (obl cert : GSet Source) :
    values (fromWorlds f src W obl cert) = Holes.evalSet f W := by
  refine Holes.gset_ext (fun a => ?_)
  rw [mem_values, Holes.mem_evalSet]
  constructor
  · rintro ⟨o, ho⟩
    obtain ⟨w, hw, hf⟩ := (Holes.mem_evalSet _ W (a, o)).mp ho
    exact ⟨w, hw, congrArg Prod.fst hf⟩
  · rintro ⟨w, hw, hf⟩
    exact ⟨src w, (Holes.mem_evalSet _ W (a, src w)).mpr ⟨w, hw, by rw [hf]⟩⟩

/-! ## §3. Closure — the second dimension, and its coordination verdict.

`Closed e` is the "future closed?" column of correction 1's table: every source
`e` is still waiting on has been certified. It is deliberately *not* a fact
about the candidate values — that is the whole point of the split.

And its coordination verdict is the **opposite** of the value axis's:
`closed_iconfluent` says closure survives merge (it is a per-source implication
between two grow-only sets), while `Holes.determinacy_not_iconfluent` says
"one candidate" does not. Two dimensions, two verdicts. -/

/-- **The future is closed**: every source still owed carries a certificate. -/
def Closed {α : Type} (e : ResultEvidence α) : Prop :=
  ∀ o, obligations e o = true → certificates e o = true

/-- **Closure is I-confluent** — two replicas that have each closed their own
futures merge to a closed future, with no coordination. Each obligation in the
merge came from one side, that side certified it, and certificates only grow.

Contrast `Holes.determinacy_not_iconfluent`, which refutes the same question
for the *value* axis: "at most one candidate" clashes on merge. The two
components of correction 1 are separated by a theorem, not by taste. -/
theorem closed_iconfluent {α : Type} :
    IConfluent (S := ResultEvidence α) Closed := by
  intro x y hx hy o ho
  have hor : obligations x o = true ∨ obligations y o = true :=
    (Holes.gset_mem_or _ _ o).mp ho
  show (certificates x o || certificates y o) = true
  rcases hor with h | h
  · rw [hx o h]; rfl
  · rw [hy o h]; exact Bool.or_true _

/-! ## §4. The rendered view — correction 1's table, computed.

`render` reads both dimensions and answers with one of five points: the four of
the table, plus `vacuous` for no candidates at all.

The empty case is the fifth point and is named as such rather than folded into
one of the four: zero candidates is `Holes.hole`, the lattice bottom, and it is
not "one candidate" nor "several". (It splits further by closedness — an
un-closed empty is "nothing yet", a closed empty is "nothing ever" — and this
file does not split it, because no theorem below needs the distinction.)

`provisional` is the table's *open* row; `open` is a Lean keyword, so the
constructor carries the reading in its name instead. -/

/-- The rendered result: correction 1's four states, plus the empty one. -/
inductive View (α : Type) : Type where
  /-- One candidate, and the future is closed: `47`. -/
  | exact (a : α)
  /-- One candidate, but evidence may still arrive: `47 + ⟨pending⟩`. -/
  | provisional (a : α)
  /-- Several candidates and the future is closed: waiting will NOT fix it. -/
  | forkedClosed
  /-- Several candidates and the future is open. -/
  | forkedOpen
  /-- No candidates: `Holes.hole`, the bottom. -/
  | vacuous

/-- Which of the five points a view is, as a numeral. Only ever used to tell
two constructors apart (`view_ne_of_tag`); it carries no meaning of its own. -/
def viewTag {α : Type} : View α → Nat
  | .exact _ => 0
  | .provisional _ => 1
  | .forkedClosed => 2
  | .forkedOpen => 3
  | .vacuous => 4

/-- Views with different tags are different views. -/
theorem view_ne_of_tag {α : Type} {a b : View α} (h : viewTag a ≠ viewTag b) :
    a ≠ b := fun heq => h (congrArg viewTag heq)

open Classical in
/-- **The view.** One unique candidate value splits by closure into
`exact`/`provisional`; several split into `forkedClosed`/`forkedOpen`; none is
`vacuous`. Noncomputable at this carrier for `Holes.evalSet`'s reason: both
decisions quantify over an unbounded type. -/
noncomputable def render {α : Type} (e : ResultEvidence α) : View α :=
  if hu : ∃ a, values e a = true ∧ ∀ b, values e b = true → b = a then
    if Closed e then View.exact (Classical.choose hu)
    else View.provisional (Classical.choose hu)
  else if ∃ a, values e a = true then
    (if Closed e then View.forkedClosed else View.forkedOpen)
  else View.vacuous

/-- **`render` reads exactly `(values, Closed)`.** Two evidences with the same
candidate-value set and the same closure truth render identically; attribution,
the particular obligation set, and the particular certificates may differ.

This is the congruence needed to transport a value-stability result into a
view-stability result once closure is also known to survive. -/
theorem render_congr {α : Type} {s t : ResultEvidence α}
    (hv : values s = values t) (hc : Closed s ↔ Closed t) :
    render s = render t := by
  classical
  simp only [render, hv, hc]

/-- `render` answers `exact a` on a sealed, inhabited, closed evidence. -/
theorem render_exact {α : Type} {e : ResultEvidence α} {a : α}
    (hm : values e a = true) (hs : Holes.SealsTo (values e) a) (hc : Closed e) :
    render e = View.exact a := by
  have hu : ∃ x, values e x = true ∧ ∀ b, values e b = true → b = x := ⟨a, hm, hs⟩
  have hch := Classical.choose_spec hu
  have heq : Classical.choose hu = a := hs _ hch.1
  simp only [render, dif_pos hu, if_pos hc, heq]

/-- `render` answers `provisional a` on a sealed, inhabited, **open** evidence:
the same value, and the admission that it may not be the last word. -/
theorem render_provisional {α : Type} {e : ResultEvidence α} {a : α}
    (hm : values e a = true) (hs : Holes.SealsTo (values e) a) (hc : ¬ Closed e) :
    render e = View.provisional a := by
  have hu : ∃ x, values e x = true ∧ ∀ b, values e b = true → b = x := ⟨a, hm, hs⟩
  have hch := Classical.choose_spec hu
  have heq : Classical.choose hu = a := hs _ hch.1
  simp only [render, dif_pos hu, if_neg hc, heq]

theorem not_unique_of_two {α : Type} {e : ResultEvidence α} {a b : α}
    (ha : values e a = true) (hb : values e b = true) (hab : a ≠ b) :
    ¬ ∃ x, values e x = true ∧ ∀ y, values e y = true → y = x := by
  rintro ⟨x, _, hx⟩
  exact hab ((hx a ha).trans (hx b hb).symm)

/-- `render` answers `forkedClosed` on two distinct candidates and a closed
future — the state the old carrier could not say: **waiting will not fix it.** -/
theorem render_forkedClosed {α : Type} {e : ResultEvidence α} {a b : α}
    (ha : values e a = true) (hb : values e b = true) (hab : a ≠ b)
    (hc : Closed e) : render e = View.forkedClosed := by
  simp only [render, dif_neg (not_unique_of_two ha hb hab),
    if_pos (show ∃ x, values e x = true from ⟨a, ha⟩), if_pos hc]

/-- `render` answers `forkedOpen` on two distinct candidates and an open
future. -/
theorem render_forkedOpen {α : Type} {e : ResultEvidence α} {a b : α}
    (ha : values e a = true) (hb : values e b = true) (hab : a ≠ b)
    (hc : ¬ Closed e) : render e = View.forkedOpen := by
  simp only [render, dif_neg (not_unique_of_two ha hb hab),
    if_pos (show ∃ x, values e x = true from ⟨a, ha⟩), if_neg hc]

/-- `render` answers `vacuous` exactly on the hole — no candidate values. -/
theorem render_vacuous {α : Type} {e : ResultEvidence α}
    (h : ∀ a, values e a = false) : render e = View.vacuous := by
  have hne : ¬ ∃ a, values e a = true := by
    rintro ⟨a, ha⟩
    rw [h a] at ha
    exact Bool.noConfusion ha
  have hnu : ¬ ∃ a, values e a = true ∧ ∀ b, values e b = true → b = a := by
    rintro ⟨a, ha, _⟩
    exact hne ⟨a, ha⟩
  simp only [render, dif_neg hnu, if_neg hne]

/-- **Inversion**: an `exact` report is backed by exactly the evidence that
licenses it — the value is a candidate, it seals the candidate set, and the
future is closed. This is what §8's soundness reads. -/
theorem values_of_render_exact {α : Type} {e : ResultEvidence α} {v : α}
    (h : render e = View.exact v) :
    values e v = true ∧ Holes.SealsTo (values e) v ∧ Closed e := by
  by_cases hu : ∃ x, values e x = true ∧ ∀ y, values e y = true → y = x
  · by_cases hc : Closed e
    · rw [render, dif_pos hu, if_pos hc] at h
      injection h with hv
      obtain ⟨hm, hs⟩ := Classical.choose_spec hu
      exact ⟨hv ▸ hm, fun b hb => hv ▸ (hs b hb), hc⟩
    · rw [render, dif_pos hu, if_neg hc] at h
      exact absurd h (view_ne_of_tag (by simp [viewTag]))
  · by_cases hne : ∃ x, values e x = true
    · by_cases hc : Closed e
      · rw [render, dif_neg hu, if_pos hne, if_pos hc] at h
        exact absurd h (view_ne_of_tag (by simp [viewTag]))
      · rw [render, dif_neg hu, if_pos hne, if_neg hc] at h
        exact absurd h (view_ne_of_tag (by simp [viewTag]))
    · rw [render, dif_neg hu, if_neg hne] at h
      exact absurd h (view_ne_of_tag (by simp [viewTag]))

/-- An `exact` report entails `Holes.Determinate` — so §5 of `Holes.lean`
prices it: reporting one answer is the uniqueness ceiling, and what buys it is
the closure certificate the inversion above extracts. -/
theorem exact_is_determinate {α : Type} {e : ResultEvidence α} {v : α}
    (h : render e = View.exact v) : Holes.Determinate (values e) :=
  Holes.sealsTo_determinate (values_of_render_exact h).2.1

/-! ## §5. All four states, inhabited.

Three peers, two answers (`47` and `49`), and four pieces of evidence that
differ only in which sources are owed and which are certified. The candidate
*values* are the same in the first two and the same in the last two: what
separates them is the second dimension, which is the claim correction 1 makes
and this section discharges. -/

/-- A peer. -/
abbrev alice : Source := 0
/-- A second peer. -/
abbrev bob : Source := 1
/-- A third peer. -/
abbrev carol : Source := 2

/-- Only `alice` may still speak. -/
def srcsA : GSet Source := fun o => decide (o = alice)
/-- `alice` and `bob` may still speak. -/
def srcsAB : GSet Source := fun o => decide (o = alice ∨ o = bob)
/-- `alice`, `bob` and `carol` may still speak. -/
def srcsABC : GSet Source := fun o => decide (o = alice ∨ o = bob ∨ o = carol)

/-- One candidate: `47`, from `alice`. -/
def cand47 : GSet (Holes.Val × Source) := fun p => decide (p = (47, alice))
/-- Two candidates: `47` from `alice`, `49` from `bob`. -/
def cand4749 : GSet (Holes.Val × Source) :=
  fun p => decide (p = (47, alice) ∨ p = (49, bob))

theorem mem_cand47 {b : Holes.Val} {o : Source} (h : cand47 (b, o) = true) :
    b = 47 ∧ o = alice := by
  have := of_decide_eq_true h
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem values_cand47 {e : ResultEvidence Holes.Val} (h : candidates e = cand47) :
    values e 47 = true ∧ Holes.SealsTo (values e) 47 := by
  constructor
  · exact (mem_values e 47).mpr ⟨alice, by rw [h]; decide⟩
  · intro b hb
    obtain ⟨o, ho⟩ := (mem_values e b).mp hb
    rw [h] at ho
    exact (mem_cand47 ho).1

theorem values_cand4749 {e : ResultEvidence Holes.Val}
    (h : candidates e = cand4749) :
    values e 47 = true ∧ values e 49 = true := by
  refine ⟨(mem_values e 47).mpr ⟨alice, by rw [h]; decide⟩,
          (mem_values e 49).mpr ⟨bob, by rw [h]; decide⟩⟩

/-- **One candidate, future closed.** `alice` is the only source owed and she
is certified: the honest result is the bare `47`. -/
def exactW : ResultEvidence Holes.Val := (cand47, srcsA, srcsA)

/-- **One candidate, future open.** The same value `47`, but `bob` is still
owed: the honest result is `47 + ⟨pending: bob⟩`. -/
def openW : ResultEvidence Holes.Val := (cand47, srcsAB, srcsA)

/-- **Several candidates, future closed.** `47` and `49`, both sources
certified: a fork that waiting will not fix. -/
def forkedClosedW : ResultEvidence Holes.Val := (cand4749, srcsAB, srcsAB)

/-- **Several candidates, future open.** `47` and `49`, with `carol` still
owed. -/
def forkedOpenW : ResultEvidence Holes.Val := (cand4749, srcsABC, srcsAB)

theorem closed_exactW : Closed exactW := fun _ h => h
theorem closed_forkedClosedW : Closed forkedClosedW := fun _ h => h

theorem not_closed_openW : ¬ Closed openW := by
  intro h
  exact Bool.noConfusion (h bob (by decide))

theorem not_closed_forkedOpenW : ¬ Closed forkedOpenW := by
  intro h
  exact Bool.noConfusion (h carol (by decide))

/-- **THE FOUR STATES ARE REAL.** Each of correction 1's four rows is
inhabited, by evidence differing only in the two dimensions the row names.
`exactW` and `openW` have *identical* candidate sets and different views;
`forkedClosedW` and `forkedOpenW` likewise. That is the whole claim: the second
dimension is not derivable from the first. -/
theorem four_states_inhabited :
    render exactW = View.exact 47
      ∧ render openW = View.provisional 47
      ∧ render forkedClosedW = View.forkedClosed
      ∧ render forkedOpenW = View.forkedOpen := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact render_exact (values_cand47 (e := exactW) rfl).1
      (values_cand47 (e := exactW) rfl).2 closed_exactW
  · exact render_provisional (values_cand47 (e := openW) rfl).1
      (values_cand47 (e := openW) rfl).2 not_closed_openW
  · exact render_forkedClosed (values_cand4749 (e := forkedClosedW) rfl).1
      (values_cand4749 (e := forkedClosedW) rfl).2 (by decide) closed_forkedClosedW
  · exact render_forkedOpen (values_cand4749 (e := forkedOpenW) rfl).1
      (values_cand4749 (e := forkedOpenW) rfl).2 (by decide) not_closed_forkedOpenW

/-- The candidate sets of the two single-value witnesses are **equal**: the
`exact`/`provisional` split is carried entirely by the second dimension. -/
theorem exactW_openW_same_candidates : candidates exactW = candidates openW := rfl

/-- Likewise for the two forks. -/
theorem forked_same_candidates :
    candidates forkedClosedW = candidates forkedOpenW := rfl

/-! ## §6. Arbitration adds a certificate; it never deletes evidence.

`Era.lean`'s arbiter never names a winner and never removes an event — it
announces a cut, and the verdict is derived. `Authority.lean` and
`GatedEra.lean` keep the same discipline. `certify` is that move here: the
candidate set is *equal* before and after, the state moves *up* the lattice,
and the rendered view changes because the second dimension did. -/

/-- **Arbitration**: certify one source closed. Grow-only, and the candidate
set is untouched. -/
def certify {α : Type} (e : ResultEvidence α) (o : Source) : ResultEvidence α :=
  (candidates e, obligations e, fun o' => certificates e o' || decide (o' = o))

/-- Certifying deletes no evidence: the candidate set is unchanged. -/
theorem certify_keeps_candidates {α : Type} (e : ResultEvidence α) (o : Source) :
    candidates (certify e o) = candidates e := rfl

/-- Certifying moves *up* the lattice — it is monotone information, like every
other move in this library. -/
theorem certify_grows {α : Type} (e : ResultEvidence α) (o : Source) :
    e ⊑ certify e o := by
  refine leq_of_components (leq_refl _) (leq_refl _) ?_
  refine (Holes.gset_leq_iff_subset _ _).mpr (fun o' h => ?_)
  show (certificates e o' || decide (o' = o)) = true
  rw [h]
  rfl

/-- **THE ARBITRATION THEOREM.** One certificate turns `provisional 47` into
`exact 47`: the value never moved, the candidate set is *equal*, the state went
*up* the lattice — and only now may the answer be called exact.

This is `Era.lean`'s pattern at the evidence carrier: the arbiter adds an
announcement, deletes nothing, and the verdict is derived from what the
announcement closed. What a certificate buys is precisely the right to stop
saying "pending", which `Holes.lean` §6 priced and could not name. -/
theorem arbitration_adds_a_certificate :
    render openW = View.provisional 47
      ∧ render (certify openW bob) = View.exact 47
      ∧ candidates (certify openW bob) = candidates openW
      ∧ openW ⊑ certify openW bob := by
  have hclosed : Closed (certify openW bob) := by
    intro o ho
    show (srcsA o || decide (o = bob)) = true
    rcases of_decide_eq_true ho with rfl | rfl
    · decide
    · decide
  have hv := values_cand47 (e := certify openW bob) rfl
  exact ⟨four_states_inhabited.2.1, render_exact hv.1 hv.2 hclosed, rfl,
    certify_grows openW bob⟩

/-- The same move on a fork: `forkedOpen` becomes `forkedClosed`. The fork does
not go away — arbitration closed the *future*, not the disagreement, and the
honest rendering says so. -/
theorem arbitration_closes_a_fork :
    render forkedOpenW = View.forkedOpen
      ∧ render (certify forkedOpenW carol) = View.forkedClosed
      ∧ candidates (certify forkedOpenW carol) = candidates forkedOpenW := by
  have hclosed : Closed (certify forkedOpenW carol) := by
    intro o ho
    show (srcsAB o || decide (o = carol)) = true
    rcases of_decide_eq_true ho with rfl | rfl | rfl
    · decide
    · decide
    · decide
  have hv := values_cand4749 (e := certify forkedOpenW carol) rfl
  exact ⟨four_states_inhabited.2.2.2,
    render_forkedClosed hv.1 hv.2 (by decide) hclosed, rfl⟩

/-! ## §7. Two futures, and why they are not interchangeable.

A **future relation** says which states a replica may still reach. Two of them
are needed and they are genuinely different questions:

  * `DeliveryFuture pool` — only *delivery* of already-issued evidence. The
    pool is fixed; a future is any state between here and it. This is the
    question "have I heard everything that has been said?", whose answer point
    is the Free Termination paper's **quiescence point**.
  * `ExtensionFuture` — new application events are permitted too. This is the
    question "will anything more ever be said?", whose answer is **free
    termination** (their Def. 3) and which quiescence does not settle.

Both refuse to invent candidates from a source that has been certified closed,
or from a source never expected at all — that is `Admits`, and it is Timely's
frontier guarantee in one clause: the frontier is a lower bound on what may
still appear, so a certified source never speaks again.

The non-interchangeability is stated exactly, in §7's last theorem: the
non-implication runs in **one** direction only, because the delivery future is
a *sub*-relation of the extension future. -/

/-- A future relation on states. -/
abbrev Future (S : Type) := S → S → Prop

/-- **Free termination** (Power–Koutris–Hellerstein, Def. 3) at an arbitrary
carrier: `s` is a free-termination state for `q` under `F` when every reachable
future agrees with `s` on `q`. State-relative by construction — which is
correction 2's whole point. -/
def FreeTermination {S β : Type} (F : Future S) (q : S → β) (s : S) : Prop :=
  ∀ t, F s t → q t = q s

/-- **What a step may add.** A candidate that was not there may arrive only
from a source that is still owed (`obligations`) and has not been certified
closed (`certificates`). Timely's frontier guarantee, in one clause. -/
def Admits {α : Type} (s t : ResultEvidence α) : Prop :=
  ∀ p, candidates s p = false → candidates t p = true →
    obligations s p.2 = true ∧ certificates s p.2 = false

/-- **The extension future**: any monotone step that respects the certificates
already held. New application events are permitted. -/
def ExtensionFuture {α : Type} (s t : ResultEvidence α) : Prop :=
  s ⊑ t ∧ Admits s t

/-- **The delivery future**: the pool of issued evidence is fixed, and a future
is any state between here and it. Only delivery, no new application events. -/
def DeliveryFuture {α : Type} (pool s t : ResultEvidence α) : Prop :=
  s ⊑ t ∧ t ⊑ pool ∧ Admits s t

/-- **The sealed future**: an extension future over a *closed source set* — no
source may appear that was not already an obligation. §8 shows this is exactly
what `render` needs, and `render_retracts_when_a_new_source_appears` shows why
nothing weaker will do. -/
def SealedFuture {α : Type} (s t : ResultEvidence α) : Prop :=
  ExtensionFuture s t ∧ ∀ o, obligations t o = true → obligations s o = true

theorem admits_refl {α : Type} (s : ResultEvidence α) : Admits s s :=
  fun _ h1 h2 => Bool.noConfusion (h1.symm.trans h2)

theorem extensionFuture_refl {α : Type} (s : ResultEvidence α) :
    ExtensionFuture s s := ⟨leq_refl s, admits_refl s⟩

theorem sealedFuture_refl {α : Type} (s : ResultEvidence α) :
    SealedFuture s s := ⟨extensionFuture_refl s, fun _ h => h⟩

/-- Every delivery future is an extension future: the pool bound is an extra
constraint, not a different kind of step. -/
theorem delivery_is_extension {α : Type} {pool s t : ResultEvidence α}
    (h : DeliveryFuture pool s t) : ExtensionFuture s t := ⟨h.1, h.2.2⟩

/-- **Stability under extension implies stability under delivery** — and this
is an *implication*, not a non-implication, because the delivery relation is
contained in the extension relation. Half of the non-interchangeability answer
is therefore positive, and saying which half is the point. -/
theorem extension_stable_implies_delivery_stable {α β : Type}
    {q : ResultEvidence α → β} {pool s : ResultEvidence α}
    (h : FreeTermination ExtensionFuture q s) :
    FreeTermination (DeliveryFuture pool) q s :=
  fun t ht => h t (delivery_is_extension ht)

/-- **At the quiescence point every query is delivery-stable, trivially.** A
replica that has delivered the whole pool has exactly one delivery future —
itself — by antisymmetry of the induced order. This is the Free Termination
paper's observation that CRDTs offer quiescence and quiescence is not the
guarantee anyone wanted. -/
theorem quiesced_delivery_stable {α β : Type} (q : ResultEvidence α → β)
    (s : ResultEvidence α) : FreeTermination (DeliveryFuture s) q s := by
  intro t ht
  rw [leq_antisymm ht.1 ht.2.1]

/-- The extension of `openW` in which `bob` — still owed, not certified —
contributes the answer `49`. -/
def openForkW : ResultEvidence Holes.Val := (cand4749, srcsAB, srcsA)

theorem openW_extends_to_openForkW : ExtensionFuture openW openForkW := by
  constructor
  · refine leq_of_components ?_ (leq_refl _) (leq_refl _)
    refine (Holes.gset_leq_iff_subset _ _).mpr (fun p h => ?_)
    exact decide_eq_true (Or.inl (of_decide_eq_true h))
  · intro p h1 h2
    rcases of_decide_eq_true h2 with rfl | rfl
    · exact absurd h1 (by decide)
    · exact ⟨by decide, by decide⟩

/-- …and it is a *sealed* future too: no new source appears, only a new
candidate from a source already owed. -/
theorem openW_seals_to_openForkW : SealedFuture openW openForkW :=
  ⟨openW_extends_to_openForkW, fun _ h => h⟩

theorem render_openForkW : render openForkW = View.forkedOpen := by
  have hv := values_cand4749 (e := openForkW) rfl
  refine render_forkedOpen hv.1 hv.2 (by decide) ?_
  intro h
  exact Bool.noConfusion (h bob (by decide))

/-- ⚠ **THE NON-INTERCHANGEABILITY, exactly.** At `openW`, taken as its own
pool:

  * every query is stable under `DeliveryFuture openW` — there is nothing left
    to deliver;
  * `render` is **not** stable under `ExtensionFuture` — `bob`, still owed, can
    contribute `49` and turn `provisional 47` into `forkedOpen`.

So delivery-stability does not imply extension-stability. The converse
direction is **not** a second non-implication: it is the *theorem*
`extension_stable_implies_delivery_stable`, because `DeliveryFuture pool ⊆
ExtensionFuture`. Precisely one of the two implications fails, and it is this
one — which is the honest content of "the two futures are not interchangeable":
they are nested, and the smaller one is the one a CRDT can observe. -/
theorem futures_not_interchangeable :
    FreeTermination (DeliveryFuture openW) render openW
      ∧ ¬ FreeTermination ExtensionFuture render openW := by
  refine ⟨quiesced_delivery_stable render openW, ?_⟩
  intro hst
  have h := hst openForkW openW_extends_to_openForkW
  rw [render_openForkW, four_states_inhabited.2.1] at h
  exact absurd h (view_ne_of_tag (by simp [viewTag]))

/-! ## §8. The licence, earned — and the price of an open source set.

`Holes.lean` §6 assumed its collapse licence (`Stable Arriving P`, abstract in
what may still arrive) and listed the bridge to a real closure as ⟨UNDONE⟩.
Here the licence is a **theorem about the evidence**: `closed_freezes` says a
closed evidence's candidate set cannot move under any admissible future.

But a certificate closes the sources you know about. §8's ⚠ theorem shows what
happens when a source you did not know about appears: an `exact` report becomes
`provisional` — a **retraction** — so `render` is *not* a sound evaluator for
the plain extension future. It is one for `SealedFuture`, which closes the
source set as well. The restriction is stated as a theorem with a witness, not
as a parenthesis. -/

/-- **THE LICENCE, EARNED.** A closed evidence's candidate set is frozen: no
admissible future can move it. Every arrival would have to come from a source
that is owed and uncertified, and `Closed` says there is none.

This is what `Holes.lean` §6 assumed under the name `Stable` — here it is
derived from the evidence a replica actually holds. -/
theorem closed_freezes {α : Type} {s t : ResultEvidence α} (hc : Closed s)
    (hle : s ⊑ t) (hadm : Admits s t) : candidates t = candidates s := by
  refine Holes.gset_ext (fun p => ?_)
  constructor
  · intro hp
    cases hs : candidates s p with
    | true => rfl
    | false =>
      have h := hadm p hs hp
      have h1 := hc p.2 h.1
      rw [h.2] at h1
      exact Bool.noConfusion h1
  · intro hp
    exact candidates_grow hle hp

/-- A sealed future of a closed evidence changes neither the values nor the
closure — so it changes nothing `render` reads. -/
theorem sealed_future_of_closed {α : Type} {s t : ResultEvidence α}
    (hc : Closed s) (hf : SealedFuture s t) : values t = values s ∧ Closed t := by
  obtain ⟨⟨hle, hadm⟩, hmem⟩ := hf
  refine ⟨values_congr (closed_freezes hc hle hadm), fun o ho => ?_⟩
  exact certificates_grow hle (hc o (hmem o ho))

/-- The evidence `exactW` re-opened by a source it had never heard of: same
candidates, same certificates, one more obligation. -/
theorem exactW_extends_to_openW : ExtensionFuture exactW openW := by
  constructor
  · refine leq_of_components (leq_refl _) ?_ (leq_refl _)
    refine (Holes.gset_leq_iff_subset _ _).mpr (fun o h => ?_)
    exact decide_eq_true (Or.inl (of_decide_eq_true h))
  · intro p h1 h2
    exact Bool.noConfusion (h1.symm.trans h2)

/-- ⚠ **A CERTIFICATE CLOSES THE SOURCES YOU KNOW ABOUT.** `exactW` renders
`exact 47`; the admissible extension `openW` — identical candidates, identical
certificates, one **new** source owed — renders `provisional 47`. The report
was retracted.

So `render` is not irrevocable for `ExtensionFuture`, hence not a
`SoundEvaluator` there, and no amount of certifying fixes it: the defect is
that the *source set* was open. This is `Holes.lean` §6's "closed membership"
caveat as a theorem with a witness. A deployment that cannot close its source
set is entitled to `provisional` and to nothing better. -/
theorem render_retracts_when_a_new_source_appears :
    ExtensionFuture exactW openW
      ∧ render exactW = View.exact 47
      ∧ render openW = View.provisional 47
      ∧ candidates openW = candidates exactW
      ∧ ¬ SealedFuture exactW openW := by
  refine ⟨exactW_extends_to_openW, four_states_inhabited.1,
    four_states_inhabited.2.1, rfl, ?_⟩
  intro h
  exact Bool.noConfusion (h.2 bob (by decide))

/-! ### The soundness contract

Two independently meaningful properties. Neither says "all futures agree" —
that is the *conclusion* of §9, not a premise. -/

/-- **A sound evaluator.** An `exact` report is true where it is made
(`correct`), and is never retracted along a permitted future (`irrevocable`).
A report that can be withdrawn is not an answer; a report that is false where
it is made is not an answer either. -/
structure SoundEvaluator {S β : Type} (F : Future S) (answer : S → GSet β)
    (peval : S → View β) : Prop where
  /-- An exact report is backed by the answer at the state where it is made. -/
  correct : ∀ s v, peval s = View.exact v →
    answer s v = true ∧ Holes.SealsTo (answer s) v
  /-- An exact report is never retracted along a permitted future. -/
  irrevocable : ∀ s t v, F s t → peval s = View.exact v → peval t = View.exact v

/-- Two answer sets that each contain `v` and are each sealed by `v` are the
same set — namely `{v}`. The arithmetic behind §9. -/
theorem seal_mem_unique {β : Type} {P Q : GSet β} {v : β}
    (hp : P v = true) (hps : Holes.SealsTo P v)
    (hq : Q v = true) (hqs : Holes.SealsTo Q v) : P = Q := by
  refine Holes.gset_ext (fun b => ?_)
  constructor
  · intro h; rw [hps b h]; exact hq
  · intro h; rw [hqs b h]; exact hp

/-- **`render` is a sound evaluator for the sealed future.** `correct` is the
inversion of §4; `irrevocable` is `closed_freezes` plus the fact that closure
survives a sealed step. Non-trivially sound: it *does* report `exact`
(§5's `exactW`), unlike `blindEval` in §10. -/
theorem render_sound {α : Type} :
    SoundEvaluator (SealedFuture (α := α)) values render where
  correct := fun _ v h =>
    ⟨(values_of_render_exact h).1, (values_of_render_exact h).2.1⟩
  irrevocable := fun s t v hf h => by
    obtain ⟨hm, hs, hc⟩ := values_of_render_exact h
    obtain ⟨hval, hct⟩ := sealed_future_of_closed hc hf
    exact render_exact (by rw [hval]; exact hm) (by rw [hval]; exact hs) hct

/-! ## §9. THE FUTURE-EXCLUSION THEOREM.

    two admissible reachable futures that disagree about the answer
      ⇒ no sound evaluator may report the position exact.

**No exact value without stability evidence; no hidden fork after reachable
divergence.** The two hypotheses of `SoundEvaluator` do the work: the report
travels to both futures (irrevocability), and at each it must be true
(correctness), so both answers would have to be exactly `{v}`.

This is the shape of Power–Koutris–Hellerstein's Theorem 22 — an algorithm that
declares itself ready must still be right at every larger instance it may yet
receive — and it is the position-indexed, instance-shaped relative of Complete
CALM's monotonicity condition ("every admissible outcome has a compatible
refinement at every causal extension"). No claim is made here about the general
theorem in either paper; this is one instance over one carrier. -/

/-- **THE FUTURE-EXCLUSION THEOREM.** If two admissible reachable futures give
different answers at a result position, then **no** sound evaluator reports
that position exact. -/
theorem divergent_futures_force_nonexact {S β : Type} {F : Future S}
    {answer : S → GSet β} {peval : S → View β}
    (hsound : SoundEvaluator F answer peval) {s x y : S}
    (hx : F s x) (hy : F s y) (hne : answer x ≠ answer y) :
    ¬ ∃ v, peval s = View.exact v := by
  rintro ⟨v, hv⟩
  obtain ⟨hxm, hxs⟩ := hsound.correct x v (hsound.irrevocable s x v hx hv)
  obtain ⟨hym, hys⟩ := hsound.correct y v (hsound.irrevocable s y v hy hv)
  exact hne (seal_mem_unique hxm hxs hym hys)

/-- **The positive companion.** An exact value survives every permitted future:
at every reachable state the answer is still exactly `v`. This is what makes
`exact` worth reporting, and together with the theorem above it is the slogan:
no exact value without stability evidence; no hidden fork after reachable
divergence. -/
theorem exact_sound {S β : Type} {F : Future S} {answer : S → GSet β}
    {peval : S → View β} (hsound : SoundEvaluator F answer peval) {s : S} {v : β}
    (hv : peval s = View.exact v) {t : S} (hf : F s t) :
    answer t v = true ∧ Holes.SealsTo (answer t) v :=
  hsound.correct t v (hsound.irrevocable s t v hf hv)

/-- **The exclusion, instantiated.** `openW` has two sealed futures that
disagree — `bob` speaks, or `bob` does not — so no sound evaluator may call it
exact. `render` obeys: it answers `provisional 47`. The theorem is not derived
from `render`'s own behaviour here; it is applied to it. -/
theorem no_exact_at_an_open_fork : ¬ ∃ v, render openW = View.exact v := by
  refine divergent_futures_force_nonexact (render_sound (α := Holes.Val))
    openW_seals_to_openForkW (sealedFuture_refl openW) ?_
  intro heq
  have h49 : values openW 49 = true := by
    rw [← heq]; exact (values_cand4749 (e := openForkW) rfl).2
  obtain ⟨o, ho⟩ := (mem_values openW 49).mp h49
  have ho' : cand47 (49, o) = true := ho
  exact absurd (mem_cand47 ho').1 (by decide)

/-! ## §10. The converse, and the premise that carries it.

Soundness alone licenses **no** converse, and the reason is one line: an
evaluator that never reports anything is sound. So the iff below is stated
under a completeness premise, and `completeness_is_load_bearing` exhibits the
sound-but-silent evaluator that makes the premise necessary rather than
decorative. The premise is then discharged for `render`. -/

/-- The evaluator that always answers `vacuous`. -/
def blindEval {S β : Type} (_ : S) : View β := View.vacuous

/-- **A canonical evaluator**: sound, and complete — it reports `exact v`
whenever every permitted future agrees the answer is exactly `v`. -/
structure CanonicalEvaluator {S β : Type} (F : Future S) (answer : S → GSet β)
    (peval : S → View β) : Prop where
  /-- Exact reports are true and irrevocable. -/
  sound : SoundEvaluator F answer peval
  /-- If every permitted future agrees the answer is exactly `v`, say so. -/
  complete : ∀ s v,
    (∀ t, F s t → answer t v = true ∧ Holes.SealsTo (answer t) v) →
    peval s = View.exact v

/-- **The converse, under the premise that carries it.** For a canonical
evaluator, reporting exact is *equivalent* to every permitted future agreeing
on a single answer. The forward half is `exact_sound` and holds for every sound
evaluator; the backward half is completeness and holds for none of them
automatically. -/
theorem canonical_exact_iff {S β : Type} {F : Future S} {answer : S → GSet β}
    {peval : S → View β} (hcan : CanonicalEvaluator F answer peval) (s : S) :
    (∃ v, peval s = View.exact v)
      ↔ (∃ v, ∀ t, F s t → answer t v = true ∧ Holes.SealsTo (answer t) v) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, fun t ht => exact_sound hcan.sound hv ht⟩
  · rintro ⟨v, hall⟩
    exact ⟨v, hcan.complete s v hall⟩

/-- ⚠ **Completeness is load-bearing, and here is why.** `blindEval` is a sound
evaluator — vacuously, since it never reports `exact` — and at `exactW` every
sealed future agrees the answer is exactly `47`. It says `vacuous` anyway. So
no converse follows from soundness, and `canonical_exact_iff`'s premise is a
real hypothesis rather than a decoration. -/
theorem completeness_is_load_bearing :
    SoundEvaluator (SealedFuture (α := Holes.Val)) values
        (blindEval (S := ResultEvidence Holes.Val))
      ∧ (∀ t, SealedFuture exactW t →
          values t 47 = true ∧ Holes.SealsTo (values t) 47)
      ∧ ¬ ∃ v : Holes.Val,
          blindEval (S := ResultEvidence Holes.Val) (β := Holes.Val) exactW
            = View.exact v := by
  refine ⟨⟨fun _ _ h => absurd h (view_ne_of_tag (by simp [viewTag, blindEval])),
    fun _ _ _ _ h => absurd h (view_ne_of_tag (by simp [viewTag, blindEval]))⟩, ?_, ?_⟩
  · intro t ht
    obtain ⟨hval, _⟩ := sealed_future_of_closed closed_exactW ht
    rw [hval]
    exact values_cand47 (e := exactW) rfl
  · rintro ⟨v, h⟩
    exact absurd h (view_ne_of_tag (by simp [viewTag, blindEval]))

/-- Every value type used below has a second element to diverge towards; this
is what lets §10 build the disagreeing future that forces closure. -/
theorem natFresh : ∀ v : Nat, ∃ v' : Nat, v' ≠ v :=
  fun v => ⟨v + 1, Nat.succ_ne_self v⟩

/-- **`render` is complete.** If every sealed future agrees the answer is
exactly `v`, then the evidence must already be closed — because an uncertified
obligation is a licence to build a future that disagrees — and `render` reports
`exact v`.

The `fresh` hypothesis is where the disagreeing future gets its value: with a
one-element answer type nothing can diverge and the statement degenerates. -/
theorem render_complete {α : Type} [DecidableEq α]
    (fresh : ∀ v : α, ∃ v' : α, v' ≠ v) (s : ResultEvidence α) (v : α)
    (hall : ∀ t, SealedFuture s t →
      values t v = true ∧ Holes.SealsTo (values t) v) :
    render s = View.exact v := by
  obtain ⟨hm, hs⟩ := hall s (sealedFuture_refl s)
  have hclosed : Closed s := by
    intro o ho
    cases hcert : certificates s o with
    | true => rfl
    | false =>
      obtain ⟨v', hv'⟩ := fresh v
      have hle : s ⊑ (candidates s ⊔ Delta.addDelta (v', o), obligations s,
          certificates s) :=
        leq_of_components (le_merge_left _ _) (leq_refl _) (leq_refl _)
      have hadm : Admits s (candidates s ⊔ Delta.addDelta (v', o), obligations s,
          certificates s) := by
        intro p h1 h2
        have h3 : (candidates s p || Delta.addDelta (v', o) p) = true := h2
        rw [h1, Bool.false_or] at h3
        have hp : p = (v', o) := of_decide_eq_true h3
        rw [hp]
        exact ⟨ho, hcert⟩
      have hseal := (hall _ ⟨⟨hle, hadm⟩, fun _ h => h⟩).2
      have hmem : values (candidates s ⊔ Delta.addDelta (v', o), obligations s,
          certificates s) v' = true := by
        refine (mem_values _ v').mpr ⟨o, ?_⟩
        show (candidates s (v', o) || Delta.addDelta (v', o) (v', o)) = true
        rw [show Delta.addDelta (v', o) (v', o) = true from by
          simp [Delta.addDelta]]
        exact Bool.or_true _
      exact absurd (hseal v' hmem) hv'
  exact render_exact hm hs hclosed

/-- **`render` is canonical** — so §10's iff is not stated over an empty class.
The `exact` reports of `render` are exactly the positions on which every sealed
future agrees. -/
theorem render_canonical :
    CanonicalEvaluator (SealedFuture (α := Holes.Val)) values render :=
  ⟨render_sound, fun s v h => render_complete natFresh s v h⟩

/-! ## §11. Correction 2, as two theorems.

The proposed headline — *a hole persists across all gossip-only extensions iff
the expression is non-monotone at that position* — is false in both directions.
This section proves both failures at `Holes.lean`'s own carrier, over the
gossip future (plain lattice growth of the candidate worlds).

  * **(a)** `qNonMono` is this library's `R(c) ∧ ¬S(c)`: read the world `w0`,
    but only while `w1` has not been observed. It is not monotone, and it has
    free-termination states — every state that has already observed `w1`, where
    it is false and pinned. (Power–Koutris–Hellerstein §4.1: "it has free
    termination states: these are the states in which the tuple `S(c)` is in
    the instance".)
  * **(b)** `qMono` is "the world `w0` has been observed": monotone, and
    **no** state where it is false is final — a lower bound that safely grows
    and never settles. (Their threshold-query discussion: free termination for
    database instances where the answer is true.)

Global monotonicity and state-relative finality are different notions. -/

/-- The gossip future at `Holes.lean`'s carrier: plain lattice growth of the
candidate worlds. -/
def Gossip (W V : GSet Holes.World) : Prop := W ⊑ V

/-- A query is monotone when growth never retracts a `true`. -/
def MonotoneQuery (q : GSet Holes.World → Bool) : Prop :=
  ∀ W V, W ⊑ V → q W = true → q V = true

/-- "The candidate world `w0` has been observed" — a monotone threshold query. -/
def qMono : GSet Holes.World → Bool := fun W => W Holes.w0

/-- `R(c) ∧ ¬S(c)` at this carrier: `w0` observed and `w1` not. Neither monotone
nor antitone. -/
def qNonMono : GSet Holes.World → Bool :=
  fun W => W Holes.w0 && !(W Holes.w1)

theorem qMono_monotone : MonotoneQuery qMono :=
  fun _ _ h hq => (Holes.gset_leq_iff_subset _ _).mp h Holes.w0 hq

/-- `qNonMono` is not monotone: observing `w1` retracts it. -/
theorem qNonMono_not_monotone : ¬ MonotoneQuery qNonMono := by
  intro h
  have hle : Delta.addDelta Holes.w0 ⊑ Holes.Wab := le_merge_left _ _
  have hbad := h _ _ hle (by decide)
  rw [show qNonMono Holes.Wab = false from by decide] at hbad
  exact Bool.noConfusion hbad

/-- **(a) A non-monotone query can already be final.** In every state that has
observed `w1`, `qNonMono` is false and stays false under all gossip — a
free-termination state for a query that is not monotone. -/
theorem qNonMono_final_once_w1_seen {W : GSet Holes.World}
    (h : W Holes.w1 = true) : FreeTermination Gossip qNonMono W := by
  intro V hV
  have h' : V Holes.w1 = true := (Holes.gset_leq_iff_subset _ _).mp hV Holes.w1 h
  show (V Holes.w0 && !(V Holes.w1)) = (W Holes.w0 && !(W Holes.w1))
  rw [h, h']
  simp

/-- …and the state exists: `Holes.Wab`, the two-replica clash of `Holes.lean`
§4, has observed `w1`. So (a) is not a statement about an empty set of states. -/
theorem qNonMono_final_at_Wab : FreeTermination Gossip qNonMono Holes.Wab :=
  qNonMono_final_once_w1_seen (by decide)

/-- **(b) A monotone query can stay non-final forever.** No state where `qMono`
is false is a free-termination state: the world `w0` can always still arrive.
Stated for *every* such state, not one witness — a monotone lower bound that
safely grows never settles below its threshold. -/
theorem qMono_never_final_while_false {W : GSet Holes.World}
    (h : qMono W = false) : ¬ FreeTermination Gossip qMono W := by
  intro hst
  have hle : W ⊑ (W ⊔ Delta.addDelta Holes.w0) := le_merge_left _ _
  have hbad := hst _ hle
  rw [h, show qMono (W ⊔ Delta.addDelta Holes.w0) = true from
    Delta.addDelta_adds W Holes.w0] at hbad
  exact Bool.noConfusion hbad

/-- ⚠ **CORRECTION 2, AS ONE STATEMENT.** Global monotonicity and
state-relative finality are independent: a non-monotone query with a
free-termination state, and a monotone query with none at any state where it is
false. The iff we proposed fails in both directions, and the notion that
replaces it is the state-relative one — `FreeTermination`, Power–Koutris–
Hellerstein's Definition 3. -/
theorem monotonicity_and_finality_are_independent :
    (¬ MonotoneQuery qNonMono ∧ FreeTermination Gossip qNonMono Holes.Wab)
      ∧ (MonotoneQuery qMono
          ∧ ∀ W, qMono W = false → ¬ FreeTermination Gossip qMono W) :=
  ⟨⟨qNonMono_not_monotone, qNonMono_final_at_Wab⟩,
   ⟨qMono_monotone, fun _ h => qMono_never_final_while_false h⟩⟩

end Uwueave.Evidence
