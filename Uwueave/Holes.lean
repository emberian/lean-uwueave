/-
# Uwueave.Holes — replicated *computation*: candidate worlds, and one equation.

Every other file in this library replicates **data** and asks whether an
invariant survives the merge. This one replicates a **computation** and asks
the same question about its *result*.

The triangulation, and what each corner contributes:

  * **LVars** (Kuper–Newton, "LVars: Lattice-based Data Structures for
    Deterministic Parallelism", FHPC'13) — lattice variables, monotone writes,
    and a *threshold read* that **blocks** until the value crosses a bound.
    Blocking is what buys determinism back. In a replicated setting blocking
    is death: you cannot block on a peer who is offline for a week, and not
    blocking is the entire reason CRDTs exist.
  * **Hazel** (Omar–Voysey–Chugh–Hammer, "Live Functional Programming with
    Typed Holes", POPL'19) — an incomplete program still has meaning:
    evaluation proceeds *around* a hole, and the result refines as holes fill.
    Hazel's hole is the **non-blocking** version of a threshold read: instead
    of waiting for the answer you carry the shape of not-having-it.

    ⚠ **That last sentence is a provocation, and is labelled one.** "LVars
    block, Hazel doesn't" is rhetorically good and technically sloppy: the two
    are not one unknown under two policies, they are two unknowns. An LVar's
    threshold read blocks on a **synchronization** unknown — the value is a
    lattice point, it exists, and the read waits for it to cross a bound. A
    Hazel hole is **syntactic/semantic incompleteness** — no term has been
    written at that position, and evaluation carries the shape of the absence.
    λ∨ (Rioux–Zdancewic 2025) keeps them apart *inside one calculus*: `⊥`
    (produced nothing) is a different point from `⊥v` (produced something,
    nothing known about it), and both differ from `⊤` (an inconsistent result
    — the ambiguity error a join of incomparable symbols yields). The bridge
    between the two unknowns is **to be built, not asserted**; nothing below
    depends on the analogy holding. What is actually used from each corner is
    the lattice, and the lattice is `GSet World`.
  * **CALM** (Hellerstein–Alvaro) and **I-confluence** (Bailis et al.;
    `Confluence.lean`) — the judgement. Which results can be computed with no
    coordination at all, and which ones name a coordination point.

What this file adds is the third leg of that triangle in the library's own
machinery: **I-confluence lifted from data to computation**, and the one
equation that makes the lift free.

## The three corrections this file is built to honor

1. **Divergence, not growth.** A hole is not absence-refined-by-growth. The
   sibling repo's `Dregg2/Calculus/BiorthTensor.lean` tried to characterise
   coordination-freedom as closure under *directed* unions and refuted it
   (`directed_conjecture_refuted`): coordination prices **incomparable**
   replicas, not growing views. So `Partial α` here is not a chain of
   tightening approximations with a single ⊥ constructor. It is a genuine
   join-semilattice of **candidate sets** — `GSet α`, the library's own
   grow-only set — where two replicas may contribute *incomparable* answers
   and the merge keeps both. The memo's `⊥ = ⟨hole⟩` survives as `hole`, the
   empty candidate set (§2), which is the lattice bottom and nothing more
   special than that: "I know nothing yet" is "no candidates", and "we
   disagree" is "several candidates", and they are points of one lattice.

2. **Worlds, not per-variable sets.** The obvious move — give each replicated
   register its own candidate set and evaluate in the set monad — is
   **wrong**, and §4 proves it wrong rather than warning about it. The set
   monad decorrelates repeated variables: `pair(x, x)` over candidates
   `{0, 1}` yields four pairs where the truth is the two-element diagonal.
   Ground truth is the image of a deterministic `eval` over candidate
   **worlds** (whole valuations); the per-variable reading is a sound
   over-approximation and nothing better. Both directions are theorems:
   `world_below_monadic` (soundness, as a `⊑` in this library's own order)
   and `monadic_has_phantoms` (a concrete inhabitant of the gap).

3. **Do not collapse prematurely.** A multi-candidate result is an honest
   final answer, not a failure state — `47 + ⟨pending: bob, carol⟩` is a
   value, and for a loom the fork *is* the product (`MVRegister.lean` made
   the same call for a single slot). Collapse is a separate, explicit,
   **priced** operation: §6's `SealsTo`, whose licence is stability and whose
   price, without stability, is a concrete clash.

## The headline

`evalSet_hom` — for the image of a candidate-world set under any deterministic
`f`,

    evalSet f (W₁ ⊔ W₂) = evalSet f W₁ ⊔ evalSet f W₂

**compute-then-merge = merge-then-compute.** Taking the image is a
join-homomorphism, so a replica may gossip its *inputs* or its *results* and
land in the same place, in any order, with any batching (`evalSet_fold`). It
is the coordination-freedom equation for computations. The derived value is a
CRDT because its carrier *is* the substrate's (`derived_is_a_CRDT` — that part
is the abbreviation, not the theorem); what the homomorphism adds is that
computing commutes with that merge, and the rest of §3 is one line each on top
of it: `evalSet` is monotone (`evalSet_mono`); any schedule agrees
(`evalSet_fold`); and **any I-confluent invariant on the result pulls back to
an I-confluent invariant on the inputs** (`result_invariant_transfers`,
inhabited by `answer_includes_iconfluent`). ⚠ That last one used to be
advertised as "the piece §4.3 of the design memo said nobody has". It is not:
**LoRe** has essentially that combination and shipped three years earlier — see
retraction 4 below and `docs/BIBLIOGRAPHY.md`. The theorem is unaffected; the
size of the claim around it is not.

The proof is short and is *supposed* to be. The content is that ∃ distributes
over ∨; the value is the statement and the corollaries.

## What coordination buys, exactly

§5 is the other half, and it is a refutation. "This computation has at most
one candidate" — determinacy — is **not** I-confluent, neither on results
(`determinacy_not_iconfluent`) nor pulled back along a real computation
(`determinate_result_not_iconfluent`, whose clash pair is two replicas each
holding one world). It is the uniqueness ceiling of `Ceiling.lean` at a new
carrier, and saying so is the point: *demanding a determinate answer from a
replicated computation is provably a coordination requirement*, by the same
theorem that says a set cannot hold at most one element.

So the trade is exact. Computing is free (§3). Wanting one answer is not (§5).
Getting one answer anyway costs a stability licence (§6).

## The reading, in one line

**A replicated computation is a set of candidate worlds pushed through a
deterministic function; taking the image is a join-homomorphism, so every
derived value is a CRDT for free — and the only thing coordination buys is the
right to throw candidates away.**

## ⚑ Read this file with its successors — the forward pointers

Every other pointer in this tree runs upward: the later file cites the earlier
one and the earlier one never learns it was superseded. So, from this side:

  * **`Uwueave/Evidence.lean` corrects this file's carrier.** `Partial α :=
    GSet α` (§2 below) conflates two independent facts — *observed incompatible
    candidates* and *unseen admissible future information* — and Evidence says
    so in those words at its own §"Correction 1", replacing the carrier with a
    three-component `ResultEvidence α` (`candidates`, `obligations`,
    `certificates`) that can distinguish a **closed fork** ("waiting will not
    fix it") from an open one. That distinction is the difference between a
    spinner and a prompt, and this file cannot state it. Everything below is
    true as written about `GSet α`; it is simply a coarser carrier than the one
    the library now has. `Evidence.closed_freezes` also *derives* §6's `Stable`
    licence rather than assuming it.
  * **`Uwueave/Choreo.lean` is the choreography item in the boundary below**,
    landed — see that entry.
  * `Uwueave/WorldFuture.lean` re-indexes Evidence's futures by a **world**
    rather than a state — and its `World` is *not* this file's `World`
    (`abbrev World := List Val`, §2). WorldFuture states the disambiguation from
    its side and reads no `Holes.World`; this sentence is the other half of it.
  * ⚑ `Uwueave/Gluing.lean` also speaks of "holes" — guarded holes with
    delta-shaped fills — and it is **unrelated machinery**: it imports `Spec`
    and `Delta`, never this file, and contains no reference to `Holes`. Two
    vocabularies, one word.

## Honest boundary

Each item is labelled ⟨TERMINAL⟩ (a theorem *of the model* — no work would
remove it) or ⟨UNDONE U-0078⟩ (work, wearing a caveat's clothes).

  * **The generic carrier accepts arbitrary functions; a typed expression
    adapter now exists.** ⟨DONE for `Preo.Expr`, terminal for arbitrary `f`⟩
    `Preo.DerivedProgram` connects the intrinsically typed expression language
    to this world semantics, exposes exact child-path holes and erased reads,
    proves locality through an explicit `WorldDecoder`, and carries the
    merge/monotonicity classifier's positive and negative cases. `f : World → α`
    here remains intentionally unrestricted and therefore cannot itself be
    classified by syntax inspection.
  * **`f` may read the representation, not just the valuation.** ⟨UNDONE U-0079⟩ A
    `World` is a `List Val` — register `r` reads `read w r`, everything past
    the end reads `0` (`read_beyond`), so finite support is structural. But
    `[1]` and `[1, 0]` are distinct worlds with identical reads, and an
    arbitrary `f` can tell them apart (`List.length` does). No predicate here
    forces `f` to factor through `read`; a `ReadsOnly f` side condition and
    the quotient that makes it moot are both unbuilt. Every theorem below is
    true as stated regardless — the two worlds are simply two worlds — but a
    deployment that wants "world = valuation" must add that constraint
    itself.
  * **`evalSet` is noncomputable.** ⟨TERMINAL at this carrier⟩ The image of a
    `Bool`-valued predicate over an unbounded world type is not decidable, so
    the definition takes the existential classically. `Classical.choice` is
    inside the audit floor and no theorem here is weaker for it. §7 closes the
    practical half rather than leaving it as a caveat: for a candidate set
    given as an explicit **list** of worlds — which is what a replica actually
    holds — `evalSet_ofList` proves the classical image equals a computable
    `List.map`, and every theorem above applies to it verbatim.
  * **`evalSet` itself is not a differential evaluator.** ⟨NARROWED⟩
    `Preo.Incremental`, re-exposed for certified expressions by
    `Preo.DerivedProgram`, proves fresh-evaluation correctness and zero root
    recomputations for an off-dependency typed environment delta. Incremental
    maintenance of this file's arbitrary candidate-world image remains
    unbuilt; `evalSet_hom` alone is still only an answer-level equation.
  * **Choreography and endpoint projection.** ⟨DONE — see `Uwueave/Choreo.lean`⟩
    *choreography : computation :: CRDT : data* — one global program, projected
    per replica, with I-confluence deciding which projections need a
    coordination event. This item used to read "not here; a sibling lane builds
    beside this one". That lane landed: `Choreo.lean` opens with this slogan
    verbatim and carries `projection_sound`,
    `coordination_free_iff_iconfluent` and the seam refinement
    `seam_coordination_free`. It is kept in this list rather than deleted only
    because the sentence is the one Choreo quotes.
  * **The `Stable` → `Era` bridge is prose.** ⟨UNDONE U-0080, and narrowed⟩ §6's
    stability licence is abstract (`Stable Arriving P`), and
    `stable_inputs_seal_the_result` proves the *mechanism* — stability of the
    inputs transports to stability of the result, along the headline. What is
    **not** built is the transport from `Era.final_view_immune` (finalised
    prefixes of an event *list*, under an arbiter's cuts) into a `Stable`
    hypothesis on a `GSet World`. ⚑ What *has* landed since is one rung of it:
    `Evidence.closed_freezes` derives the freeze from the evidence a replica
    actually holds — "this is what `Holes.lean` §6 assumed under the name
    `Stable`", in its own words — so the remaining gap is Era's arbiter cut,
    not the licence in general.
  * **Determinacy's refutation is not a new theorem.** ⟨TERMINAL, and said
    plainly⟩ `determinacy_not_iconfluent` is `Ceiling.uniqueness_ceiling` at
    the constant selector, i.e. `Ceiling.ceiling_atMostOne` read at a new
    carrier. The new content of §5 is the *pullback*
    (`determinate_result_not_iconfluent`): the clash pair is two replicas
    holding one candidate **world** each, so the coordination requirement is
    exhibited on the inputs a program actually has.
  * **Source authenticity remains external; typed positions are now exact.**
    ⟨NARROWED⟩ §7 still accepts whatever provenance function `p` computes, and
    no theorem makes its clocks causally meaningful. `evalPositions` now gives
    a generic exact value/source/position image, and `Preo.DerivedProgram`
    instantiates positions with the exact `Expr.Hole` list. Its verified entry
    point requires an external `SourceAuthenticity` proof and rejects a
    mismatched fixture. Signatures, causal ownership, and computing "who do I
    need" dynamically remain deployment obligations.

## ⚠ Four retractions from the design memo this file was built from

`FORCODEX.md` §4 made claims the literature refutes. They are withdrawn there;
they are recorded here because this is the file they were about.

  1. **"Every piece of machinery in this repo transfers from data to
     computation unchanged."** ⚠ **FALSE**, and the damage is in "unchanged".
     Monotone (`x ⊑ y → f x ⊑ f y`) and join-preserving
     (`f (x ⊔ y) = f x ⊔ f y`) are different properties, and a verdict
     transported across a computation needs the **second**; monotone alone
     gives `f x ⊔ f y ⊑ f (x ⊔ y)` and no equation, i.e. gossip-then-compute
     and compute-then-gossip may part. **`evalSet_hom` below is not affected
     and it is worth saying why**: it takes the *image* of a candidate-world
     set under a deterministic `f`, and images genuinely distribute over
     unions — the content is that `∃` distributes over `∨`. The defect was the
     generalization from it, never the theorem. `Uwueave/JoinHom.lean` proves
     the separation rather than assuming it away: `monotone_not_joinHom`
     (`card` is monotone and is not a join homomorphism, both conjuncts about
     one function on one carrier), and the sharp form
     `no_count_merge_without_provenance`, quantified over **every** binary
     combiner — the local pair `(1, 1)` must mean `1` when two replicas saw
     the same element and `2` when they saw different ones, so no merge on
     summaries alone is exact and provenance is *forced*. The same file
     refutes the follow-on (`monotone_pullback_can_fail`) and states the
     architecture as an iff (`summaryFold_iff_joinHom`).
  2. **"A monotone expression's holes fill by gossip alone."** ⚠ Only under a
     **finite closed scope with fair and complete delivery**. Monotonicity
     says an answer never has to be taken back; it says nothing about when a
     node may stop waiting. Power–Koutris–Hellerstein (2025) call that second
     question *free termination* and separate it cleanly: a Boolean threshold
     query is monotone by construction, and its free-termination states are
     **exactly** those at or above its threshold antichain — below the line
     (`|R| > 10` when the truth is `false`) the answer is already correct and
     no node may ever say so. A monotone expression whose hole is open
     forever. In an indefinitely writable system that is the common case, and
     it is why §6's collapse takes a `Stable` hypothesis rather than a
     monotonicity side condition.
  3. **"Era's arbiter cut *is precisely* the causal cut / the LVar freeze."**
     ⚠ Softened to what is true: the three **play related roles** — each
     restricts which futures are admissible — and their **evidentiary
     meanings differ**, so what a collapse licensed by each is worth differs.
     An LVars freeze is local and unilateral inside one runtime (a later write
     is an error it raises, which is why LVars gets *quasi*-determinism). A
     causal cut is epistemic: downward-closed, so it excludes futures nobody
     has *seen*, not futures that may still be *sent*. Era's arbiter cut is
     social and trusted: a third party announces an epoch and
     `Era.final_view_immune` makes the finalised prefix stop moving — bought
     with a trusted role and priced in rollback, not derived from the lattice.
     `Stable` is abstract in `Arriving` for exactly this reason: three ways to
     discharge one hypothesis, and the transport from `Era.final_view_immune`
     into a `Stable` hypothesis is named **unbuilt** in the boundary above.
  4. **"Three verdicts on one program — deterministic? coordination-free? does
     my invariant on the result survive? — and nobody currently offers all
     three; the third is the piece nobody has."** ⚠ **WITHDRAWN.** **LoRe**
     (Haas, Mogk, Yanakieva, Bieniusa, Mezini, *"LoRe: A Programming Model for
     Verifiably Safe Local-First Software"*, arXiv:2304.07133v2) is essentially
     that combination, shipping, three years earlier: invariants verified
     statically against a dataflow, the interactions whose concurrency would
     violate one identified precisely, and a coordination protocol generated
     for exactly those. It targets peer-to-peer local-first, not geo-replicated
     stores. `result_invariant_transfers` and `answer_includes_iconfluent` are
     untouched — a theorem's truth and a project's priority are different
     questions, and only the first is machine-checked here. What survives is
     narrower and is what this library should be measured on: LoRe's verdict is
     binary and per-interaction, discharged by SMT, with no *segmented* verdict,
     no coordination-**frequency** quantity, no counterexample-as-deliverable,
     and no proof terms under a total axiom gate. On the axis a user cares
     about — *can I write my app in it* — LoRe is ahead, and nobody here has
     measured against it. The full entry is `docs/BIBLIOGRAPHY.md`; this
     retraction is recorded here because §3 is where the claim was made, and it
     reached the bibliography before it reached this file.

Literature, PDFs in `~/paperbin/uweave/`:
  * Kuper, Newton — "LVars: Lattice-based Data Structures for Deterministic
    Parallelism", FHPC 2013.
  * Omar, Voysey, Chugh, Hammer — "Live Functional Programming with Typed
    Holes", POPL 2019.
  * Hellerstein, Alvaro — "Keeping CALM: When Distributed Consistency is
    Easy", CACM 2020.
  * Bailis et al. — "Coordination Avoidance in Database Systems", VLDB 2015
    (the judgement, already `Confluence.lean`'s).
  * Rioux, Zdancewic — "Functional Meaning for Parallel Streaming" (λ∨),
    arXiv:2504.02975, 2025. **Prior art for a generic `Partial α`**: a whole
    lambda calculus over an approximation/streaming order, with joins of
    partial computations as a first-class parallel operator, absence
    distinguished from unknown-value, and ambiguity as an explicit error.
  * Power, Koutris, Hellerstein — "The Free Termination Property of Queries
    Over Time", arXiv:2502.00222, 2025. **Settlement is state-relative**
    (their Theorem 22 pairs a query with an input); monotonicity is not.
  * Adams, Griffis, Porter, Satish, Zhao, Omar — "Grove: A Bidirectionally
    Typed Collaborative Structure Editor Calculus", POPL 2025. **Typed holes
    × collaborative replicated editing is already occupied** — a CmRDT edit
    log with conflicts represented as holes in the typed term. Not archived
    locally; cited from an external review.
  * Haas, Mogk, Yanakieva, Bieniusa, Mezini — "LoRe: A Programming Model for
    Verifiably Safe Local-First Software", arXiv:2304.07133v2, 2023.
    **Prior art for §3's three-verdict framing** — see retraction 4. Not
    archived locally; relayed from an external review (codex).
  * Brun, Decova, Lattuada, Traytel — "Verified Progress Tracking for Timely
    Dataflow", ITP 2021. Frontiers as **antichains** bounding what may still
    arrive, verified in Isabelle/HOL — the shape an `Arriving` component of
    `Stable` should take if it ever becomes concrete.
-/
import Uwueave.Ceiling
import Uwueave.MVRegister

namespace Uwueave.Holes

open Uwueave Uwueave.Catalog

universe u v w

/-! ## §0. Three G-Set lemmas this file leans on.

`Catalog.lean` states `gset_mem_merge` as an equation on `Bool`. Everything
below reasons about *membership*, so the same facts are restated in `Prop`
form once, here, rather than re-derived at every use. They belong in
`Catalog`; they live here because this file owns no other. -/

/-- The classical indicator. A `GSet` is `Bool`-valued, and the images this
file takes are not decidable at this carrier (§2's boundary note), so the
`Bool` comes from `Classical.propDecidable`. `Classical.choice` is inside the
audit floor; nothing below is weaker for it. -/
noncomputable def truth (p : Prop) : Bool := @decide p (Classical.propDecidable p)

/-- The indicator says what it means. -/
theorem truth_eq_true {p : Prop} : truth p = true ↔ p :=
  ⟨@of_decide_eq_true p (Classical.propDecidable p),
   @decide_eq_true p (Classical.propDecidable p)⟩

/-- Two grow-only sets with the same members are the same set. -/
theorem gset_ext {α : Type u} {P Q : GSet α} (h : ∀ a, P a = true ↔ Q a = true) :
    P = Q := by
  funext a
  cases hP : P a with
  | false =>
    cases hQ : Q a with
    | false => rfl
    | true =>
      have hcon := (h a).mpr hQ
      rw [hP] at hcon
      exact absurd hcon (by decide)
  | true => exact ((h a).mp hP).symm

/-- Membership in a merge is membership in either side — `gset_mem_merge` as a
proposition. -/
theorem gset_mem_or {α : Type u} (x y : GSet α) (a : α) :
    (x ⊔ y) a = true ↔ x a = true ∨ y a = true := by
  rw [gset_mem_merge]
  cases x a <;> cases y a <;> simp

/-- The induced order on grow-only sets **is** inclusion. `Leq` is defined by
the merge (`Confluence.lean`), and for a G-Set that unfolds to "every member of
`x` is a member of `y`" — which is what every ⊑ below should be read as. -/
theorem gset_leq_iff_subset {α : Type u} (x y : GSet α) :
    x ⊑ y ↔ ∀ a, x a = true → y a = true := by
  constructor
  · intro h a ha
    have h2 : (x a || y a) = y a := congrFun h a
    rw [ha] at h2
    exact h2.symm
  · intro h
    funext a
    show (x a || y a) = y a
    cases hx : x a with
    | false => rfl
    | true => exact (h a hx).symm

/-! ## §1. Worlds — a candidate valuation of the replicated registers.

A **world** is one internally-consistent possibility for what every replicated
register holds. Registers are named by `Nat` and the carrier is a `List Val`:
register `r` reads position `r`, and everything past the end reads `0`. Finite
support is therefore structural (`read_beyond`), not a side condition, and the
carrier keeps `DecidableEq` — which is what lets the concrete witnesses below
be exhibited rather than described.

A replica's knowledge is a **set** of worlds: exactly one candidate if it has
heard everything relevant, several if two peers said incompatible things, none
at the start. That set is a `GSet World` — a plain grow-only set, merged by
union, with the library's own instance and no new merge proofs. -/

/-- A register name. -/
abbrev Reg := Nat

/-- A register payload, kept `Nat` so every example is decidable. -/
abbrev Val := Nat

/-- A world: a finitely-supported valuation of the replicated registers.
Position `r` of the list is register `r`; registers past the end are unwritten
and read `0`. -/
abbrev World := List Val

/-- What register `r` holds in world `w`. Unwritten registers read `0`. -/
def read : World → Reg → Val
  | [], _ => 0
  | v :: _, 0 => v
  | _ :: rest, r + 1 => read rest r

/-- **Support is finite, by construction**: past the end of the list every
register reads `0`. This is the "finitely-supported" in "finitely-supported
valuation", and it is a theorem about the carrier rather than a hypothesis
carried around. -/
theorem read_beyond : ∀ (w : World) (r : Reg), w.length ≤ r → read w r = 0
  | [], _, _ => rfl
  | _ :: rest, 0, h => absurd h (Nat.not_succ_le_zero rest.length)
  | _ :: rest, r + 1, h => read_beyond rest r (Nat.le_of_succ_le_succ h)

/-- A replica's candidate worlds merge by union — the G-Set instance, free. -/
example : MergeState (GSet World) := inferInstance

/-! ## §2. Partial results — the candidate set, and the hole.

`Partial α` is the type of *answers*: a set of candidate values. The three
readings of one carrier, and correction 1 is that they are three points of one
lattice rather than three constructors:

  * empty — `hole`, the lattice bottom: no candidate yet, Hazel's ⟨hole⟩;
  * one candidate — a determinate answer (§5 prices keeping it that way);
  * several — an honest, final, multi-candidate answer (correction 3).

`evalSet f W` is the **image** of the candidate worlds under a deterministic
`f`: exactly the answers some candidate world justifies, and no others. -/

/-- A partial result: the set of candidate values. Literally `GSet α` — same
carrier, same merge, same laws, so a derived value is a replicated value with
no new machinery (§7). -/
abbrev Partial (α : Type u) := GSet α

/-- **The hole**: no candidates. The lattice bottom, and the memo's ⟨hole⟩ —
demoted from a constructor to a point, because a hole is just the least
informative answer (`hole_least`). -/
def hole {α : Type u} : Partial α := fun _ => false

/-- The hole is below every answer: it is the bottom of the same lattice, not
a separate layer. -/
theorem hole_least {α : Type u} (P : Partial α) : hole ⊑ P := by
  funext a
  show (false || P a) = P a
  rfl

/-- **The image of the candidate worlds.** `evalSet f W` holds exactly the
values `f` takes on some candidate world — the ground truth of correction 2:
evaluation is deterministic *per world*, and multiplicity comes only from not
knowing which world you are in.

Noncomputable by necessity at this carrier (the existential ranges over an
unbounded world type); §7 gives the computable equal for a candidate set held
as a list, which is what a replica actually holds. -/
noncomputable def evalSet {α : Type u} (f : World → α) (W : GSet World) :
    Partial α :=
  fun a => truth (∃ w, W w = true ∧ f w = a)

/-- Membership in the image, unfolded once so nothing below has to. -/
theorem mem_evalSet {α : Type u} (f : World → α) (W : GSet World) (a : α) :
    evalSet f W a = true ↔ ∃ w, W w = true ∧ f w = a := truth_eq_true

/-- **A computation over nothing is a hole.** The empty candidate set images
to the empty candidate set — the bottom is preserved, so "I have heard
nothing" evaluates to "I know nothing", not to a wrong answer. -/
theorem evalSet_hole {α : Type u} (f : World → α) : evalSet f hole = hole := by
  refine gset_ext (fun a => ?_)
  constructor
  · intro h
    obtain ⟨_, hw, _⟩ := (mem_evalSet f hole a).mp h
    exact Bool.noConfusion (show (false : Bool) = true from hw)
  · intro h
    exact Bool.noConfusion (show (false : Bool) = true from h)

/-- A replica certain of its world computes a single candidate: the image of
a singleton world set is the singleton answer. `Delta.addDelta` is the
library's minimal delta and doubles here as the set monad's `pure`. -/
theorem evalSet_single {α : Type} [DecidableEq α] (f : World → α) (w : World) :
    evalSet f (Delta.addDelta w) = Delta.addDelta (f w) := by
  refine gset_ext (fun a => ?_)
  rw [mem_evalSet]
  constructor
  · intro h
    obtain ⟨v, hv, hf⟩ := h
    have hvw : v = w := Ceiling.addDelta_unique hv (by simp [Delta.addDelta])
    subst hvw
    simp [Delta.addDelta, ← hf]
  · intro h
    have ha : a = f w := by simpa [Delta.addDelta] using h
    exact ⟨w, by simp [Delta.addDelta], ha.symm⟩

/-! ## §3. THE HEADLINE — the image is a join-homomorphism.

Two replicas each hold candidate worlds and each compute. One gossips its
worlds and recomputes; the other gossips its answer and merges answers. This
says they agree — **always**, for **every** deterministic `f`, with no
hypothesis on `f` whatsoever.

That is the coordination-freedom equation for computations. Its proof is three
lines of term over one lemma, because its content is that ∃ distributes over ∨;
its value is the statement, and the corollaries that are one line each. -/

/-- Membership in the image of a merge — the whole mathematical content of the
headline, isolated: a candidate answer after merging the worlds is a candidate
answer on one side or the other. -/
theorem mem_evalSet_merge {α : Type u} (f : World → α) (W₁ W₂ : GSet World)
    (a : α) :
    evalSet f (W₁ ⊔ W₂) a = true ↔
      evalSet f W₁ a = true ∨ evalSet f W₂ a = true := by
  rw [mem_evalSet, mem_evalSet, mem_evalSet]
  constructor
  · intro h
    obtain ⟨w, hw, hf⟩ := h
    rcases (gset_mem_or W₁ W₂ w).mp hw with hw' | hw'
    · exact Or.inl ⟨w, hw', hf⟩
    · exact Or.inr ⟨w, hw', hf⟩
  · intro h
    rcases h with ⟨w, hw, hf⟩ | ⟨w, hw, hf⟩
    · exact ⟨w, (gset_mem_or W₁ W₂ w).mpr (Or.inl hw), hf⟩
    · exact ⟨w, (gset_mem_or W₁ W₂ w).mpr (Or.inr hw), hf⟩

/-- **THE HEADLINE. Compute-then-merge = merge-then-compute.**

    evalSet f (W₁ ⊔ W₂) = evalSet f W₁ ⊔ evalSet f W₂

Taking the image of a candidate-world set is a **join-homomorphism**. A
replica may ship its inputs or ship its results; a peer may merge answers or
merge worlds and recompute; and every route lands on the same value. No
hypothesis on `f`: not monotonicity, not continuity, not determinism-in-the-
lattice-sense — only that `f` is a function, i.e. that evaluation is
deterministic *within* a world, which is correction 2's whole point.

Everything else in this file is a corollary of this equation or a refutation
saying what it does *not* buy (§5). -/
theorem evalSet_hom {α : Type u} (f : World → α) (W₁ W₂ : GSet World) :
    evalSet f (W₁ ⊔ W₂) = evalSet f W₁ ⊔ evalSet f W₂ :=
  gset_ext fun a =>
    (mem_evalSet_merge f W₁ W₂ a).trans
      (gset_mem_or (evalSet f W₁) (evalSet f W₂) a).symm

/-- The derived value's merge is the substrate's own — inherited, not
rebuilt. -/
example {α : Type u} : MergeState (Partial α) := inferInstance

/-- **A derived value is itself a CRDT.** Not by analogy: `Partial α` *is*
`GSet α`, so the three CvRDT laws on a computed answer are the three laws the
inputs were replicated with, at the inherited instance — and `evalSet_hom`
says the derivation commutes with that merge. Nothing about the computation
enters; there is no second convergence argument to get wrong. -/
theorem derived_is_a_CRDT {α : Type u} (P Q R : Partial α) :
    P ⊔ Q = Q ⊔ P ∧ (P ⊔ Q) ⊔ R = P ⊔ (Q ⊔ R) ∧ P ⊔ P = P :=
  ⟨merge_comm P Q, merge_assoc P Q R, merge_idem P⟩

/-- **`evalSet` is monotone**: learning more worlds never retracts an answer,
it only adds candidates. (`⊑` on a G-Set is inclusion — `gset_leq_iff_subset`.)
Immediate from the headline, and the reason gossip is safe to repeat on the
*result* side as well as the input side. -/
theorem evalSet_mono {α : Type u} (f : World → α) {W₁ W₂ : GSet World}
    (h : W₁ ⊑ W₂) : evalSet f W₁ ⊑ evalSet f W₂ := by
  show evalSet f W₁ ⊔ evalSet f W₂ = evalSet f W₂
  rw [← evalSet_hom, h]

/-- **Any schedule, any batching.** Fold a list of received world-sets into a
replica's state and compute once; or compute on each and fold the answers —
same value. This is `evalSet_hom` at the length of an actual gossip history,
and it is the sense in which derived-value replicas converge by the substrate's
own laws rather than by a new argument. -/
theorem evalSet_fold {α : Type u} (f : World → α) :
    ∀ (Ws : List (GSet World)) (init : GSet World),
      evalSet f (Ws.foldl (· ⊔ ·) init)
        = (Ws.map (evalSet f)).foldl (· ⊔ ·) (evalSet f init)
  | [], _ => rfl
  | W :: rest, init => by
      show evalSet f (rest.foldl (· ⊔ ·) (init ⊔ W))
          = (rest.map (evalSet f)).foldl (· ⊔ ·) (evalSet f init ⊔ evalSet f W)
      rw [evalSet_fold f rest (init ⊔ W), evalSet_hom]

/-- **I-confluence lifts from data to computation.** If an invariant on the
*result* is I-confluent, then "my inputs compute a legal result" is
I-confluent on the inputs — so the whole judgement of `Confluence.lean`
transfers along any computation, for free, by the headline.

The leg: not "is my program deterministic" (LVars) and not "is my program
monotone" (CALM), but *does my invariant on the answer survive the merge*. The
transfer is not vacuous in either direction — §5 exhibits a result invariant
that is **not** I-confluent and whose pullback therefore fails too, with the
clash pair on the inputs.

⚠ **Retracted, and the retraction belongs here.** This docstring used to say
the design memo's §4.3 called this "the piece nobody has". That claim is gone:
**LoRe** (Haas, Mogk, Yanakieva, Bieniusa, Mezini, arXiv:2304.07133) is
essentially the same combination, shipping, three years earlier — static
verification of invariants against a dataflow, with the coordination generated
for exactly the interactions that need it. What survives is narrower and is
stated in the header's fourth retraction and in `docs/BIBLIOGRAPHY.md`. -/
theorem result_invariant_transfers {α : Type u} (f : World → α)
    {J : Invariant (Partial α)} (hJ : IConfluent J) :
    IConfluent (S := GSet World) (fun W => J (evalSet f W)) := by
  intro W₁ W₂ h₁ h₂
  show J (evalSet f (W₁ ⊔ W₂))
  rw [evalSet_hom]
  exact hJ _ _ h₁ h₂

/-- **The transfer is inhabited.** "The answer includes `v`" is I-confluent on
results (`Catalog.gset_mem_iconfluent`), so "my candidate worlds justify the
answer `v`" is I-confluent on inputs: a real coordination-free verdict about a
real computation, discharged by the pullback in one line.

This is the positive half of the pair whose negative half is §5 — same
machinery, opposite answer, and the difference is entirely in what the
application asked for. -/
theorem answer_includes_iconfluent {α : Type u} (f : World → α) (v : α) :
    IConfluent (S := GSet World) (fun W => evalSet f W v = true) :=
  result_invariant_transfers f (gset_mem_iconfluent v)

/-! ## §4. THE PHANTOM THEOREM — why worlds and not per-variable sets.

The tempting design is per-variable: each replicated register carries its own
candidate set, and an expression is evaluated in the set monad — bind over the
candidates of `x`, bind over the candidates of `y`, return the operator's
value. It is compositional, it needs no world type, and it is **wrong**.

It is wrong because bind decorrelates: two occurrences of the *same* register
are treated as two independent draws. Ground truth is §2's image over whole
worlds, where one world fixes every register at once, so repeated reads stay
correlated (`evalSet_pair_diagonal`).

Both directions are stated, because both are needed to use the abstraction
honestly:

  * `world_below_monadic` — **sound**: the per-variable answer contains the
    true one. Safe to use as an over-approximation; a "cannot happen" verdict
    from it is trustworthy.
  * `monadic_has_phantoms` — **lossy**: with a concrete `pair(x, x)`, the
    per-variable answer strictly contains the diagonal. The extra elements are
    phantoms: answers no candidate world justifies.
  * `monadic_exact_at_single` — and the gap is exactly correlation, not a
    universal defect: with one candidate world there is nothing to
    decorrelate, and the two semantics coincide. -/

/-- Set-monad bind. Together with `Delta.addDelta` as `pure` this is the
powerset monad; `bindSet_addDelta` below is its left identity law. -/
noncomputable def bindSet {α : Type u} {β : Type v} (S : Partial α) (k : α → Partial β) :
    Partial β :=
  fun b => truth (∃ a, S a = true ∧ k a b = true)

/-- Membership in a bind, unfolded once. -/
theorem mem_bindSet {α : Type u} {β : Type v} (S : Partial α) (k : α → Partial β) (b : β) :
    bindSet S k b = true ↔ ∃ a, S a = true ∧ k a b = true := truth_eq_true

/-- The set monad's **left identity**: binding a singleton is application.
`Delta.addDelta` — the library's minimal delta — is the monad's `pure`, which
is why no new `pure` is defined here. -/
theorem bindSet_addDelta {α β : Type} [DecidableEq α] (a : α)
    (k : α → Partial β) : bindSet (Delta.addDelta a) k = k a := by
  refine gset_ext (fun b => ?_)
  rw [mem_bindSet]
  constructor
  · intro h
    obtain ⟨x, hx, hk⟩ := h
    have : x = a := Ceiling.addDelta_unique hx (by simp [Delta.addDelta])
    subst this
    exact hk
  · intro h
    exact ⟨a, by simp [Delta.addDelta], h⟩

/-- **The per-variable candidate set** for register `r`: what a replica would
carry if it tracked registers independently instead of worlds. It is itself an
image — `evalSet` of the projection — which is why the comparison below is
between two uses of the same machinery rather than between a model and its
rival. -/
noncomputable def candidates (W : GSet World) (r : Reg) : Partial Val :=
  evalSet (fun w => read w r) W

/-- **Per-variable monadic evaluation** of a binary operator over two register
reads: draw a candidate for the first register, draw a candidate for the
second, return the operator's value. The smallest thing that makes the phantom
theorem statable; deliberately not a language (see the boundary). -/
noncomputable def monadicEval₂ {α : Type} [DecidableEq α] (g : Val → Val → α)
    (S T : Partial Val) : Partial α :=
  bindSet S fun a => bindSet T fun b => Delta.addDelta (g a b)

/-- **Soundness: the per-variable reading is an over-approximation.** Every
answer the true (world-indexed) semantics produces is also produced by the
monadic one — stated as `⊑`, i.e. inclusion, in the very order this library is
about. So a per-variable analysis may report answers that cannot occur, but it
never *misses* one: "this value is impossible" is safe to believe. -/
theorem world_below_monadic {α : Type} [DecidableEq α] (g : Val → Val → α)
    (W : GSet World) (r s : Reg) :
    evalSet (fun w => g (read w r) (read w s)) W
      ⊑ monadicEval₂ g (candidates W r) (candidates W s) := by
  refine (gset_leq_iff_subset _ _).mpr (fun a ha => ?_)
  obtain ⟨w, hw, hf⟩ := (mem_evalSet _ W a).mp ha
  refine (mem_bindSet _ _ a).mpr ⟨read w r, ?_, ?_⟩
  · exact (mem_evalSet _ W _).mpr ⟨w, hw, rfl⟩
  · refine (mem_bindSet _ _ a).mpr ⟨read w s, ?_, ?_⟩
    · exact (mem_evalSet _ W _).mpr ⟨w, hw, rfl⟩
    · simp [Delta.addDelta, hf]

/-- **The world semantics keeps repeated reads correlated — the general law.**
Reading register `r` twice in one world reads the same value twice, so every
candidate pair produced by `pair(x, x)` lies on the diagonal, in **every**
candidate-world set. This is correction 2 as a theorem rather than a warning,
and the concrete gap below is one instance of it. -/
theorem evalSet_pair_diagonal (W : GSet World) (r : Reg) (a b : Val)
    (h : evalSet (fun w => (read w r, read w r)) W (a, b) = true) : a = b := by
  obtain ⟨w, _, hf⟩ := (mem_evalSet _ W (a, b)).mp h
  have h1 : read w r = a := congrArg Prod.fst hf
  have h2 : read w r = b := congrArg Prod.snd hf
  rw [← h1, h2]

/-! ### The witness: `pair(x, x)` over two candidate worlds -/

/-- One replica's candidate world: register `0` holds `0`. -/
def w0 : World := [0]

/-- The other's: register `0` holds `1`. -/
def w1 : World := [1]

/-- The merged candidate set: register `0` is `0` or `1`, and nothing says
which. Two replicas, one register, incomparable answers — correction 1's
divergence, in its smallest form. -/
def Wab : GSet World := Delta.addDelta w0 ⊔ Delta.addDelta w1

/-- The program: read register `0` twice and pair the results — `pair(x, x)`,
the whole difficulty in four tokens. -/
def pairxx : World → Val × Val := fun w => (read w 0, read w 0)

/-- The pairing operator the per-variable reading gets handed. -/
def pairOp : Val → Val → Val × Val := fun a b => (a, b)

/-- `0` is a candidate for register `0` — from `w0`. -/
theorem cand_zero : candidates Wab 0 0 = true :=
  (mem_evalSet _ Wab 0).mpr ⟨w0, by decide, rfl⟩

/-- `1` is a candidate for register `0` — from `w1`. -/
theorem cand_one : candidates Wab 0 1 = true :=
  (mem_evalSet _ Wab 1).mpr ⟨w1, by decide, rfl⟩

/-- **The true answer, exactly**: the two-element diagonal
`{(0,0), (1,1)}` — computed by the headline and `evalSet_single`, not asserted.
Pinned as an equation so that nothing below is a claim about an empty set: the
gap the phantom theorem exhibits is between two inhabited answers. -/
theorem true_answer :
    evalSet pairxx Wab = Delta.addDelta (0, 0) ⊔ Delta.addDelta (1, 1) := by
  unfold Wab
  rw [evalSet_hom, evalSet_single, evalSet_single]
  rfl

/-- **The phantoms are present in the per-variable answer**: `(0, 1)` and
`(1, 0)` — register `0` reading one value in its first occurrence and another
in its second, which no single world permits. With `true_answer` and
`world_below_monadic` this pins the per-variable answer as all four pairs
against a two-element truth. -/
theorem phantoms_present :
    monadicEval₂ pairOp (candidates Wab 0) (candidates Wab 0) (0, 1) = true
      ∧ monadicEval₂ pairOp (candidates Wab 0) (candidates Wab 0) (1, 0) = true :=
  ⟨(mem_bindSet _ _ (0, 1)).mpr
      ⟨0, cand_zero,
        (mem_bindSet _ _ (0, 1)).mpr ⟨1, cand_one, by simp [Delta.addDelta, pairOp]⟩⟩,
   (mem_bindSet _ _ (1, 0)).mpr
      ⟨1, cand_one,
        (mem_bindSet _ _ (1, 0)).mpr ⟨0, cand_zero, by simp [Delta.addDelta, pairOp]⟩⟩⟩

/-- **...and absent from the true answer.** No candidate world justifies
`(0, 1)`, by the diagonal law — the truth is `{(0,0), (1,1)}`
(`true_answer`). -/
theorem phantom_absent : evalSet pairxx Wab (0, 1) = false := by
  cases h : evalSet pairxx Wab (0, 1) with
  | false => rfl
  | true => exact absurd (evalSet_pair_diagonal Wab 0 0 1 h) (by decide)

/-- **THE PHANTOM THEOREM. The per-variable abstraction is sound and strictly
lossy** — both directions, on one witness:

  * `⊑` — the true answer is contained in the monadic one (`world_below_monadic`
    instantiated at `r = s = 0`);
  * `≠` — the containment is **strict**, with `(0, 1)` inhabiting the gap.

So per-variable candidate sets are a legitimate over-approximation and are
*not* the semantics. A system that stores candidates per register has already
lost the correlation, and no cleverness downstream recovers it. -/
theorem monadic_has_phantoms :
    evalSet pairxx Wab ⊑ monadicEval₂ pairOp (candidates Wab 0) (candidates Wab 0)
      ∧ evalSet pairxx Wab
          ≠ monadicEval₂ pairOp (candidates Wab 0) (candidates Wab 0) := by
  refine ⟨world_below_monadic pairOp Wab 0 0, fun heq => ?_⟩
  have h : evalSet pairxx Wab (0, 1) = true := by
    rw [heq]; exact phantoms_present.1
  rw [phantom_absent] at h
  exact absurd h (by decide)

/-- **The gap is correlation, and nothing else.** Over a single candidate
world there is nothing to decorrelate, and the two semantics agree exactly.
So the phantom theorem is not "the monad is broken" — it is "the monad forgets
which world you are in", and that is the only thing it forgets. -/
theorem monadic_exact_at_single {α : Type} [DecidableEq α] (g : Val → Val → α)
    (w : World) (r s : Reg) :
    evalSet (fun v => g (read v r) (read v s)) (Delta.addDelta w)
      = monadicEval₂ g (candidates (Delta.addDelta w) r)
          (candidates (Delta.addDelta w) s) := by
  unfold monadicEval₂ candidates
  rw [evalSet_single, evalSet_single, evalSet_single, bindSet_addDelta,
    bindSet_addDelta]

/-! ## §5. Determinacy is a ceiling — what coordination is actually for.

§3 says computing is free. This says *wanting one answer* is not.

"At most one candidate" is `Ceiling.lean`'s uniqueness ceiling wearing a fifth
costume. ⚠ `Ceiling.lean` does **not** say so — its header counts four, and
this is the instance that makes the count stale: `determinacy_not_iconfluent` is
`Ceiling.uniqueness_ceiling` at the constant selector, the same theorem that
refutes "at most one element", "one anchor per id", "one grant per id", "one
DFA target per slot". The new content is the **pullback**: the clash pair
exhibited on the *inputs*, two replicas each holding one candidate world, each
computing a perfectly determinate answer, whose merge is a fork.

Read as a verdict: **demanding a determinate result from a replicated
computation is a coordination requirement**, in exactly Bailis's
necessary-and-sufficient sense — not a quality-of-implementation problem, and
not fixable by a better library. LVars answer it by *blocking* (threshold
reads); we refuse to block; §6 is the price we pay instead. -/

/-- **Determinacy**: this computation has at most one candidate. The invariant
an application asserts when it wants "the" answer rather than "the answers" —
and, verbatim, the hypothesis of `Ceiling.atMostOne_entails_uniqueOn`. -/
def Determinate {α : Type u} (P : Partial α) : Prop :=
  ∀ a b : α, P a = true → P b = true → a = b

/-- ⚠ **Determinacy is not I-confluent.** Two replicas each holding one
candidate merge to a replica holding two. This is `Ceiling.ceiling_atMostOne`
at the `Partial` carrier — the same theorem, not a new one, and it is stated
here so the ceiling's fifth instance is on the record where computations
live. -/
theorem determinacy_not_iconfluent :
    ¬ IConfluent (S := Partial Nat) Determinate :=
  Ceiling.uniqueness_ceiling (fun _ => ())
    (fun s h => Ceiling.atMostOne_entails_uniqueOn s h)
    (e := 0) (e' := 1) rfl (by decide)
    (Ceiling.addDelta_atMostOne 0) (Ceiling.addDelta_atMostOne 1)
    (by decide) (by decide)

/-- The computation the pullback is stated over: read register `0`. -/
def readReg0 : World → Val := fun w => read w 0

/-- Replica A knows its world exactly: register `0` holds `0`. -/
theorem determinate_at_w0 : Determinate (evalSet readReg0 (Delta.addDelta w0)) := by
  rw [evalSet_single]
  exact Ceiling.addDelta_atMostOne _

/-- Replica B likewise, at `1`. -/
theorem determinate_at_w1 : Determinate (evalSet readReg0 (Delta.addDelta w1)) := by
  rw [evalSet_single]
  exact Ceiling.addDelta_atMostOne _

/-- ⚠ **THE COORDINATION REQUIREMENT, on the inputs.** "My computation has a
determinate result" is not I-confluent as an invariant of the *candidate
worlds*: replica A holds one world and computes `0`; replica B holds one world
and computes `1`; each result is determinate; the merge is not.

This is the pullback of `determinacy_not_iconfluent` along a real computation
— `result_invariant_transfers` in the negative direction — and it is the
theorem an application should be shown when it asks for a single answer from
replicated data. By Bailis's Theorem 3.1 (cited, not formalised, per
`Confluence.lean`) no implementation avoids this: the fork is not an artifact
of the merge, it is what the two replicas *know*.

**This is where LVars and Hazel part company, and why the file is named for
Hazel's side.** Kuper–Newton (FHPC'13) recover determinism at exactly this
point by *blocking*: a threshold read waits until the lattice variable crosses
a bound, and the wait is the coordination. That is unavailable to a replica
whose peer is offline for a week, so we refuse to block — and the cost of
refusing is the theorem above: the answer is genuinely plural, and it is the
program's business. Omar et al. (POPL'19) supply the shape for carrying it: an
incomplete evaluation still *means* something, and the indeterminacy is a
value you can render, not a spinner. §6 is what you do when you finally want
one answer anyway. -/
theorem determinate_result_not_iconfluent :
    ¬ IConfluent (S := GSet World) (fun W => Determinate (evalSet readReg0 W)) := by
  intro hconf
  have hmerge : Determinate (evalSet readReg0 (Delta.addDelta w0 ⊔ Delta.addDelta w1)) :=
    hconf _ _ determinate_at_w0 determinate_at_w1
  rw [evalSet_hom, evalSet_single, evalSet_single] at hmerge
  have h01 : (0 : Val) = 1 := hmerge 0 1 (by decide) (by decide)
  exact absurd h01 (by decide)

/-! ## §6. Seal — collapse is explicit, and it is priced.

Correction 3: a multi-candidate result is a final answer, and collapsing it is
a *separate operation with a precondition*. Sealing is the claim "the answer is
`a`" — a determinacy claim (`sealsTo_determinate`) — and §5 just proved
determinacy is not free. What makes a seal safe is therefore not the state but
the **future**: a licence saying nothing that can still arrive will move it.
That plays the role LVars' freeze plays, with the blocking removed: we do not
wait for the licence, we require it before collapsing, and carry the fork until
then. ⚠ *Role, not identity* — the memo's "this **is** LVars' freeze / Era's
arbiter cut / the causal cut" is retracted in the header. A freeze is a local
unilateral act of one runtime; a causal cut is an epistemic statement about
what has been seen; an arbiter cut is a trusted announcement priced in
rollback. All three restrict admissible futures; what each one's evidence is
*worth* differs, and a collapse is only as good as the evidence under it.

`Stable Arriving P` is that licence, abstract in what may still arrive —
abstract precisely because those three discharge it differently.
`stable_inputs_seal_the_result` is the mechanism a real system uses:
**stability of the inputs transports to stability of the result, along the
headline** — finalise what you are computing over and the answer is sealed,
with no argument about the computation at all. `Era.lean`'s arbiter cut is the
intended implementing instance of the input-side licence
(`Era.final_view_immune`: a finalised prefix stops moving); the transport from
Era's event lists into a `Stable` hypothesis here is named in the boundary as
unbuilt, and until it is built the instance is a design intention rather than
a theorem. -/

/-- **A seal**: the claim that `a` is *the* answer — every candidate is `a`. -/
def SealsTo {α : Type u} (P : Partial α) (a : α) : Prop := ∀ b, P b = true → b = a

/-- A seal is a determinacy claim, so §5 prices it: sealing is exactly the
operation that is not I-confluent. -/
theorem sealsTo_determinate {α : Type u} {P : Partial α} {a : α}
    (h : SealsTo P a) : Determinate P :=
  fun x y hx hy => (h x hx).trans (h y hy).symm

/-- **The stability licence.** `P` is stable under `Arriving` when nothing that
may still arrive moves it. Abstract in `Arriving` on purpose: what may still
arrive is a fact about the deployment (an arbiter's cut, a causal cut, a closed
membership), never about the lattice. -/
def Stable {α : Type u} (Arriving : Partial α → Prop) (P : Partial α) : Prop :=
  ∀ Q, Arriving Q → P ⊔ Q = P

/-- **Stability licenses the collapse.** A seal on a stable result survives
everything that can still arrive — which is the whole content of "freeze after
writing", with the blocking removed: the licence is a precondition on the
collapse, not a wait on the read. -/
theorem seal_survives_stable {α : Type u} {Arriving : Partial α → Prop}
    {P : Partial α} {a : α} (hst : Stable Arriving P) (hs : SealsTo P a) :
    ∀ Q, Arriving Q → SealsTo (P ⊔ Q) a := by
  intro Q hQ
  rw [hst Q hQ]
  exact hs

/-- ⚠ **Without the licence the seal is a lie — concretely.** A replica seals
its answer at `0`; a peer arrives holding `1`; the sealed claim is false of the
merged state. This is the same clash pair as §5 (it is the same ceiling), and
it is what "collapse prematurely" costs: not a stale answer, a **wrong** one,
asserted with a confidence the state never justified. -/
theorem unstable_seal_clash :
    ∃ (P Q : Partial Nat) (a : Nat), SealsTo P a ∧ ¬ SealsTo (P ⊔ Q) a := by
  refine ⟨Delta.addDelta 0, Delta.addDelta 1, 0, ?_, ?_⟩
  · intro b hb
    exact Ceiling.addDelta_unique hb (by simp [Delta.addDelta])
  · intro hseal
    have h1 : (1 : Nat) = 0 :=
      hseal 1 (by rw [gset_mem_merge]; simp [Delta.addDelta])
    exact absurd h1 (by decide)

/-- **Stability of the inputs transports to stability of the result** — and it
is the headline that does it, in one rewrite. Finalise the candidate worlds
(the arbiter's cut, the causal cut, the closed membership) and the derived
answer is stable for free, whatever the computation was: no monotonicity
hypothesis, no re-analysis per program.

This is the mechanism §4.2 of the design memo was reaching for when it said
`Era.final_view_immune` "is precisely the licence to collapse a hole that
required stability". ⚠ *Precisely* is retracted (header, retraction 3): a
finalised prefix, a causal cut and an LVars freeze **play the same role here**
— each discharges the `Stable` hypothesis — and they differ in what evidence
buys the restriction, so a collapse licensed by one is not worth what a
collapse licensed by another is. This theorem is agnostic between them by
design, which is the point: the licence lives on the inputs, and whatever
supplies it, the result does not have to re-earn it. -/
theorem stable_inputs_seal_the_result {α : Type u} (f : World → α)
    (W : GSet World) (A : GSet World → Prop) (h : ∀ V, A V → W ⊔ V = W) :
    Stable (fun Q => ∃ V, A V ∧ Q = evalSet f V) (evalSet f W) := by
  intro Q hQ
  obtain ⟨V, hV, hQV⟩ := hQ
  subst hQV
  rw [← evalSet_hom, h V hV]

/-- **The licence is inhabited** — with the *trivial* one, and it is worth
being exact about which: a replica is stable against arrivals that carry no
news (`V ⊑ W`), so having heard everything a peer will ever send is already a
seal. That is a real instance and a weak one. The licence worth having is a
statement about arrivals that have **not** happened yet — an arbiter's epoch
cut (`Era.final_view_immune`), a causal cut (`CausalReach`), a closed
membership — and the transport from any of those into this hypothesis is named
as unbuilt in the boundary. -/
theorem stable_of_subsumed {α : Type u} (f : World → α) (W : GSet World) :
    Stable (fun Q => ∃ V, V ⊑ W ∧ Q = evalSet f V) (evalSet f W) :=
  stable_inputs_seal_the_result f W (fun V => V ⊑ W)
    (fun V hV => by rw [merge_comm]; exact hV)

/-! ## §7. Closure — candidates with provenance, and the computable image.

The observation to state carefully, because the poetic version ("a computation
over a loom yields a little loom") is *almost* a theorem and it matters which
part is which.

What is **true and proved**: a derived value inhabits the same carrier as the
substrate (`Partial α` is `GSet α`), carries the substrate's own `MergeState`
— found by `inferInstance`, so the three CvRDT laws hold on a computed answer
with no new merge proof (`derived_is_a_CRDT`) — converges under
the substrate's own laws in any gossip schedule (`evalSet_fold`), and — when
the computation carries provenance alongside the value — lands *by type* in
`MVRegister.MVReg`, so the multi-value register's frontier machinery applies to
it unchanged (`prov_view_antichain`).

What is **not** claimed: that the derived object is a weave, or that anything
here makes the carried provenance causally meaningful. See the boundary. -/

/-! ### Exact source-and-position attribution -/

/-- One candidate value, the source that justified its world, and one static
position read by the computation.  The types of sources and positions are left
to the language adapter; no causal interpretation is manufactured here. -/
structure Positioned (α : Type u) (Source : Type v) (Position : Type w) where
  value : α
  source : Source
  position : Position
  deriving DecidableEq

/-- Attribute every result candidate to its world's source and to every static
position in the supplied syntax-level read list.  Repeated positions remain
observationally idempotent because the carrier is a grow-only set. -/
noncomputable def evalPositions {α : Type u} {Source : Type v} {Position : Type w}
    (f : World → α) (source : World → Source) (positions : List Position)
    (worlds : GSet World) : GSet (Positioned α Source Position) :=
  fun candidate => truth (∃ world, worlds world = true
    ∧ f world = candidate.value
    ∧ source world = candidate.source
    ∧ candidate.position ∈ positions)

/-- Exact membership in the positioned image. -/
theorem mem_evalPositions {α : Type u} {Source : Type v} {Position : Type w}
    (f : World → α) (source : World → Source) (positions : List Position)
    (worlds : GSet World) (candidate : Positioned α Source Position) :
    evalPositions f source positions worlds candidate = true ↔
      ∃ world, worlds world = true
        ∧ f world = candidate.value
        ∧ source world = candidate.source
        ∧ candidate.position ∈ positions :=
  truth_eq_true

/-- Positioned provenance commutes with candidate-world union. -/
theorem evalPositions_hom {α : Type u} {Source : Type v} {Position : Type w}
    (f : World → α) (source : World → Source) (positions : List Position)
    (left right : GSet World) :
    evalPositions f source positions (left ⊔ right) =
      evalPositions f source positions left ⊔
        evalPositions f source positions right := by
  refine gset_ext (fun candidate => ?_)
  rw [mem_evalPositions, gset_mem_or]
  constructor
  · rintro ⟨world, hworld, hvalue, hsource, hposition⟩
    rcases (gset_mem_or left right world).mp hworld with hleft | hright
    · exact Or.inl ((mem_evalPositions _ _ _ _ _).2
        ⟨world, hleft, hvalue, hsource, hposition⟩)
    · exact Or.inr ((mem_evalPositions _ _ _ _ _).2
        ⟨world, hright, hvalue, hsource, hposition⟩)
  · rintro (hleft | hright)
    · obtain ⟨world, hworld, hvalue, hsource, hposition⟩ :=
        (mem_evalPositions _ _ _ _ _).1 hleft
      exact ⟨world, (gset_mem_or left right world).2 (Or.inl hworld),
        hvalue, hsource, hposition⟩
    · obtain ⟨world, hworld, hvalue, hsource, hposition⟩ :=
        (mem_evalPositions _ _ _ _ _).1 hright
      exact ⟨world, (gset_mem_or left right world).2 (Or.inr hworld),
        hvalue, hsource, hposition⟩

/-- With no declared positions there is no positional attribution, even when
candidate worlds exist. -/
theorem evalPositions_nil {α : Type u} {Source : Type v} {Position : Type w}
    (f : World → α) (source : World → Source) (worlds : GSet World) :
    evalPositions f source ([] : List Position) worlds = fun _ => false := by
  funext candidate
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨_, _, _, _, hposition⟩ :=
    (mem_evalPositions f source [] worlds candidate).1 h
  exact List.not_mem_nil hposition

/-- **Candidates with provenance.** Evaluate a value *and* a tag in the same
world, and the answer is a set of tagged candidates: `MVRegister.Write` is
`value × clock`, so this lands in `MVRegister.MVReg` by type, not by
analogy. -/
noncomputable def evalProv (f : World → Nat) (p : World → Nat × Nat)
    (W : GSet World) : MVRegister.MVReg :=
  evalSet (fun w => (f w, p w)) W

/-- The homomorphism holds for the provenance-carrying evaluation because it
holds for every `f` — nothing was reproved. -/
theorem evalProv_hom (f : World → Nat) (p : World → Nat × Nat)
    (W₁ W₂ : GSet World) :
    evalProv f p (W₁ ⊔ W₂) = evalProv f p W₁ ⊔ evalProv f p W₂ :=
  evalSet_hom _ W₁ W₂

/-- **The MV-register's contract applies to the derived value verbatim**: the
visible candidates of a computed, provenance-carrying answer are an antichain
— what you see is the causal frontier of the answers, exactly as for a
replicated register. `MVRegister.view_antichain` instantiated; the content is
the *type*, and that it needed no new proof. -/
theorem prov_view_antichain (f : World → Nat) (p : World → Nat × Nat)
    (W : GSet World) (x y : MVRegister.Write)
    (hx : MVRegister.InView (evalProv f p W) x)
    (hy : evalProv f p W y = true) : ¬ MVRegister.Dom x.2 y.2 :=
  MVRegister.view_antichain _ x y hx hy

/-! ### The computable image

`evalSet` is classical because a `GSet World` is a predicate over an unbounded
type. A replica does not hold a predicate — it holds a **list** of candidate
worlds. On that shape the image is a `List.map`, computably, and it agrees with
the classical definition on the nose, so every theorem above applies to the
thing an implementation would actually run. -/

/-- The candidate set a replica actually holds: an explicit list of worlds. -/
def ofList (ws : List World) : GSet World := fun w => decide (w ∈ ws)

/-- The computable image: map the computation over the candidate worlds. -/
def evalList {α : Type u} [DecidableEq α] (f : World → α) (ws : List World) :
    Partial α :=
  fun a => decide (a ∈ ws.map f)

/-- **The classical image is the computable one.** For a candidate set held as
a list, `evalSet` — the `Classical.choice`-flavoured definition everything
above is stated over — equals a `List.map` followed by a membership test. The
noncomputability is a fact about the *general* carrier, not a hole under any
implementation. -/
theorem evalSet_ofList {α : Type u} [DecidableEq α] (f : World → α)
    (ws : List World) : evalSet f (ofList ws) = evalList f ws := by
  refine gset_ext (fun a => ?_)
  rw [mem_evalSet]
  constructor
  · intro h
    obtain ⟨w, hw, hf⟩ := h
    exact decide_eq_true (List.mem_map.mpr ⟨w, of_decide_eq_true hw, hf⟩)
  · intro h
    obtain ⟨w, hw, hf⟩ := List.mem_map.mp (of_decide_eq_true h)
    exact ⟨w, decide_eq_true hw, hf⟩

end Uwueave.Holes
