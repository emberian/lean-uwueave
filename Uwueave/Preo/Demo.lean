/-
# Uwueave.Preo.Demo — the acceptance test: does the elaborator rediscover what
`WeaveState.lean` proved by hand?

**Two declarations.** `LoomDoc` (§1–§3) is fragment 1, kept verbatim as a
regression — six fields, six invariants, the same six verdicts by the same
routes. `LoomDoc2` (§3½) is fragment 2: the three surface forms fragment 1
refused, each checked against the hand proof it is supposed to rediscover.

## The fragment-2 result, stated before you read the file

**Three rediscoveries, no disagreement, one narrower statement said out loud.**

  * **the seam row is the hand-written seam, as a value** —
    `LoomDoc2.in_budget.seam = WeaveState.quotaVerdict` by `rfl`;
  * **the cross row is `Spec.refIntVerdict`, as a value** — the FK verdict
    `WeaveState.bookmarksVerdict` is built from, ⚠ at the one-user shape
    because this fragment still has no `per`;
  * **two derives with opposite mergeability verdicts** — an existential read
    `fromResults`, a count `needsEvidence`, plus a third refused outright.

§3½'s header carries the detail and the one gap that is *not* closed
(`WeaveState.weaveDocSeamVerdict`'s two-feature document seam).

## The fragment-1 result (`LoomDoc`), unchanged

**It agrees, and one row it cannot reach at all.**

  * `notes` — `GrowSet Nat`, invariant `notes 0 = true`. Derived FREE.
    `WeaveState.nodesVerdict` proves the same invariant over the same carrier by
    hand, FREE. Same statement, same answer, *different citation*: the hand
    proof is `Catalog.gset_mem_iconfluent`; the elaborator reaches it through
    `classify`'s monotone-closure route (`gset_monotone_iconfluent`). Two routes
    to one fact, which is what a `RuleSet` is supposed to look like
    (`PREOSCRIPTING.md` §6).
  * `pin` — `Slot (Fin 3)`, the uniqueness ceiling. Derived ESCALATES **with the
    witness pair `{0}` / `{1}`** — the *same two singletons* `Spec.atMostOneClash`
    and `WeaveState.pinA`/`pinB` carry by hand. §2 checks that as membership
    bits, by `rfl`, rather than by looking at it.
  * `wide_pin` — `Slot Nat`, the identical ceiling at `WeaveState`'s own id type.
    **UNRESOLVED.** `∀ m n : Nat, …` is not decidable, so no route applies, and
    the elaborator says so and quotes `classify`'s diagnosis instead of guessing.
    `Catalog.gset_atMostOne_not_iconfluent` is exactly the theorem that "must
    stay hand-proved" per `Tactics.Core`'s header, and this row is that sentence
    happening. Two `Slot` fields sit side by side in the declaration on purpose:
    the fragment boundary is a property of the *index type*, not of the shape.
  * `budget` — `Escrow Bool`. No route (the value lattice is `Nat`, which is
    infinite and does not select pointwise), so the author supplies
    `Catalog.escrow_local_bound_iconfluent`. Reported `supplied`, never
    `derived`.
  * `height`, `title` — `Counter` and `LWW`. FREE for *every* invariant by the
    selection route, on infinite carriers, which is `Catalog.selection_iconfluent`
    doing exactly what it says.

## The two reach gaps `LoomDoc` had — ⚠ both CLOSED in §3½, kept here as the
## before picture

There was never a row where the elaborator and the hand proof reached
*opposite* verdicts. What they differed on was **reach**, twice:

`WeaveState.quotaVerdict` is a `SegVerdict` — globally refuted, free within an
allocation. Fragment 1 could not state it at all: one verdict type, no seam. So
`LoomDoc`'s escrow row below is the *other* budget story (`Catalog` §4's
rephrasing, free outright), and calling it "the seam" would have been the lie.
§3½'s `LoomDoc2.in_budget` is the seam, and it is `WeaveState.quotaVerdict`
itself.

`WeaveState.bookmarksVerdict` (bookmarks ⊆ nodes) is a `Verdict.cross`, and §3
below shows fragment 1 refusing that shape by name rather than approximating
it. §3½'s `LoomDoc2.fk` classifies it, against the joint merge.

Both quoted refusals in §3 are therefore **historical**: they are what the
elaborator said before fragment 2, and the two that are now handled are marked
there. Keeping them is the point — a fragment boundary that moved should be
readable as having moved.

## What is scaffolding here and what is real

REAL: the emitted `Verdict`, `SegVerdict` and `Fourth.Correct` terms and the
theorems §2/§3½ derive from them; the `.onState` / `.seamOnState` lifts (they
typecheck only if the row's *computed* answer was `free`, resp. only if the
plant's two equations hold); the composed document-scale theorems `loomDocFree`
and `loomDoc2Free`; the refusals.

SCAFFOLDING: the report *table* is a pretty-printer over an environment
extension — it re-reads every verdict from its constant, so it cannot drift, but
it is display code and nothing depends on it. The `Fin 3` id type is a toy
parameter chosen to sit inside the decidable fragment, exactly as the tree's
other miniatures are (two users, `Bool`; budget 10).
-/
import Uwueave.Preo.Elab
import Uwueave.WeaveState

namespace Uwueave.Preo.Demo

open Uwueave Uwueave.Catalog Uwueave.Spec Uwueave.Preo

/-! ## §1. The declaration

A loom document, in the surface of `PREOSCRIPTING.md` §7 minus everything the
fragment does not have. Read it as a user would: six fields with kinds, six
invariants in ordinary Lean, one of which carries its own evidence. -/

preo LoomDoc where
  field notes    : GrowSet Nat
  field pin      : Slot (Fin 3)
  field wide_pin : Slot Nat
  field budget   : Escrow Bool
  field height   : Counter
  field title    : LWW

  invariant has_genesis : notes 0 = true
  invariant one_pin     : ∀ m n, pin m = true → pin n = true → m = n
  invariant one_wide    : ∀ m n, wide_pin m = true → wide_pin n = true → m = n
  invariant in_budget   : ∀ i, budget i ≤ 5
    := .free (Uwueave.Catalog.escrow_local_bound_iconfluent (fun _ => 5))
  invariant grown       : 1 ≤ height
  invariant titled      : 1 ≤ title.ts

#preo_report LoomDoc

/-! ## §2. The acceptance checks

Every line below is a term or an `rfl`, and every one of them is *about the
constants the elaborator emitted* — not about a table, a log line, or a
self-report. -/

/-! ### 2.1 The answers, read off the emitted verdicts -/

/-- `notes`: FREE, derived. -/
example : LoomDoc.has_genesis.verdict.isFree = true := rfl
/-- `pin`: ESCALATES, derived by exhaustive decision. -/
example : LoomDoc.one_pin.verdict.isFree = false := rfl
/-- `budget`: FREE, supplied. -/
example : LoomDoc.in_budget.verdict.isFree = true := rfl
/-- `height`: FREE, derived by selection over an infinite carrier. -/
example : LoomDoc.grown.verdict.isFree = true := rfl
/-- `title`: same route, same answer. -/
example : LoomDoc.titled.verdict.isFree = true := rfl

/-! ### 2.2 Against the hand-proved rows of `WeaveState.lean`

`WeaveState` classified this document by hand: `nodesVerdict` FREE,
`pinsVerdict` a clash carrying `{0}`/`{1}`. These are the comparisons. -/

/-- **The node row agrees.** `WeaveState.nodesVerdict` is `gsetMemFree 0` —
`Catalog.gset_mem_iconfluent`, by hand, over `GSet Nat`. `LoomDoc.has_genesis`
is the same invariant over the same carrier, classified by the elaborator. The
two `isFree`s are equal because both are `true`, and both terms carry a real
`IConfluent` proof; the *proofs* are different, and that is the interesting
part. -/
example : LoomDoc.has_genesis.verdict.isFree = WeaveState.nodesVerdict.isFree := rfl

/-- **The pin row agrees.** `WeaveState.pinsVerdict` is `Spec.atMostOneClash`,
the ceiling refuted by hand at `GSet Nat`. `LoomDoc.one_pin` is the same
invariant at `GSet (Fin 3)`, refuted by `classifyFinite`. -/
example : LoomDoc.one_pin.verdict.isFree = WeaveState.pinsVerdict.isFree := rfl

/-- ⚠ **And the witnesses are the same two states.** The elaborator searched
the whole 8-state enumeration of `Fin 3 → Bool` and came back with the pair
`{0}` / `{1}` — as membership bits, `[true,false,false]` and
`[false,true,false]`. It was not told to; nothing about `Slot` hands it a
canned answer. -/
example : witnessBits LoomDoc.one_pin.verdict
    = some ([true, false, false], [false, true, false]) := rfl

/-- …and this is the hand-written pair (`Spec.atMostOneClash`'s `n == 0` and
`n == 1`, `WeaveState.pinA`/`pinB`), read at the same id type in the same
notation. Compare the two lines: the derived counterexample IS the one the
library has been carrying by hand since `Catalog.gset_atMostOne_not_iconfluent`. -/
example : (bits (fun n : Fin 3 => n == 0), bits (fun n : Fin 3 => n == 1))
    = ([true, false, false], [false, true, false]) := rfl

/-! ### 2.3 The rows as theorems

A row is only worth printing if it is a term. These are the two readings a
loom author actually wants, taken straight off the emitted verdicts. -/

/-- **The pin ceiling escalates** — the refutation, as a theorem, from the
elaborator's own verdict term. No hand witness appears in this proof. -/
theorem one_pin_escalates : ¬ IConfluent LoomDoc.one_pin :=
  Tactics.not_iconfluent_of_isFree_false (v := LoomDoc.one_pin.verdict) rfl

/-- **The free rows compose at document scale.** Every conjunct is an
elaborator-emitted `.onState` theorem — each one `proj_iconfluent` applied to a
`rfl` merge-homomorphism and a verdict that *computed* `free` — glued with
`and_iconfluent`. This is `WeaveState.core_iconfluent`'s shape with the leaves
derived instead of written: edits to the note set, spends inside quota, a
rising height and a retitle all sync in any order, forever, on a document that
also carries a ceiling that does not. -/
theorem loomDocFree : IConfluent (S := LoomDoc.State) (fun s =>
    LoomDoc.has_genesis (LoomDoc.notes s)
    ∧ (LoomDoc.in_budget (LoomDoc.budget s)
      ∧ (LoomDoc.grown (LoomDoc.height s) ∧ LoomDoc.titled (LoomDoc.title s)))) :=
  and_iconfluent LoomDoc.has_genesis.onState
    (and_iconfluent LoomDoc.in_budget.onState
      (and_iconfluent LoomDoc.grown.onState LoomDoc.titled.onState))

/-- The unresolved row is *not* one of them, and this is the point of the
`Obligation` type: `LoomDoc.one_wide.obligation` exists, prints, and names its
own remaining work — and there is no function anywhere that turns it into a
verdict. Discharging it means writing `:= Uwueave.Spec.atMostOneClash` on the
declaration (which typechecks — the invariant is that theorem's, verbatim) or
proving it. Until someone does, the table says UNRESOLVED. -/
example : LoomDoc.one_wide.obligation.onField = "wide_pin" := rfl

/-! ## §3. What it refuses

Each of these is a real failure, reproduced by uncommenting; the messages are
what the elaborator actually printed when they were run, quoted verbatim.
They are here rather than in a test harness because a refusal is part of the
surface: the fragment boundary is only honest if hitting it is loud.

⚠ **The first entry is HISTORICAL — fragment 2 handles it.** It is kept because
a boundary that moved should be readable as having moved, and because the
sentence it got wrong is instructive: "no per-field lift produces one and none
can" was true, and the conclusion drawn from it ("so the surface cannot have
it") did not follow. What was missing was not a lift but a *rule* that reaches
the joint-merge theorem — `LoomDoc2.fk` in §3½ is that rule firing.

```lean
-- FRAGMENT 1 ONLY. In fragment 2 this elaborates: `fk` is a cross row,
-- classified against the product `GSet (Fin 3) × Slot (Fin 3)`.
preo Bad where
  field notes : GrowSet (Fin 3)
  field pin : Slot (Fin 3)
  invariant fk : ∀ m, pin m = true → notes m = true
```
> preo: invariant `fk` mentions 2 fields (pin, notes) — that is a CROSS-FIELD
> invariant, and it is outside this fragment. …

The rest are live. Three or more fields is still refused, and the reason is
narrower and truer than fragment 1's was — `Spec.Verdict.cross` is over `A × B`
and there is no ternary lift in the tree:

```lean
preo Bad3 where
  field a : GrowSet Nat
  field b : GrowSet Nat
  field c : GrowSet Nat
  invariant tri : ∀ n, a n = true → b n = true → c n = true
```
> preo: invariant `tri` mentions 3 fields (a, b, c). The cross-field machinery
> is BINARY — `Spec.Verdict.cross` classifies a relation over `A × B`, and no
> ternary lift exists in the tree. Split it, or earn the ternary verdict by hand
> against the joint merge.

```lean
preo BadD where
  field a : GrowSet Nat
  field b : GrowSet Nat
  derive both : Prop = (∃ n, a n = true) ∧ (∃ n, b n = true)
```
> preo: `derive both` reads 2 field(s) (a, b) — this fragment classifies a
> computation over EXACTLY ONE field, because the transport that carries its
> answer to the declared state (`Preo.mergeability_comp`) is along one
> projection. …

```lean
preo Bad where
  field seq : RGA Nat
  invariant x : seq 0 = true
```
> preo: unknown field kind `RGA`. The fragment has six: `GrowSet α` …

```lean
preo Bad where
  field notes : GrowSet (Fin 3)
  invariant x : 1 ≤ 2
```
> preo: invariant `x` mentions no field of `Bad` — there is no carrier to
> classify it over. Fields are: notes.

```lean
preo Bad where
  field notes : GrowSet Nat
  invariant smuggled : notes 0 = true ∧ notes 1 = false := sorry
```
> preo: the verdict `Bad.smuggled.verdict` depends on sorryAx — outside the
> axiom floor `propext · Classical.choice · Quot.sound` that `#audit_floor`
> holds the whole tree to. … No row is recorded.

⚠ And the same guard now covers the **seam** and the **mergeability** facets,
which is the half fragment 2 had to add rather than inherit: a `sorry`-backed
`SegVerdict` would print `FREE·seg` and a `sorry`-backed `Fourth.Correct` would
print `fromResults`, both indistinguishable from the real thing on the page.

```lean
preo BadE where
  field flags : GrowSet Bool
  derive tally : Nat = (if flags false then 1 else 0) + (if flags true then 1 else 0)
    := sorry
```
> preo: the mergeability facet `BadE.tally.merge` depends on sorryAx — … No row
> is recorded.

That last one is the guard that makes the *supplied* route safe: author-written
evidence is checked against the tree's floor before a row exists, because a
`sorry`-backed `Verdict` prints exactly like a real one — an unproved lemma
emits the same table as a proved one, and no amount of reading the table can
tell.
-/

/-! # ═══ FRAGMENT 2 ═══

## §3½. `preo LoomDoc2` — the acceptance test for the three new surface forms

§1's `LoomDoc` is fragment 1, kept verbatim as a regression: same six rows,
same six verdicts, same routes. Everything below is the fragment the reviewer
prescribed, and every claim in this header is a `rfl` further down.

**Read the three results before the code.**

  * **(a) The seam row RE-DISCOVERS `WeaveState.quotaVerdict` — as the same
    value.** `LoomDoc2.in_budget.seam = WeaveState.quotaVerdict` is `rfl`: same
    projection `Prod.fst`, same two allocations, same segmentation proof. The
    elaborator was not handed it — the seam registry's one rule
    (`Preo.budgetSeam B`) is parametric in the budget, and it unified `B := 10`
    off the invariant the author wrote. Fragment 1's report called this row
    *inexpressible*; §10 of `PREOSCRIPTING.md` said so in the status table.
    That row is now closed.
  * **(b) The cross row RE-DISCOVERS the bookmarks verdict.** `LoomDoc2.fk` is
    `bookmarks ⊆ nodes` over two fields, and it comes out `FREE` through
    `Spec.pointsAtExisting_iconfluent` against the **joint** merge — the same
    theorem `WeaveState.bookmarksVerdict` carries. The emitted verdict is
    literally `Spec.refIntVerdict` (`rfl`). ⚠ One honest difference, stated
    rather than glossed: `WeaveState.bookmarksVerdict` is the *keyed* form
    (`∀ u, PointsAtExisting ns (bm u)`, through `keyed_cross_iconfluent`),
    because that document has per-user bookmarks. This fragment has no `per`,
    so `LoomDoc2` declares the one-user shape. Same theorem underneath, smaller
    statement, and the report does not pretend otherwise.
  * **(c) Two derives, OPPOSITE mergeability verdicts.** `anyone` (an
    existential read) is `fromResults`; `tally` (a count) is `needsEvidence`,
    and it got there through `JoinHom.no_count_merge_without_provenance` — an
    impossibility over *every* candidate combiner, not a complaint about one.
    A third derive, `top`, is UNRESOLVED, because the registry has no rule for
    it and inventing `fromResults` is precisely the error `JoinHom.lean` §4
    exists to refute.

**No row disagrees with its hand proof.** Where a rediscovery is *narrower*
than the hand result — (b)'s keyed-vs-plain — it is said above and again at the
row.

⚠ And one thing this file does NOT show, because it is not true: the derived
seam does not make `WeaveState.weaveDocSeamVerdict` derivable. That object
segments a **whole eight-field document** over `(pins, allocation)` — two
coordination features at once — and the registry has one single-field rule.
`LoomDoc2.in_budget.seamOnState` is the document-scale seam of *one* field.
The gap is a missing rule (`SeamAlgebra.prodSeams` composing two seam facets),
not a missing theorem. -/

preo LoomDoc2 where
  field nodes     : GrowSet Nat
  field bookmarks : GrowSet Nat
  field flags     : GrowSet Bool
  field quota     : Quota Bool
  field height    : Counter

  invariant in_budget : Uwueave.Segmented.BudgetInv 10 quota
  invariant fk        : ∀ n, bookmarks n = true → nodes n = true
  invariant genesis   : nodes 0 = true
  invariant grown     : 1 ≤ height
    := .free (Uwueave.Catalog.selection_iconfluent
        Uwueave.Tactics.SelectionMerge.selects _)

  derive anyone : Prop = ∃ a, nodes a = true
  derive tally  : Nat  = (if flags false then 1 else 0) + (if flags true then 1 else 0)
  derive top    : Nat  = height

#preo_report LoomDoc2

/-! ### 3½.1 (a) The seam facet, checked against the hand answer

`WeaveState.quotaVerdict` is the library's most interesting single answer:
globally refuted, free within an allocation. These lines are the elaborator's
own facet compared against it. -/

/-- ⚠ **The derived seam IS the hand-written one.** Not "agrees with" — the
same value: `Spec.budgetSegVerdict`, which `WeaveState.quotaVerdict` is defined
to be. Every field matches: the projection (`Prod.fst`), the two allocations
(10+0 and 0+10, both fully spent), and the segmentation proof
(`Segmented.budget_segmented 10`). The elaborator reached it by unifying
`Preo.budgetSeam ?B` against the invariant the author wrote, which fixed
`?B := 10`; nothing about the field kind `Quota` hands it a canned answer. -/
example : LoomDoc2.in_budget.seam = WeaveState.quotaVerdict := rfl

/-- The row's accumulated answer: ESCALATES. Reduced out of the
`Classification`, not out of any one verdict. -/
example : LoomDoc2.in_budget.classification.answer = some false := rfl

/-- ⚠ **codex's correction, on this row's own facets.** The seam does not
*compete* with the global column — it forces it. `Preo.seam_forces_clash`
applied to the elaborator's seam and the elaborator's verdict, with no
appeal to how either was produced. -/
example : LoomDoc2.in_budget.verdict.isFree = false :=
  seam_forces_clash LoomDoc2.in_budget.seam _

/-- The escalation half, as a theorem read off the accumulated classification.
This is `Segmented.budget_not_iconfluent` rediscovered. -/
example : ¬ IConfluent LoomDoc2.in_budget :=
  Classification.answer_false LoomDoc2.in_budget.classification rfl

/-- The free-running half, usable as-is: same-allocation replicas merge
legally — **spends never wait**. This is what fragment 1 could not say. -/
example (a b : Quota Bool) (hσ : a.1 = b.1)
    (ha : LoomDoc2.in_budget a) (hb : LoomDoc2.in_budget b) :
    LoomDoc2.in_budget (a ⊔ b) :=
  LoomDoc2.in_budget.seam.freeWithinSeam hσ ha hb

/-- The closure half: a same-allocation sync cannot re-allocate behind your
back. -/
example (a b : Quota Bool) (hσ : a.1 = b.1)
    (ha : LoomDoc2.in_budget a) (hb : LoomDoc2.in_budget b) :
    (a ⊔ b).1 = a.1 :=
  LoomDoc2.in_budget.seam.staysInSeam hσ ha hb

/-- ⚠ **And the seam at WHOLE-DOCUMENT scale** — the emitted
`.seamOnState`, through `Preo.seamAlong`. Fragment 1's report said a clash
could not be transported because "transporting a clash needs a legal value for
every other field … which this elaborator cannot synthesize". It can now: the
section `LoomDoc2.quota.plant` is that value, and its two equations are `rfl`.
Reading: on the whole five-field document, edits and spends sync freely; the
only meeting is a re-division of the budget. -/
example (a b : LoomDoc2.State)
    (hσ : LoomDoc2.in_budget.seamOnState.σ a = LoomDoc2.in_budget.seamOnState.σ b)
    (ha : LoomDoc2.in_budget (LoomDoc2.quota a))
    (hb : LoomDoc2.in_budget (LoomDoc2.quota b)) :
    LoomDoc2.in_budget (LoomDoc2.quota (a ⊔ b)) :=
  LoomDoc2.in_budget.seamOnState.freeWithinSeam hσ ha hb

/-- …and the document-scale seam still refutes global freedom, from its own
planted replicas. -/
example : ¬ IConfluent (S := LoomDoc2.State)
    (fun d => LoomDoc2.in_budget (LoomDoc2.quota d)) :=
  LoomDoc2.in_budget.seamOnState.escalatesGlobally

/-! ### 3½.2 (b) The cross-field row, checked against `WeaveState` -/

/-- **The elaborator's cross verdict IS `Spec.refIntVerdict`.** Same
constructor, same theorem (`pointsAtExisting_iconfluent`), earned against the
JOINT merge of `nodes × bookmarks` — no per-field lift produced it and none
could (`Catalog.lww_cross_field_not_iconfluent` is why). Fragment 1 refused
this shape by name. -/
example : LoomDoc2.fk.verdict = Spec.refIntVerdict := rfl

/-- Agreement with the document `WeaveState` classified by hand. ⚠ The
statements are not identical and the header says so: `bookmarksVerdict` is the
per-user family (`keyed_cross_iconfluent` over `∀ u`), this row is the one-user
shape, because `preo` has no `per`. What is compared here is the answer. -/
example : LoomDoc2.fk.verdict.isFree = WeaveState.bookmarksVerdict.isFree := rfl

/-- The FREE side of the accumulated answer, cashed: `Classification.answer_true`
turns the row's `some true` back into an `IConfluent` proof. (Its twin
`answer_false` did the same for the seam row. Between them: a classification
cannot lie in either direction, and neither reading inspects *how* the answer
was reached.) -/
example : IConfluent LoomDoc2.fk :=
  Classification.answer_true LoomDoc2.fk.classification rfl

/-- And the cross row at document scale — `proj_iconfluent` along the *pair*
projection `fun s => (nodes s, bookmarks s)`, whose merge homomorphism is `rfl`
because the product merge is componentwise. A bookmark never dangles, on any
replica, after any merge, on the whole five-field document. -/
example : IConfluent (S := LoomDoc2.State)
    (fun s => LoomDoc2.fk (LoomDoc2.nodes s, LoomDoc2.bookmarks s)) :=
  LoomDoc2.fk.onState

/-! ### 3½.3 (c) The two derives, and the third that is refused -/

/-- **An existential read ships as a summary.** `JoinHom.exists_joinHom`: ∃
distributes over ∨, so folding shipped summaries agrees with recomputing from
merged evidence (`summaryFold_iff_joinHom`). -/
example : LoomDoc2.anyone.classification.mergeAnswer
    = some JoinHom.Fourth.fromResults := rfl

/-- ⚠ **A count must replay the evidence.** The opposite answer, on the same
declaration, one field over. -/
example : LoomDoc2.tally.classification.mergeAnswer
    = some JoinHom.Fourth.needsEvidence := rfl

/-- The `fromResults` badge, cashed: a real combiner exists, at the **declared
document's** scale (the field-scale theorem carried along
`Preo.mergeability_comp`, which for this direction needs only that the
projection is a join homomorphism). -/
example : IncrementallyMergeable LoomDoc2.anyone :=
  Classification.mergeAnswer_correct LoomDoc2.anyone.classification
    (a := JoinHom.Fourth.fromResults) rfl

/-- ⚠ **The `needsEvidence` badge, cashed as an impossibility.** There is no
binary combiner on counts — for *every* candidate, `LoomDoc2.flags`'s two
one-element replicas present the same pair of counts with different merged
counts (`JoinHom.no_count_merge_without_provenance`). This is the direction
that needed the extra hypothesis: the transport to document scale is only sound
because `LoomDoc2.flags.surj` says every field value is reachable, and
`Preo.not_incrementallyMergeable_comp` consumes exactly that. -/
example : ¬ IncrementallyMergeable LoomDoc2.tally :=
  Classification.mergeAnswer_correct LoomDoc2.tally.classification
    (a := JoinHom.Fourth.needsEvidence) rfl

/-- The two answers are not merely different labels: they are exclusive, and
one row of this declaration inhabits each side. -/
example : LoomDoc2.anyone.classification.mergeAnswer
    ≠ LoomDoc2.tally.classification.mergeAnswer := by decide

/-- ⚠ **And the third derive is UNRESOLVED, loudly.** `top = height` is the
identity on a `Counter`; it is *obviously* a join homomorphism and the registry
still has no rule that produces one, so the elaborator says so instead of
guessing. Note which way it fails safe: no answer is **not** `fromResults`, and
shipping a summary on the strength of an unclassified derive is the exact error
`JoinHom.lean` §4 refutes. There is no `Obligation.toFourth` anywhere. -/
example : LoomDoc2.top.classification.mergeAnswer = none := rfl
example : LoomDoc2.top.obligation.onField = "height" := rfl

/-! And the discharge is live rather than decorative — the same computation,
with the author supplying the answer. `:= <proof>` on a `derive` is elaborated
at `JoinHom.Fourth.Correct <the computation> <the answer>` and kernel-checked
against the tree's floor before a row exists (§3's `BadE`), so there is no way
to write the badge without writing the proof. -/
preo Discharged where
  field height : Counter

  derive top : Nat = height
    := Uwueave.joinHom_incrementallyMergeable (f := fun n : Nat => n) (fun _ _ => rfl)

/-- The obligation `LoomDoc2.top` carries, closed one declaration over. -/
example : Discharged.top.classification.mergeAnswer
    = some JoinHom.Fourth.fromResults := rfl

/-! ### 3½.4 The accumulation itself, and route-order invariance

`grown` is the row where two rules both fire: the author supplied evidence
*and* `Counter`'s carrier is a selection lattice. Fragment 1 would have taken
the first and discarded the second. -/

/-- Two global facets on one row. -/
example : LoomDoc2.grown.classification.global.length = 2 := rfl

/-- ⚠ **And they cannot disagree** — not by policy, by type. `verdict_agree` is
applied here to two verdicts the elaborator built by *different routes*
(author-supplied evidence, and `Catalog.selection_iconfluent`), with no appeal
to how either was produced. -/
example : LoomDoc2.grown.verdict.isFree = LoomDoc2.grown.verdict₂.isFree :=
  verdict_agree _ _

/-- ⚠ **ROUTE-ORDER INVARIANCE, on this declaration's own facets.** The two
registries below differ only in the order the rules ran; `run_answer_of_perm`
says the certified answer is the same, and the proof bottoms out in
`verdict_agree` rather than in bookkeeping. This is the theorem that licenses
the elaborator's one remaining optimisation — skipping the expensive `verdict`
search when a cheap route already answered. -/
example :
    (run (f := fun _ : Nat => ())
        [some (.global LoomDoc2.grown.verdict),
         some (.global LoomDoc2.grown.verdict₂)]).answer
      = (run (f := fun _ : Nat => ())
          [some (.global LoomDoc2.grown.verdict₂),
           some (.global LoomDoc2.grown.verdict)]).answer :=
  run_answer_of_perm (List.Perm.swap _ _ _)

/-- The same for a registry that also carries the *seam* rule: wherever the
seam sits in the list, the answer is ESCALATES. -/
example (rs : List (Rule LoomDoc2.in_budget (fun _ : Quota Bool => ())))
    (h : (some (.seam ⟨Bool → Nat, LoomDoc2.in_budget.seam, "spends free"⟩) :
            Rule LoomDoc2.in_budget (fun _ : Quota Bool => ())) ∈ rs) :
    (run rs).answer = some false :=
  run_answer_of_seam rs _ h

/-! ### 3½.5 The document, composed

The free rows of `LoomDoc2` at document scale, glued — with the cross row's
conjunct earned against the joint merge and the seam row deliberately absent
(it escalates; its refined truth is `in_budget.seamOnState`). -/

/-- Genesis present, referential integrity, and a risen height — all
coordination-free on the whole document, every leaf an elaborator-emitted
`.onState`. -/
theorem loomDoc2Free : IConfluent (S := LoomDoc2.State) (fun s =>
    LoomDoc2.genesis (LoomDoc2.nodes s)
    ∧ (LoomDoc2.fk (LoomDoc2.nodes s, LoomDoc2.bookmarks s)
      ∧ LoomDoc2.grown (LoomDoc2.height s))) :=
  and_iconfluent LoomDoc2.genesis.onState
    (and_iconfluent LoomDoc2.fk.onState LoomDoc2.grown.onState)

/-! ## §4. The keywords are not stolen

`field` and `invariant` are non-reserved keywords (`&"field"`). If they had
been ordinary tokens, importing this module would have broken every downstream
file that used either word as a name. This is the check, and it is a real
hazard rather than a hypothetical one — the first draft of the grammar reserved
them. -/

/-- An ordinary definition named `field`. -/
def field : Nat := 1
/-- An ordinary definition named `invariant`. -/
def invariant : Nat := 2
example : field + invariant = 3 := rfl

/-! ## §5. The floor, until the root carries this module

`Uwueave.Audit`'s `#audit_floor` walks the whole `Uwueave` namespace, but it
can only see modules it imports, and it does not import `Uwueave.Preo.*` yet
(the root and the audit file belong to a different lane). Until they do, this
is that gate scoped to `Uwueave.Preo` — including the constants the elaborator
*generated* above, which is the half a reader would most want checked.

⚠ **Delete this section** the moment `Uwueave.Preo.Demo` appears in
`Uwueave.lean` and in `Audit.lean`'s import list; two gates for one property is
how one of them rots. -/

open Lean Elab Command in
/-- `#audit_floor` (`Uwueave.Audit`) restricted to `Uwueave.Preo`. Same floor,
same vacuity tripwire, same reason: `sorry` compiles to `sorryAx` and
`native_decide` to `Lean.ofReduceBool`, and a `Verdict` built from either
prints like any other. -/
elab "#preo_floor" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets := env.constants.toList.filterMap fun (n, _) =>
    if (`Uwueave.Preo).isPrefixOf n then some n else none
  let mut blamed : Array String := #[]
  for n in targets do
    for ax in ← collectAxioms n do
      unless allowed.contains ax do
        if blamed.size < 20 then blamed := blamed.push s!"{n} ← {ax}"
  unless blamed.isEmpty do
    throwError "preo floor violated — first offenders: {blamed.toList}"
  if targets.length < 40 then
    throwError "preo floor vacuity tripwire: only {targets.length} constants under \
      `Uwueave.Preo` — the walk is not seeing the module"
  logInfo m!"-- (retired at wire-up: the tree-wide #audit_floor now covers Uwueave.Preo)
#preo_floor: {targets.length} constants under `Uwueave.Preo`, all within the floor"

-- (retired at wire-up: the tree-wide #audit_floor now covers Uwueave.Preo)
-- retired at wire-up: the tree-wide #audit_floor now covers Uwueave.Preo
-- #preo_floor

end Uwueave.Preo.Demo
