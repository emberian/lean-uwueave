/-
# Uwueave.Preo.Demo — the acceptance test: does the elaborator rediscover what
`WeaveState.lean` proved by hand?

**Seven principal declarations, plus the `Discharged` evidence fixture.**
`LoomDoc` (§1–§3) retains fragment 1's six fields and
six invariants as a regression, while the formerly unresolved `Slot Nat` row
now reaches the conservative pins self seam. `LoomDoc2` (§3½) is fragment 2:
the three surface forms fragment 1 refused, each checked against the hand proof
it is supposed to rediscover.
`TwinQuota` (§3¾) is the document-seam acceptance: two independently budgeted
fields become one derived verdict over their pair of allocation seams.
`NestedSurface` (§3⅘) exercises the same registry through eight right-nested
fields and absorbs six legal coordination-free rows.
`KeyedDoc` (§3⅝) closes the keyed cross-field gap and rediscovers the hand
bookmarks verdict as a value.
`GroupedCarrierSurface` (§3⅞a) uses the explicit-seed custom carrier form to
recover `WeaveState.WeaveDoc`'s grouped carrier exactly.
`SemanticSurface` (§4) exercises retained-world futures and proof-carrying
protocol sessions; the standalone certificate and budget commands then consume
those exact generated meanings without manufacturing a new judgement.

## The fragment-2 result, stated before you read the file

**Three rediscoveries, no disagreement, one narrower statement said out loud.**

  * **the seam row is the hand-written seam, as a value** —
    `LoomDoc2.in_budget.seam = WeaveState.quotaVerdict` by `rfl`;
  * **the cross row is `Spec.refIntVerdict`, as a value** — the FK verdict
    `WeaveState.bookmarksVerdict` is built from, ⚠ at the one-user shape kept
    by `LoomDoc2`; §3⅝ exercises the full keyed shape;
  * **two derives with opposite mergeability verdicts** — an existential read
    `fromResults`, a count `needsEvidence`, plus a third refused outright.

§3½'s header carries the detail. §3¾ closes its two-feature surface
composition gap; §3⅞ then reconstructs `WeaveState.weaveDocSeamVerdict` as a
value at the general combinator layer and states the remaining surface gap.

## The fragment-1 declaration (`LoomDoc`), with its pin gap closed

**It agrees, including the formerly unreachable unbounded pin row.**

  * `notes` — `GrowSet Nat`, invariant `notes 0 = true`. Derived FREE.
    `WeaveState.nodesVerdict` proves the same invariant over the same carrier by
    hand, FREE. Same statement, same answer, *different citation*: the hand
    proof is `Catalog.gset_mem_iconfluent`; the elaborator reaches it through
    `classify`'s monotone-closure route (`gset_monotone_iconfluent`). Two routes
    to one fact, which is what a `RuleSet` is supposed to look like
    (`PREOSCRIPTING.md` §6).
  * `pin` — `Slot (Fin 3)`, the uniqueness ceiling. Derived ESCALATES **with the
    witness pair `{0}` / `{1}`** — the *same two singletons* `Spec.atMostOneClash`
    and `WeaveState.pinA`/`pinB` carry by hand. Its certified finite clash also
    receives the conservative self seam. §2 checks the witness as membership
    bits, by `rfl`, rather than by looking at it.
  * `wide_pin` — `Slot Nat`, the identical ceiling at `WeaveState`'s own id type.
    Binary search still cannot decide `∀ m n : Nat, …`, but the pin seam rule
    recognizes the exact `Spec.atMostOneClash` shape and packages its existing
    repro with `SegVerdict.selfSeam`. The result is ESCALATES plus "coordinate
    whenever the pin set changes", not a guessed finite decision.
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

/-- **The formerly unresolved unbounded row is the hand pins seam.** Search did
not become magically decidable: the registry matched the exact catalog clash,
then `selfSeam` added the identity projection while preserving its witnesses. -/
example : LoomDoc.one_wide.seam =
    Uwueave.Spec.SegVerdict.selfSeam WeaveState.pinsVerdict rfl := rfl

/-- Its binary facet is the same hand verdict after forgetting the seam. -/
example : LoomDoc.one_wide.verdict = WeaveState.pinsVerdict := rfl

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
    because that document has per-user bookmarks. `LoomDoc2` deliberately keeps
    the fragment-2 one-user shape as a regression; §3⅝ declares the full keyed
    form. Same theorem underneath, smaller statement here, and the report does
    not pretend otherwise.
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

⚠ One thing this file still does NOT show, because it is not yet true: the
derived seam does not make `WeaveState.weaveDocSeamVerdict` derivable. That
object segments a **whole eight-field document** over `(pins, allocation)`.
The two-Quota declaration in §3¾ closes the product-shaped composition rule;
the eventual eight-field prize additionally needs a pins-side surface seam and
`SegVerdict.absorbFree` wiring for the coordination-free conjuncts. -/

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
regression shape. What is compared here is the answer; §3⅝ checks exact keyed
value equality. -/
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

/-! ### 3⅝. A keyed cross row is the hand bookmarks verdict

`field bookmarks per Bool : GrowSet Nat` has carrier
`Bool → GSet Nat` and pointwise merge. The invariant is classified once against
the joint merge of `nodes × GSet Nat`, then
`Uwueave.keyed_cross_iconfluent` transports that proof to every user. -/

preo KeyedDoc where
  field nodes : GrowSet Nat
  field bookmarks per Bool : GrowSet Nat

  invariant fk : ∀ u n, bookmarks u n = true → nodes n = true

#preo_report KeyedDoc

/-- **The keyed surface rediscovers the full hand verdict as the same value.**
This is no longer the one-user approximation of `LoomDoc2.fk`: carrier,
predicate, and proof route all have the `User → GSet NodeId` shape. -/
example : KeyedDoc.fk.verdict = WeaveState.bookmarksVerdict := rfl

/-- The keyed field's emitted carrier and accessor are definitionally the
pointwise family the surface promises. -/
example : KeyedDoc.bookmarks (fun _ => false, fun u n => u && n == 0) true 0 = true := rfl

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

/-! ## §3¾. Two row seams become one document seam

This is the seam-registry composition acceptance. Each invariant independently
reaches `Preo.budgetSeam 10`; because the declaration has exactly two fields,
the elaborator lifts the left verdict with `SegVerdict.liftFst`, lifts the right
with `.liftSnd`, and conjoins them on `TwinQuota.State` with `.andSeams`.

The result is not merely extensionally plausible. It is the existing hand
composition `budgetSegVerdict.prodSeams budgetSegVerdict` as a value, by `rfl`:
same pair-of-allocations seam and the same left-field concrete clash with the
right field held at its carried legal witness. -/

preo TwinQuota where
  field east : Quota Bool
  field west : Quota Bool

  invariant east_budget : Uwueave.Segmented.BudgetInv 10 east
  invariant west_budget : Uwueave.Segmented.BudgetInv 10 west

#preo_report TwinQuota

/-- **The registry rediscovers the hand composition as the same value.** This
checks more than agreement of answers: `rfl` sees the pair seam, both lifted
field verdicts, and the carried global repro. Proof-valued fields are irrelevant
by proof irrelevance; every computational field is definitionally identical. -/
example : TwinQuota.documentSeam =
    Spec.budgetSegVerdict.prodSeams Spec.budgetSegVerdict := rfl

/-- The derived document seam watches both allocation functions. No scalar or
single-field seam has been substituted for the pair. -/
example : TwinQuota.documentSeam.σ =
    (fun d : TwinQuota.State => (d.1.1, d.2.1)) := rfl

/-- The composed verdict retains a concrete global refutation: two legal
two-quota documents can merge outside the conjunction. -/
example : ¬ IConfluent (S := TwinQuota.State) (fun d =>
    TwinQuota.east_budget (TwinQuota.east d) ∧
      TwinQuota.west_budget (TwinQuota.west d)) :=
  TwinQuota.documentSeam.escalatesGlobally

/-! ## §3⅘. Nested-state composition and checked free absorption

This declaration deliberately has eight flat surface fields, with the pin and
quota at the far end of the right-nested product. The document rule must find
and lift those two seams without assuming they are `Prod.fst`/`Prod.snd` of the
whole state. Its custom sections plant each seam verdict's legal `x` in the
other coordinated field; in particular they do **not** plant the structural
zero quota, which is illegal at budget 10.

The six preceding free rows all hold at the carried pin-clash documents, so
the registry's `absorbFree` attempts succeed. The numbered sixth constant in
the acceptance below is an intentional tripwire: silently skipping even one
side condition makes this module fail to elaborate. -/

preo NestedSurface where
  field nodes     : GrowSet Nat
  field bookmarks : GrowSet Nat
  field flags     : GrowSet Bool
  field spend     : Escrow Bool
  field height    : Counter
  field title     : LWW
  field pins      : Slot Nat
  field quota     : Quota Bool

  invariant nodes_clear : nodes 0 = false
    := .free (Uwueave.Catalog.gset_notmem_iconfluent 0)
  invariant bookmarks_clear : bookmarks 0 = false
    := .free (Uwueave.Catalog.gset_notmem_iconfluent 0)
  invariant flags_clear : flags false = false
    := .free (Uwueave.Catalog.gset_notmem_iconfluent false)
  invariant spend_clear : ∀ u, spend u ≤ 0
    := .free (Uwueave.Catalog.escrow_local_bound_iconfluent (fun _ => 0))
  invariant height_zero : height = 0
  invariant title_zero : title.ts = 0
  invariant one_pin : ∀ m n, pins m = true → pins n = true → m = n
  invariant in_budget : Uwueave.Segmented.BudgetInv 10 quota

#preo_report NestedSurface

/-- All six free rows were absorbed after the two seam rows. This equality is
definitionally trivial only if every side-condition attempt emitted its
numbered constant. -/
example : NestedSurface.documentSeam = NestedSurface.documentSeamFree6 := rfl

/-- **The nested registry derives the hand document-seam shape.** Its carrier
is the surface's flat right nest rather than `WeaveState.WeaveDoc`, but the
coordination projection is exactly `(pins, allocation)` through that nest. -/
example : NestedSurface.documentSeam.σ = (fun d : NestedSurface.State =>
    (NestedSurface.pins d, (NestedSurface.quota d).1)) := rfl

/-- The absorbed result still carries the concrete pin clash at whole-document
scale; absorption never weakens or existentially forgets the repro. -/
example : ¬ IConfluent (fun d : NestedSurface.State =>
    (((((((NestedSurface.one_pin (NestedSurface.pins d)
      ∧ NestedSurface.in_budget (NestedSurface.quota d))
      ∧ NestedSurface.nodes_clear (NestedSurface.nodes d))
      ∧ NestedSurface.bookmarks_clear (NestedSurface.bookmarks d))
      ∧ NestedSurface.flags_clear (NestedSurface.flags d))
      ∧ NestedSurface.spend_clear (NestedSurface.spend d))
      ∧ NestedSurface.height_zero (NestedSurface.height d))
      ∧ NestedSurface.title_zero (NestedSurface.title d))) :=
  NestedSurface.documentSeam.escalatesGlobally

/-! ## §3⅞a. The general algebra reconstructs the eight-field hand verdict

The first surface could not declare `WeaveCore` as one grouped carrier or name
the legal seed `core₀` that absorption honestly requires. §3⅞b below closes
both carrier-shape gaps with the explicit-seed custom form. One narrower
surface boundary remains: built-in `Quota` deliberately plants its structural
zero, which is not legal for `BudgetInv 10`; the elaborator may not silently
replace it with the invariant-specific `quota₀`. That is not an algebra gap.
At the term layer the route is now complete and contains no theorem specialized
to `WeaveState`:

1. turn the already-certified pins clash into its conservative identity seam;
2. compose it with the quota allocation seam;
3. lift that coordination surface beside the free core; and
4. prepend the free core with `SegVerdict.prependFree`.

Choosing the hand proof's own legal planting values (`quota₀`, `core₀`) makes
the result the same `SegVerdict` value, not merely the same projection. -/

/-- The pins-side seam the document needs: coordinate on the whole pin set.
`selfSeam` retains `pinsVerdict`'s singleton/singleton repro verbatim. -/
def weavePinsSeam :
    SegVerdict (S := GSet Nat)
      (fun s => ∀ m n, s m = true → s n = true → m = n) (GSet Nat) :=
  Uwueave.Spec.SegVerdict.selfSeam WeaveState.pinsVerdict rfl

/-- The two non-free fields composed over `(pins, allocation)`. The quota is
held at the hand proof's legal `quota₀` while the carried pins clash fires. -/
def weaveCoordViaAlgebra :
    SegVerdict (S := GSet Nat × Segmented.QuotaState)
      (fun p => (∀ m n, p.1 m = true → p.1 n = true → m = n)
        ∧ Segmented.BudgetInv 10 p.2)
      (GSet Nat × (Bool → Nat)) :=
  (weavePinsSeam.liftFst WeaveState.quota₀).andSeams
    (WeaveState.quotaVerdict.liftSnd WeaveState.pinA)
    WeaveState.quota₀_legal WeaveState.quota₀_legal

/-- **The eventual prize at the general combinator layer.** No field of this
record is hand-written here: identity seam, product lifts, same-state seam
conjunction, and free-prefix absorption reconstruct the existing value. -/
def weaveDocViaAlgebra :
    SegVerdict WeaveState.weaveDocInv (GSet Nat × (Bool → Nat)) :=
  (weaveCoordViaAlgebra.liftSnd WeaveState.core₀).prependFree
    (WeaveState.fst_iconfluent WeaveState.core_iconfluent)
    WeaveState.core₀_legal WeaveState.core₀_legal

/-- **Whole-value rediscovery by reduction.** The seam, both complete document
witnesses, and every non-proof field coincide with the hand artifact. -/
example : weaveDocViaAlgebra = WeaveState.weaveDocSeamVerdict := rfl

/-! ## §3⅞b. An application carrier with an explicit planting seed

The six built-in field kinds are useful catalog entries, not a closed universe
of application state. `custom` accepts the existing grouped `WeaveCore`
carrier only because its product `MergeState` already exists, and it makes the
seed visible instead of synthesizing an arbitrary inhabitant. Together with
the two built-in coordination fields, right nesting is definitionally the hand
document carrier. -/

preo GroupedCarrierSurface where
  field core : (custom WeaveState.WeaveCore) := WeaveState.core₀
  field pins : GrowSet WeaveState.NodeId
  field quota : Quota WeaveState.User

/-- The predictable alias retains the application carrier, without wrapping or
flattening it. -/
theorem groupedCarrierSurface_core_carrier :
    GroupedCarrierSurface.core.Carrier = WeaveState.WeaveCore := rfl

/-- **Whole carrier acceptance.** Explicit grouping now reaches the hand state
shape that eight flat surface fields deliberately did not. -/
theorem groupedCarrierSurface_state_is_weaveDoc :
    GroupedCarrierSurface.State = WeaveState.WeaveDoc := rfl

theorem groupedCarrierSurface_core_seed_is_core₀ :
    GroupedCarrierSurface.core.seed = WeaveState.core₀ := rfl

theorem groupedCarrierSurface_core_plant_proj
    (core : GroupedCarrierSurface.core.Carrier) :
    GroupedCarrierSurface.core
        (GroupedCarrierSurface.core.plant core) = core :=
  GroupedCarrierSurface.core.plant_proj core

/-! ## §4. Named futures and proof-carrying protocol sessions

This is a thin surface over the semantic modules. A future names its complete
`Future.WorldModel`; a protocol body is a typed `Protocol.Term`; and a session
is the result of one call to the proof-carrying Protocol API. Nothing below
stores a FREE bit, a meeting count, or a state-only certificate. -/

/-- The one-element strategy space used by the checked profile-plan examples.
Its nonemptiness is structural (`head`), not an elaborator assumption. -/
def unitStrategies : CoordEffect.Admissible Unit where
  head := ()
  rest := []

preo SemanticSurface where
  field marker : Counter

  invariant nonnegative : marker ≤ marker

  future Delivered on (Future.evidenceWorldModel Holes.Val) :=
    Future.Delivery Holes.Val
  future Working on (Future.evidenceWorldModel Holes.Val) :=
    Future.Extension Holes.Val
  future EraDelivered on Future.eraWorldModel := Future.EraDelivery
  future EraIssuing on Future.eraWorldModel := Future.EraIssuance
  future EraAnnouncing on Future.eraWorldModel := Future.EraAnnouncement

  typed derive Next over {
    schema := [.nat, .nat],
    reach := [Incremental.before, Incremental.secondChangedAfter,
      Incremental.firstChangedAfter]
  } :=
    .natSucc (.field 0)
  typed derive Total over {
    schema := [.nat, .nat],
    reach := [Incremental.before]
  } :=
    .natAdd (.field 0) (.field 1)

  protocol Coalescing over Unit := Protocol.coalescingProtocol
  protocol Ambient over Unit := Protocol.ambientProtocol
  protocol TwoRound over Unit := Protocol.twoRoundProtocol

  session Coalesced runs Coalescing at ()
  session Profiled under unitStrategies runs Coalescing at () := by
    simp [unitStrategies, CoordEffect.Admissible.toList]
  session Combined under unitStrategies composes Coalescing with Ambient at () := by
    simp [unitStrategies, CoordEffect.Admissible.toList]

#preo_report SemanticSurface

/-! ### 4.0 Intrinsically typed programs reach the checked runtime adapter -/

/-- A hand-written value for whole-program comparison. Its success field is
the actual reduction of `Raw.infer`, not an independent type assertion. -/
def handNextProgram : Expr.Program [.nat, .nat] where
  raw := .natSucc (.field 0)
  success := rfl

/-- Whole-value acceptance: the surface program is the direct hand-built
`Expr.Program`, including its raw spelling and inference witness. -/
theorem semanticSurface_next_is_hand_program :
    SemanticSurface.Next.Program = handNextProgram := rfl

/-- The existential inference result and typed term are exactly the expected
hand values. -/
theorem semanticSurface_next_checked_exact :
    SemanticSurface.Next.Checked =
      ⟨.nat, Expr.Term.natSucc (.var .here)⟩
      ∧ SemanticSurface.Next.Term = Incremental.firstPlusOne := by
  exact ⟨rfl, rfl⟩

/-- Positional holes and their erased field reads come from one structural
analysis. The unary successor contributes child path `[0]`. -/
theorem semanticSurface_next_exact_dependencies :
    SemanticSurface.Next.Holes =
        [{ path := [0], field := 0, kind := .field }]
      ∧ SemanticSurface.Next.Reads = [0]
      ∧ SemanticSurface.Next.Reads =
        SemanticSurface.Next.Holes.map Expr.Hole.field := by
  exact ⟨rfl, rfl, rfl⟩

/-- Positive classifications contain proofs, never detached Boolean labels. -/
theorem semanticSurface_next_positive_certificates :
    (∃ safe, SemanticSurface.Next.MergeSafe? = some safe)
      ∧ (∃ safe, SemanticSurface.Next.MonotoneSafe? = some safe) := by
  exact ⟨⟨.natSucc (.var .here), rfl⟩,
    ⟨.ofMergeSafe (.natSucc (.var .here)), rfl⟩⟩

/-- Addition is admitted by the larger monotone fragment but deliberately not
misclassified as preserving independent merge. -/
theorem semanticSurface_total_honest_incompleteness :
    SemanticSurface.Total.MergeSafe? = none
      ∧ (∃ safe, SemanticSurface.Total.MonotoneSafe? = some safe) := by
  exact ⟨rfl, ⟨.natAdd (.ofMergeSafe (.var .here))
    (.ofMergeSafe (.var (.there .here))), rfl⟩⟩

def semanticSurfaceNextCache : SemanticSurface.Next.Cache :=
  SemanticSurface.Next.buildCache Incremental.before

def semanticSurfaceRemoteAgainAfter : Expr.Env [.nat, .nat] :=
  .cons (t := .nat) (2 : Nat) (.cons (t := .nat) (100 : Nat) .nil)

/-- A second consecutive delta on the same off-dependency field, now based at
the first update's `after` environment. -/
def semanticSurfaceRemoteAgain :
    Incremental.EnvDelta Incremental.secondChangedAfter where
  after := semanticSurfaceRemoteAgainAfter
  changed := Incremental.changedSecondField
  unchanged := by
    intro t field h
    cases field with
    | here => rfl
    | there field =>
        cases field with
        | here => simp [Incremental.changedSecondField] at h
        | there field => nomatch field

/-- A change to field 1 is outside `Next`'s exact dependency set, so the
generated checked update reuses its cache with zero root evaluations. -/
theorem semanticSurface_next_off_dependency_zero :
    (SemanticSurface.Next.update semanticSurfaceNextCache
      Incremental.secondChanged).recomputations = 0 :=
  (SemanticSurface.Next.update_off_dependency_zero semanticSurfaceNextCache
    Incremental.secondChanged rfl).1

/-- The retained value is still linked to a fresh evaluation at the post-state
by the generated correctness theorem. -/
theorem semanticSurface_next_update_correct :
    (SemanticSurface.Next.update semanticSurfaceNextCache
      Incremental.secondChanged).value =
        SemanticSurface.Next.Eval Incremental.secondChanged.after :=
  SemanticSurface.Next.update_correct semanticSurfaceNextCache
    Incremental.secondChanged

def semanticSurfaceNextCacheAfterRemote : SemanticSurface.Next.Cache :=
  SemanticSurface.Next.updateCache semanticSurfaceNextCache
    Incremental.secondChanged

/-- Update results are first-class next caches, so a second delta chains
without rebuilding or reevaluating the initial environment. -/
theorem semanticSurface_next_cache_chains :
    semanticSurfaceNextCacheAfterRemote.env = Incremental.secondChangedAfter
      ∧ semanticSurfaceNextCacheAfterRemote.value = (3 : Nat)
      ∧ (SemanticSurface.Next.update semanticSurfaceNextCacheAfterRemote
          semanticSurfaceRemoteAgain).recomputations = 0 := by
  refine ⟨rfl, rfl, ?_⟩
  exact (SemanticSurface.Next.update_off_dependency_zero
    semanticSurfaceNextCacheAfterRemote semanticSurfaceRemoteAgain rfl).1

/-- The evaluator hook is deliberately a small stable seam for the checked
six-status `ResultProgram` adapter; consumers need not unwrap `Checked`. -/
theorem semanticSurface_next_eval_exact :
    SemanticSurface.Next.Eval Incremental.before = (3 : Nat) := rfl

/-- The authored typed environment is a query input contract, not a hidden
projection from the surrounding document. Here the document is definitionally
`Nat`, while the typed program explicitly consumes two naturals. An application
that wants document evaluation must write its `State → Expr.Env Schema`
projection and can then call `Next.Eval`; none is inferred from field names. -/
theorem semanticSurface_typed_environment_boundary :
    SemanticSurface.State = Nat
      ∧ SemanticSurface.Next.Schema = [.nat, .nat]
      ∧ SemanticSurface.Next.Reach =
        [Incremental.before, Incremental.secondChangedAfter,
          Incremental.firstChangedAfter] := by
  exact ⟨rfl, rfl, rfl⟩

/-- The generated result program consumes the typed evaluator and the exact
finite reach; its future and resolution remain visible in its type and
descriptor. -/
theorem semanticSurface_next_result_exact :
    SemanticSurface.Next.Result.reach = SemanticSurface.Next.Reach
      ∧ SemanticSurface.Next.Result.evaluate Incremental.before = .exact (3 : Nat)
      ∧ SemanticSurface.Next.Result.descriptor.resolution =
        StatusEffects.Resolution.preserveFork := by
  exact ⟨rfl, rfl, rfl⟩

/-- The written reach does real least-effect work: exact is supported, and any
other effect supporting all three written environments subsumes the generated
one. -/
theorem semanticSurface_next_effect_exact :
    SemanticSurface.Next.Result.effect.Allows StatusEffects.Shape.exact := by
  apply SemanticSurface.Next.Result.effect_supports Incremental.before
  change Incremental.before ∈ SemanticSurface.Next.Reach
  simp [SemanticSurface.Next.Reach]

theorem semanticSurface_next_effect_is_least
    (candidate : StatusEffects.Effect)
    (supports : StatusEffects.Supports candidate
      SemanticSurface.Next.Result.reach SemanticSurface.Next.Result.evaluate) :
    SemanticSurface.Next.Result.effect ⊑ₑ candidate :=
  SemanticSurface.Next.Result.effect_least candidate supports

def semanticSurfaceNextReport :=
  SemanticSurface.Next.reportAt Incremental.before (by simp [SemanticSurface.Next.Reach])

/-- End-to-end checked report acceptance: the carrier site is the environment
actually evaluated, not a report-supplied claim. -/
theorem semanticSurface_next_report_site :
    SemanticSurface.Next.ResultCarrier.site semanticSurfaceNextReport.checked.output =
      Incremental.before :=
  ResultProgram.CheckedReport.site_exact semanticSurfaceNextReport.checked

/-- The report says exactly the status computed at that checked site. -/
theorem semanticSurface_next_report_status :
    SemanticSurface.Next.ResultCarrier.Says semanticSurfaceNextReport.checked.output
      (.exact (3 : Nat)) := by
  simpa using ResultProgram.CheckedReport.says_computed semanticSurfaceNextReport.checked

/-- Reach admission survives construction as proof-carrying report data, so a
downstream consumer can recover effect support rather than trusting the call
site that built the report. -/
theorem semanticSurface_next_report_retains_reach :
    semanticSurfaceNextReport.checked.state ∈ SemanticSurface.Next.Reach :=
  semanticSurfaceNextReport.inReach

/-- Future identity, preserve-fork resolution, surface identity, visibility
and disclosure all come from the checked declaration. -/
theorem semanticSurface_next_report_policy_exact :
    semanticSurfaceNextReport.checked.futureId =
        "Uwueave.Preo.Demo.SemanticSurface.Next/snapshot-equality"
      ∧ semanticSurfaceNextReport.checked.resolutionId =
        ResultProgram.ResolutionIdentity.preserveFork
      ∧ semanticSurfaceNextReport.checked.surfaceId =
        "Uwueave.Preo.Demo.SemanticSurface.Next/inspectable"
      ∧ semanticSurfaceNextReport.checked.visibility =
        ResultProgram.Visibility.inspectable
      ∧ semanticSurfaceNextReport.checked.disclosure (3 : Nat) =
        ResultProgram.Disclosure.shown := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! #### Typed-program refusals

These are surface-command failures, not merely equations about `Raw.infer` in
isolation. A failed row records no report metadata and emits none of the typed
term, positive analyses, cache/update, or result/report artifacts. -/

/--
error: preo: `typed derive Broken` was refused by `Preo.Expr.Raw.infer`. The expression is malformed, reads a field outside its schema, applies an operator at the wrong type, or uses raw `.custom`, which has no implementation/locality proof. No typed term or positive analysis was emitted. Kernel reduction said: Tactic `decide` proved that the proposition
  (Expr.Raw.infer Schema Raw).isSome = true
is false
-/
#guard_msgs in
preo BadTypedMalformed where
  field marker : Counter
  typed derive Broken over { schema := [], reach := [] } :=
    .boolNot (.litNat 7)

/--
error: preo: `typed derive Hidden` was refused by `Preo.Expr.Raw.infer`. The expression is malformed, reads a field outside its schema, applies an operator at the wrong type, or uses raw `.custom`, which has no implementation/locality proof. No typed term or positive analysis was emitted. Kernel reduction said: Tactic `decide` proved that the proposition
  (Expr.Raw.infer Schema Raw).isSome = true
is false
-/
#guard_msgs in
preo BadTypedOpaque where
  field marker : Counter
  typed derive Hidden over { schema := [], reach := [] } :=
    .custom "unchecked"

/-! ### 4.1 A session budget is one five-currency plan witness -/

preo_budget CoalescedProfileBudget for SemanticSurface.Coalesced :
    Scheduling.peerOnlyLimits := Scheduling.coalescedProfileUpperBound

/-- Whole-value acceptance against the existing hand witness. The command does
not rebuild its plan, limits, or pointwise proof. -/
theorem coalescedProfileBudget_is_hand_witness :
    CoalescedProfileBudget = Scheduling.coalescedProfileUpperBound := rfl

theorem coalescedProfileBudget_plan_is_generated_plan :
    CoalescedProfileBudget.Plan = CoalescedProfileBudget.plan := rfl

/-- Every coordinate remains independently observable. Four genuine zeroes do
not become a scalar zero and the peer action is not read from crossings. -/
theorem coalescedProfileBudget_retains_five_currencies :
    CoalescedProfileBudget.plan.profile .peerBarrier = 1
      ∧ CoalescedProfileBudget.plan.profile .arbiterCut = 0
      ∧ CoalescedProfileBudget.plan.profile .networkRound = 0
      ∧ CoalescedProfileBudget.plan.profile .userPrompt = 0
      ∧ CoalescedProfileBudget.plan.profile .rollback = 0 := by
  decide

/-- The standalone surface has no crossing-count acceptance route. -/
theorem no_crossing_count_accepts_profile_budget :
    ¬ ∃ accepts : Nat → Bool, ∀ s : Scheduling.Session,
      accepts s.crossings = true ↔
        Scheduling.HasProfileUpperBound s Scheduling.zeroLimits :=
  Scheduling.no_crossing_count_decides_profile_acceptance

/-- Nor can a peer-meeting floor accept the other four coordinates. -/
theorem meeting_floor_does_not_accept_profile_budget :
    Scheduling.MeetingFloor Scheduling.mixedCurrencySession 1
      ∧ 1 ≤ Scheduling.peerOnlyLimits .peerBarrier
      ∧ ¬ Scheduling.HasProfileUpperBound Scheduling.mixedCurrencySession
          Scheduling.peerOnlyLimits :=
  Scheduling.meeting_floor_does_not_entail_profile_acceptance

/- An exportable budget is explicitly about the exact plan carried by its
source elaboration. This second witness preserves all five realized coordinates
and makes the plan-equality licence definitionally visible to the manifest. -/
preo_budget GeneratedCoalescedProfileBudget for SemanticSurface.Coalesced :
    SemanticSurface.Coalesced.plan.profile :=
  SemanticSurface.Coalesced.exactProfileUpperBound

theorem generatedCoalescedProfileBudget_is_exact_elaboration_bound :
    GeneratedCoalescedProfileBudget =
      SemanticSurface.Coalesced.exactProfileUpperBound := rfl

/-- The historical coalesced plan uses one barrier, while conservative protocol
elaboration retains one action per obligation. It is a valid bound for the same
session, but cannot be attached to the generated plan under a false equality. -/
theorem coalescedHandBudget_has_no_generated_plan_equality :
    ¬ CoalescedProfileBudget.plan = SemanticSurface.Coalesced.plan := by
  intro same
  have profileSame := congrArg
    (fun plan => plan.profile Scheduling.Currency.peerBarrier) same
  change 1 = 2 at profileSame
  omega

/-! ### 4.2 Named certificates retain their complete dependent type -/

preo_certificate QuiescedRenderCertificate :
    Future.CheckedCertificate SemanticSurface.Delivered WorldFuture.renderW
      (fun w => w) (fun w => WorldFuture.Quiesced w) Future.quiescedIndex :=
  Future.quiescedWorldCertificate

/-- Whole-value acceptance: the standalone surface adds a stable name, not a
state-only approximation or a second certificate semantics. -/
theorem quiescedRenderCertificate_is_hand_certificate :
    QuiescedRenderCertificate = Future.quiescedWorldCertificate := rfl

/- A deliberately constant observation admits a real extension certificate;
it is useful here because it lets the surface exercise the variance direction
without asserting that `renderW` is extension-stable. -/
preo_certificate ConstantExtensionCertificate :
    Future.CheckedCertificate SemanticSurface.Working (fun _ => ())
      (fun _ => ()) (fun _ => True) Future.quiescedIndex := by
  refine { accepted := True.intro, soundForAll := ?_ }
  intro _ _ _ _
  rfl

preo_certificate ConstantDeliveryCertificate :
    Future.CheckedCertificate SemanticSurface.Delivered (fun _ => ())
      (fun _ => ()) (fun _ => True) Future.quiescedIndex :=
  Future.extensionCertificateToDelivery ConstantExtensionCertificate

/-- Certificate variance is extension → delivery, by the semantic API. -/
theorem constantCertificate_restricts_extension_to_delivery :
    ConstantDeliveryCertificate =
    Future.extensionCertificateToDelivery ConstantExtensionCertificate := rfl

/-! ### 4.3 One explicit checked export manifest

Every numeric identity below is manifest data. The source names select checked
field, classification, future/certificate and elaboration constants; none is
hashed, inferred from state, or read back out of `#preo_report`. Both the plain
and profiled session names denote one `Protocol.Elaboration`; the composed
`SemanticSurface.Combined` is deliberately not exportable by the V2 command. -/

preo_export SemanticExport from SemanticSurface :
    ProjectionV2.Examples.config :=
  declaration := { id := 700, stateType := 701, schema := 1 }
  | field marker := { id := 702, kind := 10, carrier := 701, key := none }
  | invariant nonnegative := {
    id := 703, carrier := 701, codec := Export.Examples.natCodec,
    answered := rfl }
  | future Delivered := {
    certificate := QuiescedRenderCertificate, id := 704,
    world := 705, relation := 706 }
  | budget GeneratedCoalescedProfileBudget for Coalesced := {
    id := 711, session := 707, plan := 708, samePlan := rfl }
  | session Profiled := { id := 709, plan := 710 }

/-- The exact hand builder chain. Its type index is the real generated state,
and each semantic row is eliminated at the checked Export API immediately. -/
noncomputable def semanticExportHandBundle :
    Export.DeclarationBundle SemanticSurface.State :=
  Export.DeclarationBundle.addElaboration
    (Export.DeclarationBundle.addElaborationWithBudget
      (Export.DeclarationBundle.addCertifiedFuture
        (Export.DeclarationBundle.addClassification
          (Export.DeclarationBundle.addField
            (Carrier := SemanticSurface.marker.Carrier)
            (Export.DeclarationBundle.ofDeclaration SemanticExport.Declaration)
            ⟨702⟩ 10 701 none)
          SemanticSurface.nonnegative.classification rfl
          ⟨703⟩ 701 Export.Examples.natCodec)
        SemanticSurface.Delivered QuiescedRenderCertificate
        ⟨704⟩ 705 706)
      SemanticSurface.Coalesced ⟨707⟩ ⟨708⟩ ⟨711⟩
      GeneratedCoalescedProfileBudget rfl)
    SemanticSurface.Profiled ⟨709⟩ ⟨710⟩

/-- Whole-value acceptance: surface elaboration is exactly the direct checked
builder chain, including row order and every explicit stable ID. -/
theorem semanticExport_bundle_is_hand_builder :
    SemanticExport.Bundle = semanticExportHandBundle := rfl

theorem semanticExport_artifact_is_hand_builder :
    SemanticExport.Artifact = semanticExportHandBundle.toArtifact := rfl

/-- The paired projection selects the canonical structural encoding and that
encoding decodes to the exact checked artifact emitted beside it. -/
theorem semanticExport_canonical_roundtrip :
    SemanticExport.Encoding.decode = SemanticExport.Artifact :=
  SemanticExport.Projection.decode_encoding

/-- The durable frame is canonical and returns the exact neutral encoding with
no trailing bytes; decoding it does not reconstruct any proof object. -/
theorem semanticExport_durable_roundtrip :
    ArtifactDurable.decodeProjection SemanticExport.ArtifactDurableBytes =
      some (SemanticExport.Encoding, []) :=
  ArtifactDurable.decodeProjection_projectionBytes SemanticExport.Encoding

/-- The generated stable IDs and row counts are data-visible exactly as
written. There is one field/invariant/future and two session/plan pairs. -/
theorem semanticExport_exact_ids_and_lengths :
    SemanticExport.Encoding.declaration.id = 700
      ∧ SemanticExport.Encoding.declaration.stateTypeId = 701
      ∧ SemanticExport.Encoding.declaration.schemaVersion = 1
      ∧ SemanticExport.Encoding.fields.map (fun row => row.id) = [702]
      ∧ SemanticExport.Encoding.invariants.map (fun row => row.id) = [703]
      ∧ SemanticExport.Encoding.futures.map (fun row => row.id) = [704]
      ∧ SemanticExport.Encoding.sessions.map (fun row => row.id) = [707, 709]
      ∧ SemanticExport.Encoding.plans.map (fun row => row.id) = [708, 710]
      ∧ SemanticExport.Encoding.budgets.map (fun row => row.id) = [711]
      ∧ SemanticExport.Encoding.fields.length = 1
      ∧ SemanticExport.Encoding.invariants.length = 1
      ∧ SemanticExport.Encoding.futures.length = 1
      ∧ SemanticExport.Encoding.sessions.length = 2
      ∧ SemanticExport.Encoding.plans.length = 2
      ∧ SemanticExport.Encoding.budgets.length = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- Representation identities and every cross-row reference remain exactly the
written manifest values; no source-name hashing fills any of these columns. -/
theorem semanticExport_exact_manifest_rows :
    SemanticExport.Encoding.fields.map (fun row =>
        (row.id, row.declarationId, row.kindId, row.carrierTypeId, row.keyTypeId)) =
      [(702, 700, 10, 701, none)]
      ∧ SemanticExport.Encoding.invariants.map (fun row =>
        (row.id, row.declarationId, row.carrierTypeId)) = [(703, 700, 701)]
      ∧ SemanticExport.Encoding.futures.map (fun row =>
        (row.id, row.declarationId, row.worldTypeId, row.relationId)) =
          [(704, 700, 705, 706)]
      ∧ SemanticExport.Encoding.sessions.map (fun row =>
        (row.id, row.declarationId)) = [(707, 700), (709, 700)]
      ∧ SemanticExport.Encoding.plans.map (fun row =>
        (row.id, row.sessionId)) = [(708, 707), (710, 709)]
      ∧ SemanticExport.Encoding.budgets.map (fun row =>
        (row.id, row.sessionId, row.planId)) = [(711, 707, 708)] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both exported plans retain the actual five-coordinate realized profile;
the source neither inserts crossing counts nor invents a meeting scalar. -/
theorem semanticExport_exact_profiles :
    SemanticExport.Encoding.plans.map (fun row => row.profile) =
      [[(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
        (.userPrompt, 0), (.rollback, 0)],
       [(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
        (.userPrompt, 0), (.rollback, 0)]] := rfl

/-- The budget row retains both sides of the checked claim: the written five
limits and the realized five-coordinate profile of the exact exported plan. -/
theorem semanticExport_exact_budget :
    SemanticExport.Encoding.budgets.map
        (fun row => (row.limits, row.realizedProfile)) =
      [([(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
          (.userPrompt, 0), (.rollback, 0)],
        [(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
          (.userPrompt, 0), (.rollback, 0)])] := rfl

/-- Rendering preserves successful validation without executing the validator
or renderer a second time in this proof. The case split is on the already named
validation result; `validation_ok` eliminates its error branch. -/
theorem semanticExport_render_result_ok :
    SemanticExport.RenderResult.isOk = true := by
  change (SemanticExport.Validation.map ProjectionV2.renderRustSource).isOk = true
  cases h : SemanticExport.Validation with
  | ok value => rfl
  | error error =>
      have accepted := SemanticExport.validation_ok
      rw [h] at accepted
      cases accepted

/-- Validation gates all generated outputs before the private value reaches the
renderer. Each computation is established once above and projected here. -/
theorem semanticExport_validated_and_rendered :
    SemanticExport.Validation.isOk = true
      ∧ SemanticExport.RenderResult.isOk = true := by
  exact ⟨SemanticExport.validation_ok, semanticExport_render_result_ok⟩

/-! ### 4.4 Future declarations retain worlds and variance -/

/-- Whole-value acceptance: the surface future is exactly the semantic
delivery declaration, including its name, scope and world relation. -/
example : SemanticSurface.Delivered = Future.Delivery Holes.Val := rfl

/-- The model itself is explicit and definitionally the requested evidence
world, rather than an inferred relation on materialized state. -/
example : SemanticSurface.Delivered.WorldModel =
    Future.evidenceWorldModel Holes.Val := rfl

example : SemanticSurface.Working = Future.Extension Holes.Val := rfl
example : SemanticSurface.EraDelivered = Future.EraDelivery := rfl
example : SemanticSurface.EraIssuing = Future.EraIssuance := rfl
example : SemanticSurface.EraAnnouncing = Future.EraAnnouncement := rfl

/-- Inclusion runs from delivery to extension. -/
example : SemanticSurface.Delivered.IncludedIn SemanticSurface.Working :=
  Future.delivery_le_extension Holes.Val

/-- Consequently an extension-stability artifact restricts to delivery. -/
example {R : Type} {answer : WorldFuture.World Holes.Val → R}
    {index : Future.WorldIndex (Future.evidenceWorldModel Holes.Val)}
    (a : Future.CheckedStability SemanticSurface.Working answer index) :
    Future.CheckedStability SemanticSurface.Delivered answer index :=
  a.restrict (Future.delivery_le_extension Holes.Val)

/-- ⚠ The converse is genuinely false at the concrete quiesced world. -/
example : ¬ Future.CheckedStability SemanticSurface.Working
    WorldFuture.renderW Future.quiescedIndex :=
  Future.delivery_artifact_does_not_promote_to_extension

/-- The concrete delivery certificate cannot be promoted in the unsound
direction: such a certificate would project the refuted extension stability. -/
theorem deliveryCertificate_cannot_export_as_working :
    ¬ Future.CheckedCertificate SemanticSurface.Working
    WorldFuture.renderW (fun w => w) (fun w => WorldFuture.Quiesced w)
      Future.quiescedIndex := by
  intro certificate
  exact Future.delivery_artifact_does_not_promote_to_extension
    certificate.stability

/-- ⚠ Same materialized state, different retained worlds: a checked world
certificate exists, but no state-indexed certificate may be reused there. -/
example :
    Future.quiescedIndex.state = Future.pendingIndex.state
      ∧ Evidence.FreeTermination SemanticSurface.Delivered.future
          WorldFuture.renderW Future.quiescedIndex.world
      ∧ ¬ Evidence.FreeTermination SemanticSurface.Delivered.future
          WorldFuture.renderW Future.pendingIndex.world
      ∧ (¬ ∃ C : Evidence.ResultEvidence Holes.Val → Prop,
          Future.CheckedCertificate SemanticSurface.Delivered WorldFuture.renderW
            WorldFuture.observe C Future.quiescedIndex) :=
  Future.same_state_different_worlds_block_certificate_reuse

/-! ### 4.5 Protocol/session elaboration is one semantic API call -/

example : SemanticSurface.Coalescing = Protocol.coalescingProtocol := rfl
example : SemanticSurface.Ambient = Protocol.ambientProtocol := rfl
example : SemanticSurface.TwoRound = Protocol.twoRoundProtocol := rfl

/-- Whole-value acceptance for the checked elaboration bundle. -/
example : SemanticSurface.Coalesced =
    Protocol.elaborate Protocol.coalescingProtocol () := rfl

example : SemanticSurface.Coalesced.session = Scheduling.coalescingSession := rfl

/-- The plan and upper bound are projections of that one elaboration record. -/
example : SemanticSurface.Coalesced.Plan = SemanticSurface.Coalesced.plan := rfl
example : SemanticSurface.Coalesced.UpperBound =
    SemanticSurface.Coalesced.upperBound := rfl

/-- Profile elaboration also remains the existing semantic value. -/
example : SemanticSurface.Profiled.ProfilePlan =
    Protocol.elaborateProfilePlan unitStrategies Protocol.coalescingProtocol ()
      (by simp [unitStrategies, CoordEffect.Admissible.toList]) := rfl

/-- Composition is pointwise under one selected strategy, not two independent
per-branch choices. The surface value is the modular composed elaboration. -/
example : SemanticSurface.Combined =
    Protocol.elaborateComposedProfilePlan unitStrategies
      Protocol.coalescingProtocol Protocol.ambientProtocol ()
      (by simp [unitStrategies, CoordEffect.Admissible.toList]) := rfl

example :
    let plan := SemanticSurface.Combined
    plan.left.strategy = () ∧ plan.right.strategy = () := by
  exact Protocol.elaborated_composition_uses_one_strategy unitStrategies
    Protocol.coalescingProtocol Protocol.ambientProtocol ()
    (by simp [unitStrategies, CoordEffect.Admissible.toList])

/-- ⚠ Crossings are still not meetings after reaching the surface: two
crossings coalesce into one exact meeting. -/
example :
    (SemanticSurface.Coalescing.denote ()).crossings = 2
      ∧ Scheduling.LeastMeetings (SemanticSurface.Coalescing.denote ()) 1
      ∧ 1 < (SemanticSurface.Coalescing.denote ()).crossings :=
  Protocol.ast_crossings_can_exceed_meetings

/-- …and one crossing can require two incompatible rounds. No report cell or
session constructor replaces these witnessed scheduling theorems by a scalar. -/
example :
    (SemanticSurface.TwoRound.denote ()).crossings = 1
      ∧ Scheduling.LeastMeetings (SemanticSurface.TwoRound.denote ()) 2
      ∧ (SemanticSurface.TwoRound.denote ()).crossings < 2 :=
  Protocol.ast_one_crossing_can_need_two_rounds

/-! ## §5. The keywords are not stolen

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

end Uwueave.Preo.Demo
