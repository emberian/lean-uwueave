/-
# Uwueave.Preo.Demo — the acceptance test: does the elaborator rediscover what
`WeaveState.lean` proved by hand?

One `preo` declaration, six fields, six invariants, and every answer the
fragment can give — FREE derived two different ways, ESCALATES with the
counterexample, FREE supplied by the author, and UNRESOLVED. Then §2 checks the
derived rows against the hand-written ones in `Uwueave.WeaveState`, which
classified the same document by hand before any of this existed.

## The result, stated before you read the file

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

## The disagreement, and there is one worth naming

There is no row where the elaborator and the hand proof reach *opposite*
verdicts. What they differ on is **reach**:

`WeaveState.quotaVerdict` is a `SegVerdict` — globally refuted, free within an
allocation, with the seam `docSeam` and the capstone `weaveDoc_segmented`. That
is the most interesting answer in the whole library, and `preo` **cannot state
it at all**: the fragment has one verdict type and no seam. So the escrow row
here is the *other* budget story (`Catalog` §4's rephrasing, free outright), and
the row a real loom needs is not merely unclassified — it is inexpressible. That
is the first thing the next pass should fix, and calling this file's escrow row
"the seam" would have been the lie.

Likewise `WeaveState.bookmarksVerdict` (bookmarks ⊆ nodes) is a `Verdict.cross`,
and §3 shows `preo` refusing that shape by name rather than approximating it.

## What is scaffolding here and what is real

REAL: the emitted `Verdict` terms and the theorems §2 derives from them; the
`.onState` lifts (they typecheck only if the verdict computed `free`); the
composed document-scale theorem `loomDocFree`; the refusals.

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

```lean
preo Bad where
  field notes : GrowSet (Fin 3)
  field pin : Slot (Fin 3)
  invariant fk : ∀ m, pin m = true → notes m = true
```
> preo: invariant `fk` mentions 2 fields (pin, notes) — that is a CROSS-FIELD
> invariant, and it is outside this fragment. No per-field lift produces one and
> none can (`Catalog.lww_cross_field_not_iconfluent` refutes the candidate); it
> must be earned against the joint merge as a `Spec.Verdict.cross`, by hand, as
> `Spec.refIntVerdict` and `WeaveState.bookmarksVerdict` are. Classify one field
> per invariant, or write the cross verdict yourself.

```lean
preo Bad where
  field seq : RGA Nat
  invariant x : seq 0 = true
```
> preo: unknown field kind `RGA`. The fragment has five: `GrowSet α` …

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
> preo: the verdict for `smuggled` depends on sorryAx — outside the axiom floor
> `propext · Classical.choice · Quot.sound` that `#audit_floor` holds the whole
> tree to. … No row is recorded.

That last one is the guard that makes the *supplied* route safe: author-written
evidence is checked against the tree's floor before a row exists, because a
`sorry`-backed `Verdict` prints exactly like a real one — an unproved lemma
emits the same table as a proved one, and no amount of reading the table can
tell.
-/

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
