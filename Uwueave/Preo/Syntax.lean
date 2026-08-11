/-
# Uwueave.Preo.Syntax — the preoscript surface, and the objects its elaborator emits.

`PREOSCRIPTING.md` §10 lists **surface syntax + elaborator** as the only
*unbuilt* row in a table of otherwise-proved machinery. This module and
`Uwueave.Preo.Elab` are the first thing in that row: a `preo` declaration that
elaborates to ordinary Lean definitions and produces, for every invariant it
carries, a **`Spec.Verdict` term** — or, where no route reaches one, an
`Obligation` that says so and is *not* a verdict.

The reviewer's instruction this follows (codex, quoted in `CODEXHELP.md`): build
the semantic modules first, then *"define the smallest AST required to compose
their evidence, keeping arbitrary Lean computation behind a proved opaque
node."* Everything here is small on purpose. There is no deep-embedded
expression language: an invariant is an ordinary Lean term, and the only thing
the elaborator analyses about it is **which field it reads** (§6). That is the
one syntactic fact the classification carrier depends on, and it is the whole
"AST".

## What lives here

  * §1 the five field kinds and their carriers — every one an existing
    `Catalog` type with a *proved* `MergeState`; no new CRDT is invented here;
  * §2 `proj_iconfluent` — the one new theorem, and the only way a field-scoped
    verdict reaches the declared state type;
  * §3 `Obligation` — the honest non-answer, carrying no evidence field and no
    map into `Verdict`;
  * §4 `witnesses?` / `witnessBits` — reading a derived clash back out, so the
    acceptance test can compare the elaborator's counterexample against a
    hand-written one;
  * §5 the report rows (an environment extension: display metadata only — the
    FREE/ESCALATES column is re-read from the emitted terms at report time, so
    the table cannot drift from the evidence);
  * §6 the surface syntax itself.

## The fragment, stated up front

`preo` covers exactly this and refuses everything else loudly:

```
preo <Name> where
  field <name> : <kind>                       -- kind ∈ GrowSet α · Slot α · Escrow ι · Counter · LWW
  invariant <name> : <predicate>              -- must mention EXACTLY ONE field
  invariant <name> : <predicate> := <verdict> -- author-supplied evidence, kernel-checked
```

*Not* in the fragment, and each is a real feature of `PREOSCRIPTING.md` §7 that
this pass does not build: `per`, `future`, `derive`, `session`, `budget`,
`parallel`, seam verdicts (`SegVerdict` — so a `preo` declaration cannot yet
say "free *within* an allocation", which is exactly what the quota field of
`WeaveState.lean` needs), and cross-field invariants (`Spec.Verdict.cross`),
which are refused rather than guessed at because no per-field lift produces one
and `Catalog.lww_cross_field_not_iconfluent` is why.
-/
import Uwueave.Tactics

namespace Uwueave.Preo

open Uwueave Uwueave.Catalog Uwueave.Spec

universe u v

/-! ## §1. Field kinds

Five, all backed. Four are `Catalog` types verbatim; the fifth (`Slot`) is a
grow-only set under the name of the shape it is *expected* to carry — see its
docstring for what that does and does not buy. -/

/-- **A slot: a grow-only set carrying a uniqueness ceiling.** The carrier is
`Catalog.GSet` — the same type `GrowSet` gives — and the name records the
author's *intent*, which the report prints.

⚠ Read that twice: `Slot` does **not** hand the elaborator a canned verdict.
`Ceiling.uniqueness_ceiling` proves that any invariant entailing "at most one
element per key" over a grow-only set escalates, and it would be easy — and
dishonest — to have the elaborator answer ESCALATES for a field spelled `Slot`
without looking at what was written. It classifies the invariant you actually
wrote, by the routes in `Uwueave.Preo.Elab` §3, and if you write a *free*
invariant on a `Slot` field you get FREE. The kind is a label on the report,
not a shortcut through the classifier. -/
abbrev Slot (α : Type) := GSet α

/-! ## §2. Reaching the declared state — the projection lift

A `preo` declaration builds one state type out of its fields, and every verdict
is earned on **one field's carrier**. This is the theorem that carries a
field-scoped result to the whole declared document, and it is the only new
confluence content in the Preo modules. -/

/-- **A field-scoped invariant lifts along any join-homomorphic projection.**
For a `preo` declaration the projection is a nest of `.1`/`.2` and `hπ` is
`rfl` (`prod_merge_fst`/`prod_merge_snd`), so the elaborator emits the
homomorphism as a one-word proof and this lemma does the rest.

This subsumes `WeaveState.fst_iconfluent` (π = `Prod.fst`) and
`WeaveState.at_key_iconfluent` (π = `(· k₀)`); it is stated once here because
the elaborator needs a *uniform* lift over an arbitrary projection path.

⚠ What it does not do: it lifts a **free** verdict only. A clash on a field
does not travel this way — transporting one needs a legal value for every
other field (`Spec.Verdict.prodClashRight`'s `a` and `ha`), i.e. a legal
document, which the elaborator cannot synthesize and `WeaveState.core₀` builds
by hand. The report says so per row rather than quietly dropping the fact. -/
theorem proj_iconfluent {S : Type u} {T : Type v} [MergeState S] [MergeState T]
    {π : S → T} (hπ : ∀ x y : S, π (x ⊔ y) = π x ⊔ π y)
    {I : Invariant T} (h : IConfluent I) :
    IConfluent (S := S) (fun s => I (π s)) := by
  intro x y hx hy
  show I (π (x ⊔ y))
  rw [hπ]
  exact h _ _ hx hy

/-! ## §3. The non-answer, named

`Uwueave.Tactics`'s discipline is that a search may fail but may never report
a wrong verdict, and that `none` is **no verdict** rather than freedom
(`classifyIn?_never_free`). A DSL inherits that obligation the moment it puts a
table on the screen: the third column needs a cell that is not FREE and not
ESCALATES. -/

/-- **What the elaborator produces when no route reaches a verdict.**

Note what this type does *not* have: any field of a proof type, and any
function into `Spec.Verdict`. It is a record of strings indexed by the
invariant it failed to classify, so it can be printed and cannot be mistaken
for evidence — `Verdict.isFree` does not apply to it, and there is no
`Obligation.toVerdict` to be tempted by. Discharging one means producing a
`Verdict I`; the `discharge` field says what the elaborator thinks that would
take, and that string is a hint, not a claim. -/
structure Obligation {S : Type u} [MergeState S] (I : Invariant S) : Type u where
  /-- The invariant's surface name, as written in the `preo` declaration. -/
  invName : String
  /-- The field it reads, and the kind that field was declared with. -/
  onField : String
  /-- The routes that were tried, in order, and did not apply. -/
  tried : List String
  /-- What would close it — prose, addressed to the author. Not a claim. -/
  discharge : String

/-! ## §4. Reading a verdict back out

`Verdict.isFree` erases everything but the answer. The acceptance test needs
the other half: *which* two replicas the elaborator found, so they can be
compared against the pair a hand proof carries. -/

/-- The two clashing replicas of a refuted verdict, or `none` when it is free.
Total, and it invents nothing: the states come out of the `clash` constructor
that already carries the three facts making them a counterexample. -/
def witnesses? {S : Type u} [MergeState S] {I : Invariant S} : Verdict I → Option (S × S)
  | .free _ => none
  | .clash x y _ _ _ => some (x, y)

/-- A grow-only set over an enumerable element type, as its membership bits in
`FinEnum` order — a state you can compare by `rfl` and read on a page. -/
def bits {α : Type} [Tactics.FinEnum α] (s : GSet α) : List Bool :=
  (Tactics.FinEnum.enum (S := α)).map s

/-- A refuted grow-set verdict's witness pair, as bit vectors. This is how the
acceptance test asks "is the pair the elaborator *found* the same pair
`Spec.atMostOneClash` carries by hand?" and gets an answer that is checked
rather than eyeballed. -/
def witnessBits {α : Type} [Tactics.FinEnum α] {I : Invariant (GSet α)}
    (v : Verdict I) : Option (List Bool × List Bool) :=
  (witnesses? v).map fun p => (bits p.1, bits p.2)

/-! ## §5. Report rows

Display metadata, and *only* display metadata. The FREE/ESCALATES column is
**not** stored here: `#preo_report` re-reads it from the emitted `Verdict`
constant by reduction, every time it prints. That is deliberate — a stored
answer is a second source of truth that can disagree with the term, and this
repo has a memo-vs-term drift class it does not need another instance of. -/

/-- One printable line of a `preo` report. `evidence` names the constant the
answer is read from; `.anonymous` never appears (an unclassified invariant
gets an `Obligation` constant, which is also a constant). -/
structure Row where
  /-- The `preo` declaration this row belongs to. -/
  decl : Lean.Name
  /-- `true` for a field row, `false` for an invariant row. -/
  isField : Bool
  /-- The field's or invariant's surface name. -/
  name : String
  /-- Fields: the kind as written. Invariants: the field they read. -/
  detail : String
  /-- Fields: the carrier type. Invariants: the route that classified them. -/
  detail₂ : String
  /-- The emitted constant: a `Verdict`, or an `Obligation`. -/
  evidence : Lean.Name
  /-- Whether `evidence` is an `Obligation` rather than a `Verdict`. -/
  isObligation : Bool
  /-- What the row cites: a theorem name, or the discharge hint. -/
  cite : String
  deriving Inhabited

open Lean in
/-- The rows of every `preo` declaration in scope. Persisted, so a report can
be printed in a file downstream of the declaration. -/
initialize preoExt : SimplePersistentEnvExtension Row (Array Row) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl (init := #[]) (· ++ ·)
    addEntryFn := fun s a => s.push a
  }

/-! ## §6. The surface

Three points of grammar worth stating, because each was a real failure first:

  * `field` and `invariant` are **non-reserved** keywords (`&"field"`), so this
    module does not steal two ordinary identifiers from every file that imports
    it. Verified in `Uwueave.Preo.Demo` §4, where both are still used as
    definition names.
  * every item is wrapped in `withPosition(…)` with `colGt` guards on the terms
    it contains: without them `field height : Counter` on one line swallows the
    `invariant` beginning the next (measured — `Counter invariant` parsed as an
    application before the guards went in). With them, a predicate may still
    span lines as long as the continuation is indented past the item.
  * the optional `:= <term>` is author-supplied *evidence*, not a hint. It is
    elaborated at type `Spec.Verdict <the invariant>`, so the kernel checks it;
    there is no way to supply a verdict without supplying its proof, and the
    report marks the row `supplied` rather than `derived` regardless. -/

/-- `field <name> : <kind> [<arg>]` — one field of the declared state. -/
syntax preoField := withPosition(&"field" ident " : " ident (ppSpace colGt term:max)?)

/-- `invariant <name> : <predicate> [:= <verdict term>]` — one invariant, over
exactly one field, optionally with its evidence supplied by the author. -/
syntax preoInv := withPosition(&"invariant" ident " : " colGt term (" := " colGt term)?)

/-- **A preoscript declaration.** Elaborates to a state type, its field
accessors, a checked `MergeState`, one `Invariant` per row, and — per row — a
`Spec.Verdict` term or an `Obligation`. See `Uwueave.Preo.Elab` for what is
emitted and in what order; see this file's header for the fragment. -/
syntax (name := preoDecl) "preo " ident " where "
  (ppLine colGe preoField)* (ppLine colGe preoInv)* : command

/-- Print the verdict table of a `preo` declaration: every field with its kind
and carrier, every invariant with the field it reads, its verdict, the route
that produced it and the constant carrying the evidence. The verdict column is
computed from those constants at print time, not stored. -/
syntax (name := preoReport) "#preo_report " ident : command

end Uwueave.Preo
