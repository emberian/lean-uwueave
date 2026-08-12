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
node."* Everything here is small on purpose. Invariants and ordinary derives
remain Lean terms, with only a conservative field-mention scan. The separate
`typed derive` row consumes `Preo.Expr.Raw`, whose deliberately first-order AST
exists exactly where structural reads, merge/monotonicity proofs and checked
incremental reuse need it. Unsupported raw syntax is refused; arbitrary Lean
computation stays in the ordinary escape hatch.

## What lives here

  * §1 `Slot` — one of the six built-in field kinds; the other five are
    `Catalog` and `Segmented` types verbatim (`Quota` lives in
    `Uwueave.Preo.Classification`, next to the seam rule that reads it). The
    explicit-seed `custom` form reuses an application's existing carrier and
    `MergeState`; it invents no CRDT or merge proof;
  * §2 `proj_iconfluent` — the confluence lift, and the way a field-scoped
    verdict reaches the declared state type. Its seam and mergeability
    counterparts (`seamAlong`, `mergeability_comp`) are in
    `Uwueave.Preo.Classification` §6;
  * §3 `Obligation` — the honest non-answer, carrying no evidence field and no
    map into `Verdict`;
  * §4 `witnesses?` / `witnessBits` — reading a derived clash back out, so the
    acceptance test can compare the elaborator's counterexample against a
    hand-written one;
  * §5 the report rows (an environment extension: display metadata only — every
    ANSWER column is reduced out of the row's `Preo.Classification` at report
    time, so the table cannot drift from the evidence);
  * §6 the surface syntax itself, including `typed derive`'s parser-hard schema,
    finite reach and raw program boundary.

## The fragment, stated up front

`preo` covers exactly this and refuses everything else loudly:

```
preo <Name> where
  field <name> : <kind>                       -- kind ∈ GrowSet α · Slot α · Escrow ι
                                              --      · Quota ι · Counter · LWW
  field <name> : (custom <Carrier>) := <seed> -- application carrier; explicit seed
  field <name> per <Key> : <kind>             -- keyed family, merged pointwise
  invariant <name> : <predicate>              -- ONE field, or TWO (a cross-field
                                              -- invariant, over the product state)
  invariant <name> : <predicate> := <verdict> -- author-supplied evidence, kernel-checked
  future <name> on <WorldModel> := <FutureDecl>
  typed derive <name> over {
    schema := <Expr.Schema>, reach := <List (Expr.Env schema)>
  } := <Expr.Raw>
  derive <name> : <type> = <expr>             -- ONE field; the fourth verdict
  derive <name> : <type> = <expr> := <evidence>
  protocol <name> over <Strategy> := <Protocol.Term Strategy>
  session <name> runs <protocol> at <strategy>
  session <name> under <admissible> runs <protocol> at <strategy> := <membership proof>
  session <name> under <admissible> composes <left> with <right>
    at <strategy> := <membership proof>

preo_certificate <name> : <Future.CheckedCertificate ...> := <proof>
preo_budget <name> for <session> : <Currency → Nat limits> := <ProfileUpperBound>
preo_export <name> from <declaration> : <ValidationConfig> :=
  declaration := { id := <Nat>, stateType := <Nat>, schema := <Nat> }
  | field <field> := { id := <Nat>, kind := <Nat>, carrier := <Nat>, key := <Option Nat> }
  | invariant <invariant> := { id := <Nat>, carrier := <Nat>,
    codec := <FirstOrderCodec>, answered := <classification.answer = some _> }
  | future <future> := { certificate := <named certificate>, id := <Nat>,
    world := <Nat>, relation := <Nat> }
  | session <session> := { id := <Nat>, plan := <Nat> }
  | budget <named budget> for <session> := {
    id := <Nat>, session := <Nat>, plan := <Nat>, samePlan := <equality proof> }
```

Fragment 2 closed three of fragment 1's refusals — **seam facets** (a globally
clashing invariant now carries its `SegVerdict` alongside the clash rather than
being inexpressible), **cross-field invariants** (two fields, classified against
the joint merge), and **`derive` with the mergeability verdict**. What changed
structurally is in `Uwueave.Preo.Classification`: a row accumulates *facets*
instead of a winner, and the answer it certifies is proved independent of the
route order (`Preo.run_answer_congr`).

The custom field form requires an existing `MergeState` for the carrier and an
explicit planting seed; the elaborator never guesses an inhabitant of an
application type. The future form is explicitly indexed by a
`Preo.Future.WorldModel`; it cannot silently fall back to a relation on
materialized state. Protocol bodies inside `preo` are typed `Protocol.Term`
values: the six-constructor semantic AST is deep, while this declaration
surface deliberately keeps its body as an ordinary checked Lean term. The
standalone `Preo.ProtocolSurface.preo_protocol` command now provides a
punctuation-delimited native spelling for all six constructors and expands to
that same AST and one `Protocol.elaborate` call. Sessions call
`Protocol.elaborate`, `elaborateProfilePlan`, or
`elaborateComposedProfilePlan` once and expose their proof-carrying results.

*Still* not in this declaration fragment: native protocol bodies inline among
the repeated `preo` items (the separate `preo_protocol` command owns that
grammar), arbitrary schedule discovery, a pretty in-declaration budget block,
invariants over three or more fields, and general declaration composition.
`Preo.Planning` does provide bounded search over a duplicate-free,
caller-capped authored action universe. Ordinary Lean `derive` remains a
one-field escape hatch; `typed derive` is the multi-input first-order program
surface, with its exact positional reads and checked incremental adapter.
Each update result promotes directly to the next cache; generated reports
require membership in the authored finite reach. Typed-program export and
automatic projection from the declaration `State` remain outside this fragment.
`preo_certificate` keeps its full dependent type as an ordinary
Lean term: the command checks that its reduced head is
`Future.CheckedCertificate` but does not invent a state-indexed shorthand.
`preo_budget` is equally thin: it consumes a real five-currency
`Scheduling.ProfileUpperBound` at one emitted session and does no synthesis.
The typed Lean-term escape hatches still reach every protocol constructor,
certificate index and schedule plan. The native protocol parser duplicates no
semantics: it expands to `Protocol.Term` and the existing elaborator.
`preo_export` is likewise a thin checked manifest: its rows call the
proof-indexed `Export.DeclarationBundle` builders immediately, then expose only
their canonical artifact, durable bytes, and validated V2 projection. IDs are
literal manifest data, never hashes of source names. A composed profile plan is
not a `Protocol.Elaboration`, so it has no session row in this first export
surface.

One operational boundary is intentionally visible. The `classify` and
`verdict` tactics cap their implicit exhaustive route at 64 states / 4096
ordered pairs, but this declaration elaborator's finite facet is the explicit,
logically total `Tactics.classifyFinite` function and has no implicit work cap.
It is attempted whenever `FinEnum` and `DecidablePred` synthesize, even if an
author-supplied facet already exists, because applicable facets accumulate.
Keep such carriers small until the declaration route shares the tactic gate.
-/
import Uwueave.Tactics.Verdict

namespace Uwueave.Preo

open Uwueave Uwueave.Catalog Uwueave.Spec

universe u v

/-! ## §1. Field kinds

Six built-ins, all backed, plus one explicit application escape hatch. Four
are `Catalog` types verbatim (`GrowSet`, `Escrow`, `Counter`, `LWW`); `Quota`
is `Segmented.QuotaState` and lives in `Uwueave.Preo.Classification` §1,
beside the seam rule that is the whole reason it exists; and `Slot` — below —
is a grow-only set under the name of the shape it is *expected* to carry, which
is a label and not a shortcut. `(custom T) := seed` accepts `T` only with an
already-proved `MergeState T` and retains the seed as a named checked value. -/

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

`Uwueave.Tactics.Verdict`'s discipline is that a search may fail but may never
report a wrong verdict, and that `none` is **no verdict** rather than freedom
(`classifyIn?_never_free`). A DSL inherits that obligation the moment it puts
a table on the screen: the third column needs a cell that is not FREE and not
ESCALATES. Production consumers import that leaf; the larger
`Uwueave.Tactics` module is its demonstration suite. -/

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

/-- What a report row is about. Fragment 2 adds two item kinds to fragment 1's
two, and they are genuinely different questions — a `derive` row answers "ship
the summary or replay the evidence?" and has no confluence verdict at all. -/
inductive RowKind where
  /-- A declared field: name, kind, carrier. -/
  | field
  /-- An invariant over exactly one field. -/
  | invariant
  /-- An invariant over exactly two fields, classified against the product
  state (`Spec.Verdict.cross`). -/
  | cross
  /-- A computed value, classified by the fourth verdict (`JoinHom.Fourth`). -/
  | derive
  /-- A Raw-inferred first-order program with exact reads and checked cache
  updates. Unlike ordinary `derive`, this row is intrinsically typed. -/
  | typedDerive
  /-- A named, explicitly world-model-indexed future declaration. -/
  | future
  /-- A typed `Protocol.Term`; its semantics remain in `Protocol.Term.denote`. -/
  | protocol
  /-- A proof-carrying protocol elaboration or global-strategy profile plan. -/
  | session
  deriving Inhabited, DecidableEq, Repr

/-- One printable line of a `preo` report. `evidence` names the constant the
answers are read from — for an item row that is its **`Classification`**, and
every answer column (`GLOBAL`, `SEAM`, `MERGEABILITY`) is reduced out of it at
print time. Nothing here stores an answer. -/
structure Row where
  /-- The `preo` declaration this row belongs to. -/
  decl : Lean.Name
  /-- Which semantic/display item kind this row is. -/
  kind : RowKind
  /-- The field's, invariant's or derive's surface name. -/
  name : String
  /-- Fields: the kind as written. Items: the field(s) they read. -/
  detail : String
  /-- Fields: the carrier type. Items: every route that fired, in order. -/
  detail₂ : String
  /-- The emitted constant the answers are read from: the row's
  `Classification` (items) or its `merge_hom` (fields). -/
  evidence : Lean.Name
  /-- Whether the row reached no facet at all — an `Obligation` and nothing
  else. -/
  isObligation : Bool
  /-- What the row cites: theorem names, or the discharge hint. -/
  cite : String
  /-- The seam facet's reading, or `""` when the row has no seam. -/
  seamCite : String
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

/-- A built-in field of the declared state, either scalar or keyed. The keyed
spelling `field <name> per <Key> : <kind>` elaborates to `Key → <carrier>` and
inherits the pointwise `MergeState`; `per` is non-reserved, like `field`
itself. -/
declare_syntax_cat preoFieldBody
syntax "(" &"custom" ppSpace colGt term ")" " := " colGt term : preoFieldBody

/-- An application-defined carrier. `:=` is the parser-hard boundary after the
carrier term, and the seed is mandatory: plants of the other fields need an
actual value, which the elaborator may not infer for an arbitrary type. A
keyed custom field uses the seed pointwise. -/
syntax ident (ppSpace colGt term:max)? : preoFieldBody

syntax preoField := withPosition(&"field" ident
  (ppSpace &"per" ppSpace colGt term:51)? " : " preoFieldBody)

/-- `invariant <name> : <predicate> [:= <verdict term>]` — one invariant, over
**one or two** fields, optionally with its evidence supplied by the author. A
two-field invariant is classified against the product state as a
`Spec.Verdict.cross`; fragment 1 refused that shape outright. -/
syntax preoInv := withPosition(&"invariant" ident " : " colGt term (" := " colGt term)?)

/-- `derive <name> : <type> = <expr> [:= <evidence>]` — a computed value over
exactly one field, classified by the **fourth verdict**: may its summary be
shipped and merged (`JoinHom.Fourth.fromResults`), or must a peer replay the
source evidence (`needsEvidence`)?

Two points of grammar, each paid for:

  * the type sits at `term:51`, so the `=` that follows is the surface's own
    separator rather than an `Eq` inside the type — `PREOSCRIPTING.md` §7
    spells a derive with `=` and this keeps that spelling. A type that
    genuinely needs an equation, or an arrow, must be parenthesised.
  * the optional evidence is introduced by `:=` and **not** by a soft keyword.
    `… evidence <term>` was the first draft and it is unreachable: the body is
    an ordinary `term`, a non-reserved keyword is an ordinary identifier, and
    `(if …) evidence sorry` parses as an application ("function expected") long
    before the item parser sees it. `:=` cannot continue a term, so it is the
    separator that works — and it matches `invariant`'s. -/
syntax preoDerive :=
  withPosition(&"derive" ident " : " colGt term:51 " = " colGt term
    (" := " colGt term)?)

/-- A parser-hard intrinsically typed program.  The braces terminate the
schema and `:=` terminates the header, so neither arbitrary Lean term can eat
the next declaration item. `Raw.infer` determines the result type; malformed
or opaque raw nodes make the entire declaration fail before any program row is
recorded. -/
syntax preoTypedDerive :=
  withPosition(&"typed" ppSpace &"derive" ident ppSpace &"over" ppSpace
    "{" &"schema" " := " colGt term "," ppSpace
      &"reach" " := " colGt term "}" " := " colGt term)

/-- `future <name> on <WorldModel> := <FutureDecl>` — a stable surface name for
a relation on the model's retained world carrier. The model is mandatory:
future declarations cannot be inferred from, or collapsed onto, state alone. -/
syntax preoFuture := withPosition(&"future" ident
  ppSpace &"on" ppSpace colGt term " := " colGt term)

/-- `protocol <name> over <Strategy> := <term>` — a typed opaque entry into the
deep `Protocol.Term` AST. Keeping the body an ordinary Lean term makes all six
semantic constructors available without maintaining a second, drifting parser. -/
syntax preoProtocol := withPosition(&"protocol" ident
  ppSpace &"over" ppSpace colGt term " := " colGt term)

/-- A checked session elaboration. The plain form exposes
`Protocol.Elaboration` and its `.plan`/`.upperBound`; the `under` form also
selects one member of a named admissible strategy space; the `composes` form
uses `elaborateComposedProfilePlan`, so both sides retain that same strategy. -/
declare_syntax_cat preoSessionMode
syntax (name := preoSessionRuns) "runs" ppSpace ident : preoSessionMode
syntax (name := preoSessionProfile) "under" ppSpace ident ppSpace "runs"
  ppSpace ident : preoSessionMode
syntax (name := preoSessionComposed) "under" ppSpace ident ppSpace "composes"
  ppSpace ident ppSpace "with" ppSpace ident : preoSessionMode
syntax preoSession := withPosition(&"session" ident ppSpace preoSessionMode
  ppSpace &"at" ppSpace colGt term (" := " colGt term)?)

/-- **A preoscript declaration.** Elaborates to a state type, its field
accessors, a checked `MergeState`, one `Invariant` per invariant row, one
computation per `derive` row, and — per item — a `Preo.Classification`
accumulating every facet the rule registry certified. See `Uwueave.Preo.Elab`
for what is emitted and in what order; see this file's header for the
fragment. -/
syntax (name := preoDecl) "preo " ident " where "
  (ppLine colGe preoField)*
  (ppLine colGe preoInv)*
  (ppLine colGe preoFuture)*
  (ppLine colGe preoTypedDerive)*
  (ppLine colGe preoDerive)*
  (ppLine colGe preoProtocol)*
  (ppLine colGe preoSession)* : command

/-- Name a checked future certificate without parsing or inferring any of its
dependent indices. The elaborator requires the supplied type to reduce to
`Future.CheckedCertificate ...`, checks the proof at exactly that type, and
applies the same axiom-floor gate as reportable `preo` evidence. Kept as a
standalone command so another adjacent repeated item family cannot make the
declaration grammar ambiguous. -/
syntax (name := preoCertificate) "preo_certificate " ident " : " colGt term:51
  " := " colGt term : command

/-- Accept a five-currency limit only from one exhibited plan for the exact
session carried by a named `Protocol.Elaboration`. The limit is an ordinary
`Currency → Nat` term terminated by `:=`; the evidence must inhabit
`Scheduling.ProfileUpperBound`. No crossing count, meeting floor, scalar upper
bound, or independently selected coordinate plans fit the generated type. -/
syntax (name := preoBudget) "preo_budget " ident ppSpace &"for" ppSpace ident
  " : " colGt term:51 " := " colGt term : command

/-! ### Checked export manifests

The export command has one mandatory declaration row and one repeated *sum*
of tagged rows. Keeping a single repeated syntax category avoids the adjacent
`item* item*` ambiguity that previously made session forms unreachable. Its
leading `|` is also load-bearing: the following row words are non-reserved, so
the punctuation tells the command parser that another manifest row follows.
Braces, commas and `:=` are parser-hard boundaries around arbitrary Lean terms.
Every stable ID is explicit; source names select checked constants only. -/

declare_syntax_cat preoExportItem
syntax (name := preoExportField) "|" &"field" ident " := " "{"
  &"id" " := " colGt term:51 ","
  &"kind" " := " colGt term:51 ","
  &"carrier" " := " colGt term:51 ","
  &"key" " := " colGt term "}" : preoExportItem
syntax (name := preoExportInvariant) "|" &"invariant" ident " := " "{"
  &"id" " := " colGt term:51 ","
  &"carrier" " := " colGt term:51 ","
  &"codec" " := " colGt term:51 ","
  &"answered" " := " colGt term "}" : preoExportItem
syntax (name := preoExportFuture) "|" &"future" ident " := " "{"
  &"certificate" " := " ident ","
  &"id" " := " colGt term:51 ","
  &"world" " := " colGt term:51 ","
  &"relation" " := " colGt term "}" : preoExportItem
syntax (name := preoExportSession) "|" &"session" ident " := " "{"
  &"id" " := " colGt term:51 ","
  &"plan" " := " colGt term "}" : preoExportItem
syntax (name := preoExportBudget) "|" &"budget" ident
  ppSpace &"for" ppSpace ident " := " "{"
  &"id" " := " colGt term:51 ","
  &"session" " := " colGt term:51 ","
  &"plan" " := " colGt term:51 ","
  &"samePlan" " := " colGt term "}" : preoExportItem

/-- Build one checked declaration bundle from explicit manifest rows, then
emit its canonical artifact/encoding, durable bytes and validated ProjectionV2
view. The validation configuration is explicit and compilation fails unless
the emitted projection validates (including stable-ID uniqueness). -/
syntax (name := preoExport) "preo_export " ident ppSpace &"from" ppSpace ident
  " : " colGt term:51 " := "
  ppLine colGe (&"declaration" " := " "{"
    &"id" " := " colGt term:51 ","
    &"stateType" " := " colGt term:51 ","
    &"schema" " := " colGt term "}")
  (ppLine colGe preoExportItem)* : command

/-- Print the verdict table of a `preo` declaration: every field with its kind
and carrier, every invariant with the field it reads, its verdict, the route
that produced it and the constant carrying the evidence. The verdict column is
computed from those constants at print time, not stored. -/
syntax (name := preoReport) "#preo_report " ident : command

end Uwueave.Preo
