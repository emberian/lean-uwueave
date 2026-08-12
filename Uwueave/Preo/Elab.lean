/-
# Uwueave.Preo.Elab — the elaborator: a `preo` declaration becomes Lean, and
its items become **accumulated facets**.

`Uwueave.Preo.Syntax` holds the grammar and the field kinds;
`Uwueave.Preo.Classification` holds the facet algebra and its invariance
theorem; here is what a declaration turns into and how the facets are reached.

## What fragment 2 changed, structurally

Fragment 1 ran four routes in order and took the **first match**, so an
invariant had exactly one answer and a seam had nowhere to live. The reviewer's
correction — *"SEAM is not a third alternative to free and clash; rules
monotonically add certified facts; prove route-order invariance"* — is
implemented here as three independent **facet families** per item:

  * the **global** family (`Spec.Verdict`) — every cheap route that applies
    contributes, and they cannot disagree (`Preo.verdict_agree`);
  * the **seam** family (`Spec.SegVerdict`) — tried *whether or not* a global
    verdict was found, because a seam is extra structure about a clash rather
    than a competitor to it (`Preo.seam_forces_clash`);
  * the **mergeability** family (`JoinHom.Fourth`) — the `derive` rows' answer,
    a different question with a different subject.

The answer the report prints is `Classification.answer`, reduced out of the
emitted `Classification` constant.

⚠ The one place order still matters operationally is that the expensive
`verdict` tactic is skipped when a cheap route already answered. Be exact about
what licenses that, because the obvious citation is the wrong one:
`run_answer_congr` compares registries with the *same membership*, and skipping
a rule changes the membership. The licence is **`Preo.answerOf_congr`** (and
its consumer `Classification.answer_unique`) — the answer depends only on WHICH
FACET KINDS were reached, so a classification with one more global facet in it
certifies the same thing as one without. `run_answer_congr` is the stronger,
separate statement about reordering.

## What one `preo N where …` emits, in order

For fields `f₁ : k₁ … fₙ : kₙ`, invariants `i₁ … iₘ` and derives `d₁ … d_p`:

```
abbrev  N.fⱼ.Carrier                   := cⱼ                         -- predictable type name
abbrev  N.State                          := c₁ × (c₂ × … cₙ)      -- right-nested
abbrev  N.fⱼ (s : N.State)               := s.2…2.1               -- the projection
example : MergeState N.State             := inferInstance         -- CHECKED, not assumed
theorem N.fⱼ.merge_hom (x y)             : N.fⱼ (x ⊔ y) = N.fⱼ x ⊔ N.fⱼ y := rfl
def     N.fⱼ.plant  : cⱼ → N.State                                -- the section
theorem N.fⱼ.plant_proj / .plant_merge / .surj                    -- its three equations

@[reducible] def N.iₖ : Invariant cⱼ     := fun fⱼ => <predicate>  -- or cᵤ × cᵥ (cross)
def     N.iₖ.verdict  : Verdict N.iₖ                              -- global facets, in
def     N.iₖ.verdict₂ : Verdict N.iₖ                              -- route order
def     N.iₖ.seam     : SegVerdict N.iₖ Seg                       -- seam facet
def     N.iₖ.obligation : Obligation N.iₖ                         -- …or, if NOTHING fired
def     N.iₖ.classification : Classification N.iₖ _               -- ⚠ the row's answer
theorem N.iₖ.onState  : IConfluent (fun s => N.iₖ (N.fⱼ s))       -- FREE rows only
def     N.iₖ.seamOnState : SegVerdict (fun d => N.iₖ (N.fⱼ d)) Seg -- SEAM rows only
def     N.documentSeamLeft / .documentSeamRight                   -- nested lifts
def     N.documentSeamBase : SegVerdict (fun d => N.i₁ … ∧ N.i₂ …) _
def     N.documentSeamFreeₖ                                       -- absorbed FREE rows
def     N.documentSeam                                             -- final seam fold

@[reducible] def N.dₖ.on : cⱼ → T        := fun fⱼ => <expr>
def     N.dₖ : N.State → T               := fun s => N.dₖ.on (N.fⱼ s)
def     N.dₖ.merge : MergeFacet N.dₖ                              -- Fourth + its proof
def     N.dₖ.classification : Classification _ N.dₖ

def     N.q.Raw / .Schema / .Program                              -- Raw.infer witness
def     N.q.Checked / .Type / .Term / .Eval                       -- one typed value
def     N.q.Holes / .Reads / .MergeSafe? / .MonotoneSafe?         -- exact/proof options
def     N.q.buildCache / .update / .updateCache / .update_correct  -- chained incrementality
def     N.q.Reach / .Result / .ResultCarrier / .reportAt           -- checked six-status UI
```

Four of those lines are the point:

  * `N.iₖ.verdict` is a `Spec.Verdict` **value** — it cannot exist without its
    evidence, so a wrong verdict is not a thing this elaborator can print.
  * `N.iₖ.seam` is a `SegVerdict` **value** — it carries the global clash AND
    the segmentation proof, so a row cannot claim "free within an allocation"
    without proving the allocation is a fiber.
  * `N.dₖ.merge` carries a `Fourth.Correct` proof, so a `fromResults` badge is
    an `IncrementallyMergeable` term and a `needsEvidence` badge is a real
    impossibility proof.
  * `N.iₖ.onState` / `N.iₖ.seamOnState` are the field-scoped results read at
    the declared document's scale; their proof arguments are welded to the
    *computed* answer (`iconfluent_of_isFree … rfl`), not to the elaborator's
    opinion of it.
  * `N.documentSeam` is emitted when a declaration has exactly two seam rows on
    distinct fields, wherever those fields sit in the right-nested state. Two
    custom `seamAlong` sections plant each verdict's legal witness in the other
    field; `.andSeams` then forms the pair seam. Finally `.absorbFree` adds each
    FREE row whose legality at the carried clash pair kernel-checks. A free row
    that is false or undecidable there is omitted, never assumed.
  * `N.q.Program` contains a kernel-reduced success witness for `Raw.infer`.
    Every dependency, algebraic certificate, cache result and exact six-status
    report above is computed from that one term. The authored finite reach feeds
    least effect inference; equality is the explicit default future, not an
    assertion that arbitrary environment changes preserve the result.

## The rule registry

**Global family**, all attempted, all accumulated:

  1. **supplied** — the author wrote `:= <term>`; kernel-checked. Reported as
     `supplied`, never as `derived`.
  2. **selection** — `Tactics.SelectionMerge cⱼ` synthesizes, so
     `Catalog.selection_iconfluent` frees *every* invariant over the carrier.
  3. **finite decision** — `Tactics.classifyFinite`, total and decisive both
     ways over a `FinEnum` carrier with a decidable invariant.
  4. **cross-FK** (two-field rows only) — `Spec.pointsAtExisting_iconfluent`
     through `Verdict.cross_free`: referential integrity over grow-only sets.
     *Attempted*, not pattern-matched — the kernel decides whether the row's
     invariant really is that one.
  5. **search** — the `verdict` tactic, run only if 1–4 all missed (the
     invariance note above says exactly which theorem licenses skipping it, and
     which one does not).

**Seam family**, attempted on every one-field row:

  6. **budget seam** — `Preo.budgetSeam B`, the allocation fiber at *any*
     positive budget (`Segmented.budget_segmented` + a generalised clash). One
     rule, and the registry is meant to grow: `Seams.epochSegVerdict`,
     `Seams.schemaSegVerdict` and `SeamAlgebra.flagDaySegVerdict` are the next
     three, each pinned to a concrete world that no `preo` surface can spell
     yet.
  7. **pin self-seam** — the `Spec.atMostOneClash` ceiling over `GSet Nat`,
     coordinated on the pin set itself via `SegVerdict.selfSeam`. A final
     fallback applies the same conservative self seam to any one-field global
     clash the registry already certified; free verdicts cannot pass its
     `isFree = false` premise.
  8. **document composition** — with exactly two seam rows on distinct fields,
     lift both through arbitrary right-nested projection paths (`seamAlong`),
     conjoin them (`andSeams`), then absorb every FREE row whose truth at both
     carried clash documents is discharged by kernel decision (`absorbFree`).
     The emitted `N.documentSeam` coordinates on the pair of seam values and
     carries the left row's concrete global clash throughout.

**Mergeability family**, attempted on every `derive` row: `verdict_exists`,
`verdict_restrict`, `verdict_high`, `verdict_image` (`fromResults`) and
`verdict_card` (`needsEvidence`). Each is a closed theorem tried *by
typechecking against the emitted computation*, so a shape it does not know is a
refusal and never a guess.

Otherwise: an `Obligation`, naming the routes tried and what would close it.

⚠ And whichever routes ran, every emitted facet is checked against the tree's
axiom floor (`propext · Classical.choice · Quot.sound`) **before a row
exists** — a `sorry`-backed `Verdict` prints exactly like a real one.

## What it refuses, loudly

  * an unknown built-in field kind — the six are named in the error;
  * a `custom` field without its explicit planting seed or without an existing
    `MergeState` instance;
  * a field kind with a missing or surplus argument;
  * an invariant mentioning **no** field (it would have no carrier);
  * an invariant mentioning **three or more** fields — the cross machinery is
    binary (`Spec.Verdict.cross` is over `A × B`), and a ternary lift is not
    in the tree;
  * a `derive` reading zero or more than one field — the mergeability transport
    (`Preo.mergeability_comp`) is along **one** projection;
  * a malformed, out-of-range, ill-typed or raw-opaque `typed derive` —
    `Raw.infer` must return a checked term before any analysis or row exists;
  * a declaration with no fields.
-/
import Uwueave.Preo.Classification
import Uwueave.Preo.ArtifactDurable
import Uwueave.Preo.Future
import Uwueave.Preo.Incremental
import Uwueave.Preo.ProjectionV2
import Uwueave.Preo.ResultProgram
import Uwueave.Protocol
import Uwueave.SeamAlgebra

namespace Uwueave.Preo

open Lean Elab Command Term Meta
open Uwueave Uwueave.Catalog Uwueave.Spec

/-! ## §1. Small helpers -/

/-- A syntax node as a one-line string, for the report. -/
private def pp (s : Syntax) : String :=
  (((s.reprint.getD "?").replace "\n" " ").replace "  " " ").trimAscii.toString

/-- Does this type have an instance? Used only to *choose a route*; the route
then emits a term that is checked independently, so a wrong answer here can
only cost a worse error message. -/
private def canSynth (tyStx : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyStx
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← Meta.trySynthInstance ty with
      | .some _ => pure true
      | _ => pure false
    catch _ => pure false

/-- Does a fully written type reduce to the checked-certificate family? This
recognises reducible aliases but deliberately does not infer a certificate
from state, a future name, or the proof term's result type. -/
private def isCheckedCertificateType (tyStx : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars ty
      let ty ← withDefault <| whnf ty
      pure (ty.getAppFn.constName? ==
        some ``Uwueave.Preo.Future.CheckedCertificate)
    catch _ => pure false

/-- Does a source term have `Protocol.Elaboration` at the head of its reduced
type? Export uses this positive check rather than guessing from a source name:
a composed `ProfilePlan` is intentionally not an ordinary checked session. -/
private def isProtocolElaborationTerm (termStx : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let value ← Term.elabTerm termStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars (← inferType value)
      let ty ← withDefault <| whnf ty
      pure (ty.getAppFn.constName? == some ``Uwueave.Protocol.Elaboration)
    catch _ => pure false

/-- Reduce a `Classification`'s **accumulated answer**. This is how the report
reads a row: not off a stored string, not off one verdict constant, but off the
`Classification.answer` of the facets the registry certified — the same
function `Preo.run_answer_congr` proves order-independent.

Outer `none` means the term did not reduce (a bug worth reporting); inner
`none` means the row certified no confluence answer, which is UNRESOLVED and is
*not* FREE. -/
private def readAnswer (c : Name) : CommandElabM (Option (Option Bool)) :=
  liftTermElabM do
    try
      let e ← mkAppM ``Uwueave.Preo.Classification.answer #[← mkConstWithFreshMVarLevels c]
      let r ← withDefault <| whnf e
      if r.isAppOfArity ``Option.none 1 then return some none
      if r.isAppOfArity ``Option.some 2 then
        let b ← withDefault <| whnf r.appArg!
        if b.isConstOf ``Bool.true then return some (some true)
        if b.isConstOf ``Bool.false then return some (some false)
      return none
    catch _ => return none

/-- Reduce a `Classification`'s **mergeability answer** (`JoinHom.Fourth`). -/
private def readMergeAnswer (c : Name) : CommandElabM (Option (Option String)) :=
  liftTermElabM do
    try
      let e ← mkAppM ``Uwueave.Preo.Classification.mergeAnswer
        #[← mkConstWithFreshMVarLevels c]
      let r ← withDefault <| whnf e
      if r.isAppOfArity ``Option.none 1 then return some none
      if r.isAppOfArity ``Option.some 2 then
        let b ← withDefault <| whnf r.appArg!
        if b.isConstOf ``Uwueave.JoinHom.Fourth.fromResults then
          return some (some "fromResults")
        if b.isConstOf ``Uwueave.JoinHom.Fourth.needsEvidence then
          return some (some "needsEvidence")
      return none
    catch _ => return none

/-- Emit a command, and roll the environment (and the message log) back if it
did not go through cleanly. This is how a *route* may be attempted rather than
merely probed — `by verdict` cannot be predicted without running it, and neither
can "does `budgetSeam` typecheck at this invariant"; a route that does not apply
must leave no trace, not a logged error and a `sorry`-bodied definition.

Only `env` and `messages` are restored: rolling back the whole command state
would rewind the macro-scope counter, and two commands sharing a scope is a
hygiene bug waiting to be blamed on something else.

On failure it returns *what went wrong*, so an `Obligation` can quote the
classifier's own words rather than a generic shrug. -/
private def tryEmit (cmd : Syntax) : CommandElabM (Except String Unit) := do
  let savedEnv ← getEnv
  let savedMsgs := (← get).messages
  let complain : CommandElabM String := do
    let fresh := (← get).messages.toList.filter (·.severity == .error)
    match fresh.reverse.head? with
    | some m => return (← m.data.toString)
    | none => return "the route did not apply"
  let restore : CommandElabM Unit :=
    modify fun st => { st with env := savedEnv, messages := savedMsgs }
  try
    elabCommand cmd
    if (← get).messages.hasErrors then
      let why ← complain
      restore
      return .error why
    return .ok ()
  catch e =>
    let why ← e.toMessageData.toString
    restore
    return .error why

/-- The axioms a constant depends on, minus Lean's own floor. -/
private def offFloor (c : Name) : CommandElabM (Array Name) := do
  let axs ← collectAxioms c
  return axs.filter fun a =>
    !([``propext, ``Classical.choice, ``Quot.sound].contains a)

/-- ⚠ **Every emitted facet answers to the tree's floor before a row exists.**
This is what makes the *supplied* routes safe: a `sorry`-backed `Verdict`,
`SegVerdict` or `Fourth.Correct` prints exactly like a real one, and no amount
of reading the table would tell. -/
private def floorCheck (at? : Syntax) (what : String) (c : Name) : CommandElabM Unit := do
  let stray ← offFloor c
  unless stray.isEmpty do
    throwErrorAt at? "preo: the {what} `{c}` depends on \
      {String.intercalate ", " (stray.toList.map toString)} — outside the \
      axiom floor `propext · Classical.choice · Quot.sound` that `#audit_floor` \
      holds the whole tree to. A `sorry` here is a facet with a hole in it, and \
      `native_decide` is the compiled evaluator rather than the kernel; a row \
      printed off either would be exactly the failure this table exists to make \
      impossible. No row is recorded."

/-- The carrier type of a built-in field kind. Six kinds, each an existing
catalog or `Segmented` type with a proved `MergeState`; custom carriers are
handled separately because their type is the author's term. -/
private def carrierOf (kind : Ident) (arg? : Option Term) : CommandElabM Term := do
  let k := kind.getId.toString
  match k, arg? with
  | "GrowSet", some a => `(Uwueave.Catalog.GSet $a)
  | "Slot",    some a => `(Uwueave.Preo.Slot $a)
  | "Escrow",  some a => `(Uwueave.Catalog.Escrow $a)
  | "Quota",   some a => `(Uwueave.Preo.Quota $a)
  | "Counter", none   => `(Nat)
  | "LWW",     none   => `(Uwueave.Catalog.LWW)
  | "GrowSet", none | "Slot", none | "Escrow", none | "Quota", none =>
      throwErrorAt kind "preo: field kind `{k}` needs an element type — write \
        `{k} Nat`, `{k} (Fin 3)`, … (the carrier is a map out of it, so the \
        elaborator cannot guess one)."
  | "Counter", some _ =>
      throwErrorAt kind "preo: `Counter` takes no argument — its carrier is \
        `Nat` under `max` (`Catalog.instMergeStateNatMax`). For a per-replica \
        counter use `Escrow ι`."
  | "LWW", some _ =>
      throwErrorAt kind "preo: `LWW` takes no argument — `Catalog.LWW` is a \
        concrete (timestamp, value) register. Put the key before the colon: \
        `field <name> per <Key> : LWW`."
  | _, _ =>
      throwErrorAt kind "preo: unknown built-in field kind `{k}`. Use one of six: \
        `GrowSet α` (grow-only set), `Slot α` (a grow-only set carrying a \
        uniqueness ceiling), `Escrow ι` (per-replica quota spend), `Quota ι` \
        (allocation PLUS spend — the carrier the seam lives on), `Counter` \
        (`Nat` under max), `LWW` (last-writer-wins register). Each supplies a \
        carrier and a proved `MergeState` from `Uwueave.Catalog` or \
        `Uwueave.Segmented`. For an application carrier write \
        `field <name> : (custom <Carrier>) := <seed>`; its `MergeState` must \
        already exist and its seed is never inferred."

/-- A canonical planting value for each built-in kind — the *other* fields'
contents when the elaborator plants a field-scale state in a document. This is
a well-typed structural seed, not a proof of an arbitrary invariant (the zero
quota, importantly, is not legal at budget 10). Custom carriers never enter
this function: their author must supply the corresponding value explicitly. -/
private def defaultOf (kind : Ident) (arg? : Option Term) : CommandElabM Term := do
  let k := kind.getId.toString
  match k, arg? with
  | "GrowSet", some a => `((fun _ => false : Uwueave.Catalog.GSet $a))
  | "Slot",    some a => `((fun _ => false : Uwueave.Preo.Slot $a))
  | "Escrow",  some a => `((fun _ => 0 : Uwueave.Catalog.Escrow $a))
  | "Quota",   some a => `((((fun _ => 0), (fun _ => 0)) : Uwueave.Preo.Quota $a))
  | "Counter", _      => `((0 : Nat))
  | "LWW",     _      => `((⟨0, 0⟩ : Uwueave.Catalog.LWW))
  | _, _ => throwErrorAt kind "preo: internal — no default for kind `{k}`"

/-- Every field name mentioned in a term. This is the *entire* syntactic
analysis the elaborator performs on a predicate or a derive body: which field it
reads decides the carrier the item is classified over. Everything else is left
to Lean.

The root component is what counts, because dot notation arrives as **one**
identifier: `title.ts` is a single ident named `title.ts`.

⚠ It is a syntactic over-approximation, deliberately: an occurrence shadowed by
an inner binder still counts as a mention. That can misattribute a row or refuse
a declaration that would have been fine — both loud — but it cannot produce a
wrong facet, because whatever carrier it picks, the item is then classified *on
that carrier* by a route that ends in a checked term. -/
private partial def mentions (fields : Array Name) (stx : Syntax) : Array Name :=
  go stx #[]
where
  go (s : Syntax) (acc : Array Name) : Array Name :=
    if s.isIdent then
      let n := s.getId.eraseMacroScopes
      let n := if fields.contains n then n else n.getRoot
      if fields.contains n && !acc.contains n then acc.push n else acc
    else
      s.getArgs.foldl (fun a c => go c a) acc

/-! ## §2. Building state terms -/

/-- The projection path to field `i` of `n`, as syntax over `s`. -/
private def projPath (i n : Nat) : CommandElabM Term := do
  let mut e : Term ← `(s)
  for _ in [0:i] do
    e ← `($e.2)
  if i + 1 < n then e ← `($e.1)
  return e

/-- Right-nest a list of component terms into a state term. -/
private def nest (ts : Array Term) : CommandElabM Term := do
  let n := ts.size
  let mut e := ts[n - 1]!
  for k in [0:n-1] do
    e ← `(($(ts[n - 2 - k]!), $e))
  return e

/-- **The section for field `i`**: a closed function taking a field value to a
document holding it, with `defaultOf` in every other slot. Its two equations
(`π ∘ ι = id` and `π (ι a ⊔ ι b) = a ⊔ b`) are both `rfl`, because the product
merge is componentwise by definition. -/
private def plantFn (i n : Nat) (defs : Array Term) : CommandElabM Term := do
  let mut ts : Array Term := #[]
  for k in [0:n] do
    if k == i then ts := ts.push (← `(v)) else ts := ts.push defs[k]!
  let body ← nest ts
  `(fun v => $body)

/-- The section for a **pair** of fields `i < j` — the cross-field rows' plant,
taking the product value apart. -/
private def plantFn₂ (i j n : Nat) (defs : Array Term) : CommandElabM Term := do
  let mut ts : Array Term := #[]
  for k in [0:n] do
    if k == i then ts := ts.push (← `(v.1))
    else if k == j then ts := ts.push (← `(v.2))
    else ts := ts.push defs[k]!
  let body ← nest ts
  `(fun v => $body)

/-! ## §3. The declaration elaborator -/

/-- One certified facet, as the elaborator tracks it: the constant carrying it
and the route label the report prints. -/
private structure Fired where
  const : Ident
  route : String
  cite : String
  deriving Inhabited

/-- A field-scale seam retained until the declaration is complete, so the
two-field document rule can compose one seam from each component. -/
private structure FiredSeam where
  field : Nat
  inv : Ident
  const : Ident
  segTy : Term
  deriving Inhabited

/-- The products of classifying one invariant, including declaration-scale
facets retained for the document-seam fold. -/
private structure InvariantResult where
  row : Row
  seam? : Option FiredSeam
  freeOnState? : Option Ident
  deriving Inhabited

/-- The two field spellings erase to the same checked ingredients before state
construction. `custom` is retained only so its explicit seed and merge
instance can receive named, floor-checked constants. -/
private structure ParsedField where
  name : Ident
  key? : Option Term
  baseCarrier : Term
  baseDefault : Term
  kindLabel : String
  custom : Bool
  deriving Inhabited

@[command_elab preoDecl]
def elabPreoDecl : CommandElab := fun stx => do
  let `(command| preo $declId:ident where
      $fs:preoField* $invs:preoInv* $futures:preoFuture*
      $typedDers:preoTypedDerive* $ders:preoDerive*
      $protocols:preoProtocol* $sessions:preoSession*) := stx
    | throwError "preo: malformed declaration"
  let declName := declId.getId
  let ns ← getCurrNamespace
  let fullDecl := ns ++ declName
  if fs.isEmpty then
    throwErrorAt declId "preo: `{declName}` declares no fields — a state type \
      with no fields has nothing to classify. Add `field <name> : <kind>`."
  -- §3.1 Fields: name, kind syntax, carrier, default.
  let mut fieldIdents : Array Ident := #[]
  let mut fieldKinds : Array String := #[]
  let mut fieldKeys : Array (Option Term) := #[]
  let mut carriers : Array Term := #[]
  let mut defaults : Array Term := #[]
  let mut customFields : Array Bool := #[]
  for f in fs do
    let `(preoField| field $nm:ident $[per $key:term]? : $body:preoFieldBody) := f
      | throwErrorAt f "preo: malformed field"
    let parsed : ParsedField ← match body with
      | `(preoFieldBody| (custom $carrierTy:term) := $seed:term) =>
        pure (⟨nm, key, carrierTy, seed, "custom " ++ pp carrierTy, true⟩ :
          ParsedField)
      | `(preoFieldBody| $k:ident $[$a:term]?) =>
        pure (⟨nm, key, ← carrierOf k a, ← defaultOf k a,
          pp k ++ (a.map (fun t => " " ++ pp t)).getD "", false⟩ : ParsedField)
      | _ => throwErrorAt body "preo: malformed field body"
    let nm := parsed.name
    let key := parsed.key?
    if fieldIdents.any (·.getId == nm.getId) then
      throwErrorAt nm "preo: duplicate field `{nm.getId}`"
    let carrier : Term ← match key with
      | none => pure parsed.baseCarrier
      | some key => `($key → $(parsed.baseCarrier))
    let default : Term ← match key with
      | none => pure parsed.baseDefault
      | some key => `(fun (_ : $key) => $(parsed.baseDefault))
    unless ← canSynth (← `(Uwueave.MergeState $carrier)) do
      throwErrorAt f "preo: field `{nm.getId}` has carrier `{pp carrier}`, but \
        no `MergeState` instance is available. A custom carrier reuses an \
        application merge model; the seed supplies a planting value, not a \
        merge operation. Define and prove the instance before this declaration."
    fieldIdents := fieldIdents.push nm
    fieldKinds := fieldKinds.push
      ((key.map (fun key => "per " ++ pp key ++ " : ")).getD ""
        ++ parsed.kindLabel)
    fieldKeys := fieldKeys.push key
    carriers := carriers.push carrier
    defaults := defaults.push default
    customFields := customFields.push parsed.custom
  let n := carriers.size
  let fieldNames := fieldIdents.map (·.getId)
  -- Every field receives a stable type path. Custom fields additionally expose
  -- the mandatory seed and the reused merge instance as named checked terms.
  for i in [0:n] do
    let fname := fieldIdents[i]!.getId
    let carrierId := mkIdent (declName ++ (fname ++ `Carrier))
    elabCommand (← `(command|
      /-- The checked carrier of this field, named for manifests and adapters. -/
      abbrev $carrierId : Type := $(carriers[i]!)))
    if customFields[i]! then
      let seedId := mkIdent (declName ++ (fname ++ `seed))
      elabCommand (← `(command|
        /-- The author-supplied planting seed for this application carrier. -/
        def $seedId : $carrierId := $(defaults[i]!)))
      floorCheck (fieldIdents[i]!) "custom field seed" (fullDecl ++ (fname ++ `seed))
      defaults := defaults.set! i seedId
      let mergeId := mkIdent (declName ++ (fname ++ `mergeState))
      elabCommand (← `(command|
        /-- The application's existing merge model, checked and retained. -/
        abbrev $mergeId : Uwueave.MergeState $carrierId := inferInstance))
      floorCheck (fieldIdents[i]!) "custom field MergeState"
        (fullDecl ++ (fname ++ `mergeState))
  -- §3.2 The state type: carriers, right-nested.
  let mut stateTy : Term := carriers[n - 1]!
  for i in [0:n-1] do
    stateTy ← `($(carriers[n - 2 - i]!) × $stateTy)
  let stateId := mkIdent (declName ++ `State)
  elabCommand (← `(command|
    /-- The declared state: the field carriers, right-nested. Its `MergeState`
    is inherited from the product and pointwise instances — the `example` below
    is the check that it really is. -/
    abbrev $stateId : Type := $stateTy))
  -- §3.3 Accessors, the checked `MergeState`, each field's merge homomorphism
  -- and each field's SECTION (the plant) with its three equations.
  for i in [0:n] do
    let fname := fieldIdents[i]!.getId
    let accId := mkIdent (declName ++ fname)
    let body ← projPath i n
    elabCommand (← `(command| abbrev $accId (s : $stateId) : $(carriers[i]!) := $body))
    let homId := mkIdent (declName ++ (fname ++ `merge_hom))
    elabCommand (← `(command|
      theorem $homId (x y : $stateId) :
          $accId (Uwueave.MergeState.merge x y)
            = Uwueave.MergeState.merge ($accId x) ($accId y) := rfl))
    let plantId := mkIdent (declName ++ (fname ++ `plant))
    let pfn ← plantFn i n defaults
    elabCommand (← `(command|
      /-- A document holding the given field value, and the declared planting
      seed in every other field — the section the seam and mergeability
      transports need. Invariant legality is checked where a transport uses it,
      never inferred from the seed. -/
      def $plantId : $(carriers[i]!) → $stateId := $pfn))
    elabCommand (← `(command|
      theorem $(mkIdent (declName ++ (fname ++ `plant_proj)))
          (a : $(carriers[i]!)) : $accId ($plantId a) = a := rfl))
    elabCommand (← `(command|
      theorem $(mkIdent (declName ++ (fname ++ `plant_merge)))
          (a b : $(carriers[i]!)) :
          $accId (Uwueave.MergeState.merge ($plantId a) ($plantId b))
            = Uwueave.MergeState.merge a b := rfl))
    elabCommand (← `(command|
      theorem $(mkIdent (declName ++ (fname ++ `surj)))
          : ∀ a : $(carriers[i]!), ∃ s : $stateId, $accId s = a :=
        fun a => ⟨$plantId a, rfl⟩))
  elabCommand (← `(command| example : Uwueave.MergeState $stateId := inferInstance))
  let mut rows : Array Row := #[]
  for i in [0:n] do
    rows := rows.push
      { decl := fullDecl, kind := .field, name := fieldIdents[i]!.getId.toString
        detail := fieldKinds[i]!, detail₂ := pp carriers[i]!
        evidence := fullDecl ++ (fieldIdents[i]!.getId ++ `merge_hom)
        isObligation := false, cite := "MergeState by inferInstance (checked)"
        seamCite := "" }
  let mut declarationSeams : Array FiredSeam := #[]
  let mut declarationFrees : Array Ident := #[]
  -- §3.4 Invariants.
  for inv in invs do
    let `(preoInv| invariant $nm : $pred $[:= $supplied]?) := inv
      | throwErrorAt inv "preo: malformed invariant"
    let used := mentions fieldNames pred
    if used.isEmpty then
      throwErrorAt nm "preo: invariant `{nm.getId}` mentions no field of \
        `{declName}` — there is no carrier to classify it over. Fields are: \
        {String.intercalate ", " (fieldNames.toList.map toString)}."
    if used.size > 2 then
      throwErrorAt nm "preo: invariant `{nm.getId}` mentions {used.size} fields \
        ({String.intercalate ", " (used.toList.map toString)}). The cross-field \
        machinery is BINARY — `Spec.Verdict.cross` classifies a relation over \
        `A × B`, and no ternary lift exists in the tree. Split it, or earn the \
        ternary verdict by hand against the joint merge."
    -- The fields this row reads, in DECLARATION order (so the product's `.1`
    -- and `.2` match the schema the author wrote, not the traversal order of
    -- their predicate).
    let mut idxs : Array Nat := #[]
    for u in used do
      let some k := fieldNames.findIdx? (· == u) | throwErrorAt nm "preo: internal"
      idxs := idxs.push k
    if idxs.size == 2 && idxs[0]! > idxs[1]! then
      idxs := #[idxs[1]!, idxs[0]!]
    let isCross := idxs.size == 2
    let invId := mkIdent (declName ++ nm.getId)
    let carrier : Term ←
      if isCross then `($(carriers[idxs[0]!]!) × $(carriers[idxs[1]!]!))
      else pure carriers[idxs[0]!]!
    let readsStr := String.intercalate " × " (idxs.toList.map (fun k =>
      fieldNames[k]!.toString))
    let result : InvariantResult ← withRef nm do
      -- The invariant, with the FIELD NAME(S) as the binder(s): the predicate
      -- reads exactly as written. `@[reducible]` so `DecidablePred` synthesis
      -- can see through the definition.
      if isCross then
        let fA := fieldIdents[idxs[0]!]!
        let fB := fieldIdents[idxs[1]!]!
        elabCommand (← `(command|
          @[reducible] def $invId : Uwueave.Invariant $carrier :=
            fun p => (fun $fA => fun $fB => $pred) p.1 p.2))
      else
        elabCommand (← `(command|
          @[reducible] def $invId : Uwueave.Invariant $carrier :=
            fun $(fieldIdents[idxs[0]!]!) => $pred))
      -- ── The GLOBAL facet family. Every route that applies contributes; they
      -- cannot disagree (`Preo.verdict_agree`), which is the licence for
      -- skipping the expensive search when a cheap route already answered.
      let mut globals : Array Fired := #[]
      let mut tacticSaid : String := ""
      let vBase := nm.getId ++ `verdict
      -- Several global routes may fire on one row; they are numbered in route
      -- order and `Preo.verdict_agree` says they cannot disagree.
      let vSuffix : Array String := #["", "₂", "₃", "₄", "₅", "₆"]
      let mkVId : Nat → Ident := fun k =>
        mkIdent (declName ++ vBase.appendAfter vSuffix[k]!)
      if let some ev := supplied then
        let vId := mkVId globals.size
        elabCommand (← `(command|
          def $vId : Uwueave.Spec.Verdict $invId := $ev))
        let cite := "author-supplied, kernel-checked: " ++ pp ev
        globals := globals.push { const := vId, route := "supplied", cite := cite }
      if ← canSynth (← `(Uwueave.Tactics.SelectionMerge $carrier)) then
        let vId := mkVId globals.size
        let cite := "Catalog.selection_iconfluent (the merge picks a side)"
        match ← tryEmit (← `(command|
            def $vId : Uwueave.Spec.Verdict $invId :=
              Uwueave.Spec.Verdict.free
                (Uwueave.Catalog.selection_iconfluent
                  Uwueave.Tactics.SelectionMerge.selects $invId))) with
        | .ok _ => globals := globals.push { const := vId, route := "selection", cite := cite }
        | .error _ => pure ()
      if (← canSynth (← `(Uwueave.Tactics.FinEnum $carrier)))
          && (← canSynth (← `(DecidablePred $invId))) then
        let vId := mkVId globals.size
        let cite := "Tactics.classifyFinite (total; classifyFinite_isFree_iff)"
        match ← tryEmit (← `(command|
            def $vId : Uwueave.Spec.Verdict $invId :=
              Uwueave.Tactics.classifyFinite $invId)) with
        | .ok _ => globals := globals.push { const := vId, route := "classifyFinite", cite := cite }
        | .error _ => pure ()
      if isCross && fieldKeys[idxs[0]!]!.isNone && fieldKeys[idxs[1]!]!.isSome then
        let vId := mkVId globals.size
        let cite := "Confluence.keyed_cross_iconfluent applied to \
          Spec.pointsAtExisting_iconfluent (referential integrity for every key, \
          earned once against the JOINT merge and lifted pointwise)"
        match ← tryEmit (← `(command|
            def $vId : Uwueave.Spec.Verdict $invId :=
              Uwueave.Spec.Verdict.free
                (Uwueave.keyed_cross_iconfluent
                  (R := Uwueave.Spec.PointsAtExisting)
                  Uwueave.Spec.pointsAtExisting_iconfluent))) with
        | .ok _ => globals := globals.push { const := vId, route := "keyed-cross-FK", cite := cite }
        | .error _ => pure ()
      if isCross then
        let vId := mkVId globals.size
        let cite := "Spec.pointsAtExisting_iconfluent through Verdict.cross_free \
          (referential integrity over grow-only sets, earned against the JOINT merge \
          — no lift produced it and none could)"
        match ← tryEmit (← `(command|
            def $vId : Uwueave.Spec.Verdict $invId :=
              Uwueave.Spec.Verdict.cross_free Uwueave.Spec.pointsAtExisting_iconfluent)) with
        | .ok _ => globals := globals.push { const := vId, route := "cross-FK", cite := cite }
        | .error _ => pure ()
      if globals.isEmpty then
        let vId := mkVId 0
        let cite := "Tactics.verdict (classify's routes; the term it emits is kernel-checked)"
        match ← tryEmit (← `(command|
            def $vId : Uwueave.Spec.Verdict $invId := by verdict)) with
        | .ok _ => globals := globals.push { const := vId, route := "verdict tactic", cite := cite }
        | .error why => tacticSaid := why
      for g in globals do
        floorCheck nm "verdict" (ns ++ g.const.getId)
      -- ── The SEAM facet family. Tried WHETHER OR NOT a global verdict was
      -- found: a seam is additional structure about a clashing invariant, not
      -- a competing answer (`Preo.seam_forces_clash`).
      let mut seam? : Option (Ident × Term × String) := none
      if !isCross then
        let seamId := mkIdent (declName ++ (nm.getId ++ `seam))
        match ← tryEmit (← `(command|
            def $seamId : Uwueave.Spec.SegVerdict $invId (Bool → Nat) :=
              Uwueave.Preo.budgetSeam _ (by decide))) with
        | .ok _ =>
            floorCheck nm "seam verdict" (fullDecl ++ (nm.getId ++ `seam))
            seam? := some (seamId, ← `((Bool → Nat)),
              "FREE within the allocation (Segmented.budget_segmented); the seam is \
               the allocation `Prod.fst`, so spends never coordinate and only a \
               RE-ALLOCATION crosses this seam; scheduling any meeting requires \
               explicit demands. Globally refuted by the carried clash \
               (Preo.budget_not_iconfluent_at).")
        | .error _ => pure ()
        -- The pins-side seam used by `WeaveState.docSeam`: the whole pin set
        -- is the coordination key. This exact-Nat rule reaches the unbounded
        -- ceiling that neither finite decision nor the search tactic can.
        if seam?.isNone then
          match ← tryEmit (← `(command|
              def $seamId : Uwueave.Spec.SegVerdict $invId $carrier :=
                Uwueave.Spec.SegVerdict.selfSeam
                  Uwueave.Spec.atMostOneClash rfl)) with
          | .ok _ =>
              floorCheck nm "seam verdict" (fullDecl ++ (nm.getId ++ `seam))
              seam? := some (seamId, carrier,
                "FREE only while the entire field is fixed \
                 (SegVerdict.selfSeam on Spec.atMostOneClash). This is the \
                 conservative pin seam: every pin-set change coordinates; \
                 the carried singleton/singleton clash refutes global freedom.")
          | .error _ => pure ()
        -- Any independently certified clash admits the same conservative
        -- upper bound. This does not guess a clash: `rfl` must show that the
        -- already-emitted verdict is a clash before `selfSeam` will elaborate.
        if seam?.isNone && !globals.isEmpty then
          match ← tryEmit (← `(command|
              def $seamId : Uwueave.Spec.SegVerdict $invId $carrier :=
                Uwueave.Spec.SegVerdict.selfSeam $(globals[0]!.const) rfl)) with
          | .ok _ =>
              floorCheck nm "seam verdict" (fullDecl ++ (nm.getId ++ `seam))
              seam? := some (seamId, carrier,
                "FREE only while the entire field is fixed \
                 (SegVerdict.selfSeam on the row's certified clash). This is \
                 a sound conservative upper bound, not a claim that no coarser \
                 seam exists.")
          | .error _ => pure ()
      -- A seam entails the clash, so a row with a seam and no global route
      -- still gets its `Verdict` — demoted from the seam it already proved.
      if globals.isEmpty then
        if let some (seamId, _, _) := seam? then
          let vId := mkVId 0
          elabCommand (← `(command|
            def $vId : Uwueave.Spec.Verdict $invId :=
              Uwueave.Spec.SegVerdict.toClash $seamId))
          let cite := "Spec.SegVerdict.toClash — the seam's own carried clash \
            (Preo.seam_forces_clash: a seam FORCES this column to ESCALATES, it \
            never competes with it)"
          globals := globals.push { const := vId, route := "seam⇒clash", cite := cite }
          floorCheck nm "verdict" (ns ++ vId.getId)
      -- ── Nothing fired at all: an Obligation, and never a guess.
      let mut oblId? : Option Ident := none
      if globals.isEmpty && seam?.isNone then
        let hasEnum ← canSynth (← `(Uwueave.Tactics.FinEnum $carrier))
        let enumNote :=
          if hasEnum then
            "the carrier enumerates, so `classifyFinite` was blocked on decidability \
             rather than on the carrier (an unbounded `∀ n : Nat` is the usual cause); "
          else
            "the carrier has neither `SelectionMerge` (which would free every invariant \
             over it) nor `FinEnum` (which would let `classifyFinite` decide); "
        let seamNote :=
          if isCross then "no seam rule is tried on a cross-field row (the registry's \
            entries are single-carrier fibers); "
          else "the seam registry (`Preo.budgetSeam`, the pin ceiling, and the \
            certified-clash self seam) did not typecheck at this invariant; "
        let why :=
          enumNote ++ seamNote ++ "and `verdict` said: " ++ tacticSaid.take 400 ++
          " — DISCHARGE by supplying evidence with `:= <term>` (a catalog verdict such \
           as `Spec.atMostOneClash`, or a hand proof), or by restating the field over \
           a finite index type."
        let oId := mkIdent (declName ++ (nm.getId ++ `obligation))
        elabCommand (← `(command|
          def $oId : Uwueave.Preo.Obligation $invId where
            invName := $(Syntax.mkStrLit nm.getId.toString)
            onField := $(Syntax.mkStrLit readsStr)
            tried := ["selection (Catalog.selection_iconfluent)",
                      "finite decision (Tactics.classifyFinite)",
                      "cross-FK (Spec.pointsAtExisting_iconfluent)",
                      "search (the `verdict` tactic)",
                      "seam (Preo.budgetSeam)",
                      "pin/self seam (SegVerdict.selfSeam)"]
            discharge := $(Syntax.mkStrLit why)))
        oblId? := some oId
      -- ── The accumulated Classification. Every verdict answer the report
      -- prints is reduced out of THIS constant.
      let classId := mkIdent (declName ++ (nm.getId ++ `classification))
      let gList ← `([$(globals.map (·.const)),*])
      let sList : Term ← match seam? with
        | none => `(([] : List (Uwueave.Preo.SeamFacet $invId)))
        | some (sId, segTy, reading) =>
            `([({ Seg := $segTy, verdict := $sId,
                  reading := $(Syntax.mkStrLit reading) } :
                Uwueave.Preo.SeamFacet $invId)])
      let oList : Term ← match oblId? with
        | none => `(([] : List (Uwueave.Preo.Obligation $invId)))
        | some oId => `([$oId])
      elabCommand (← `(command|
        /-- The row's accumulated facets. `#preo_report` reduces its `.answer`;
        nothing about the verdict is stored as text. -/
        def $classId : Uwueave.Preo.Classification $invId (fun _ : $carrier => ()) where
          global := $gList
          seams := $sList
          mergeability := []
          obligations := $oList))
      let classFull := fullDecl ++ (nm.getId ++ `classification)
      -- ── Document-scale readings, welded to the COMPUTED answer.
      let ans ← readAnswer classFull
      let mut freeOnState? : Option Ident := none
      if ans == some (some true) then
        let onStateId := mkIdent (declName ++ (nm.getId ++ `onState))
        if isCross then
          let accA := mkIdent (declName ++ fieldNames[idxs[0]!]!)
          let accB := mkIdent (declName ++ fieldNames[idxs[1]!]!)
          match ← tryEmit (← `(command|
            theorem $onStateId :
                Uwueave.IConfluent (S := $stateId) (fun s => $invId ($accA s, $accB s)) :=
              Uwueave.Preo.proj_iconfluent (π := fun s : $stateId => ($accA s, $accB s))
                (fun _ _ => rfl)
                (Uwueave.Tactics.iconfluent_of_isFree
                  (v := $(globals[0]!.const)) rfl))) with
          | .ok _ => freeOnState? := some onStateId
          | .error _ => pure ()
        else
          let accId := mkIdent (declName ++ fieldNames[idxs[0]!]!)
          let homId := mkIdent (declName ++ (fieldNames[idxs[0]!]! ++ `merge_hom))
          match ← tryEmit (← `(command|
            theorem $onStateId :
                Uwueave.IConfluent (S := $stateId) (fun s => $invId ($accId s)) :=
              Uwueave.Preo.proj_iconfluent $homId
                (Uwueave.Tactics.iconfluent_of_isFree
                  (v := $(globals[0]!.const)) rfl))) with
          | .ok _ => freeOnState? := some onStateId
          | .error _ => pure ()
      if let some (seamId, segTy, _) := seam? then
        let fname := fieldNames[idxs[0]!]!
        let accId := mkIdent (declName ++ fname)
        let homId := mkIdent (declName ++ (fname ++ `merge_hom))
        let plantId := mkIdent (declName ++ (fname ++ `plant))
        let projEq := mkIdent (declName ++ (fname ++ `plant_proj))
        let mergeEq := mkIdent (declName ++ (fname ++ `plant_merge))
        let _ ← tryEmit (← `(command|
          /-- ⚠ The row's seam, read at the WHOLE declared document: coordinate
          only when this field's segment changes, and a same-segment sync can
          move nothing else. -/
          def $(mkIdent (declName ++ (nm.getId ++ `seamOnState))) :
              Uwueave.Spec.SegVerdict (S := $stateId)
                (fun d => $invId ($accId d)) $segTy :=
            Uwueave.Preo.seamAlong $accId $homId $plantId $projEq $mergeEq $seamId))
      let routes := String.intercalate " · " (globals.toList.map (·.route))
        ++ (if seam?.isSome then " · seam" else "")
      let r : Row :=
        { decl := fullDecl, kind := if isCross then .cross else .invariant
          name := nm.getId.toString
          detail := readsStr
          detail₂ := if routes.isEmpty then "—" else routes
          evidence := classFull
          isObligation := oblId?.isSome
          cite :=
            if let some o := oblId? then
              "UNRESOLVED — " ++ (globals.toList.map (·.cite)).foldl (· ++ · ) ""
                ++ s!"see `{fullDecl ++ o.getId.replacePrefix declName .anonymous}`"
            else String.intercalate " ⊕ " (globals.toList.map (·.cite))
          seamCite := match seam? with | some (_, _, s) => s | none => "" }
      return {
        row := r
        seam? := seam?.map fun (seamId, segTy, _) =>
          { field := idxs[0]!, inv := invId, const := seamId, segTy := segTy }
        freeOnState? := freeOnState? }
    if let some seam := result.seam? then
      declarationSeams := declarationSeams.push seam
    if let some h := result.freeOnState? then
      declarationFrees := declarationFrees.push h
    rows := rows.push result.row
  -- ── The DOCUMENT-SEAM rule. Two field seams may sit anywhere in the
  -- right-nested state. Each is lifted with `seamAlong`, using a section that
  -- plants the OTHER verdict's legal `x` at the other coordinated field and
  -- ordinary defaults everywhere else. Those custom sections make the
  -- side-conditions of `andSeams` available from the verdicts' own `.hx`,
  -- without assuming that a field kind's structural default satisfies its
  -- invariant (the zero quota, importantly, does not satisfy budget 10).
  if declarationSeams.size == 2 then
    let a := declarationSeams[0]!
    let b := declarationSeams[1]!
    let (left, right) := if a.field < b.field then (a, b) else (b, a)
    if left.field != right.field then
      let leftSeam := left.const
      let rightSeam := right.const
      let leftAcc := mkIdent (declName ++ fieldNames[left.field]!)
      let rightAcc := mkIdent (declName ++ fieldNames[right.field]!)
      let leftHom := mkIdent (declName ++ (fieldNames[left.field]! ++ `merge_hom))
      let rightHom := mkIdent (declName ++ (fieldNames[right.field]! ++ `merge_hom))
      let rightX : Term ← `(Uwueave.Spec.SegVerdict.x $rightSeam)
      let leftX : Term ← `(Uwueave.Spec.SegVerdict.x $leftSeam)
      let leftPlant ← plantFn left.field n (defaults.set! right.field rightX)
      let rightPlant ← plantFn right.field n (defaults.set! left.field leftX)
      let leftLiftId := mkIdent (declName ++ `documentSeamLeft)
      let rightLiftId := mkIdent (declName ++ `documentSeamRight)
      let baseId := mkIdent (declName ++ `documentSeamBase)
      let documentSeamId := mkIdent (declName ++ `documentSeam)
      elabCommand (← `(command|
        /-- The left field's seam at document scale. Its section plants the
        right seam verdict's legal left witness, so the two lifted invariants
        can be conjoined without an unproved default-legality assumption. -/
        def $leftLiftId :=
          Uwueave.Preo.seamAlong $leftAcc $leftHom $leftPlant
            (fun _ => rfl) (fun _ _ => rfl) $leftSeam))
      elabCommand (← `(command|
        /-- The right field's seam at document scale, with the left seam
        verdict's legal left witness planted symmetrically. -/
        def $rightLiftId :=
          Uwueave.Preo.seamAlong $rightAcc $rightHom $rightPlant
            (fun _ => rfl) (fun _ _ => rfl) $rightSeam))
      elabCommand (← `(command|
        /-- The two seamed field invariants conjoined at document scale. Its
        seam is the pair of their field seams; replicas sharing a fiber of that
        pair merge without coordination. The carried global clash is the left
        invariant's concrete witness with the right verdict's legal left
        witness held fixed. -/
        def $baseId :=
          Uwueave.Spec.SegVerdict.andSeams $leftLiftId $rightLiftId
            (Uwueave.Spec.SegVerdict.hx $rightSeam)
            (Uwueave.Spec.SegVerdict.hx $rightSeam)))
      -- Free rows may ride this already-stable seam, but `absorbFree` honestly
      -- requires them to hold at its carried clash pair. Attempt that proof by
      -- kernel decision; a row whose legality is undecidable or false at the
      -- generated witnesses is left out rather than assumed.
      let mut currentSeam := baseId
      let mut absorbed : Nat := 0
      for freeProof in declarationFrees do
        let suffix := Name.mkSimple s!"documentSeamFree{absorbed + 1}"
        let nextId := mkIdent (declName ++ suffix)
        match ← tryEmit (← `(command|
            /-- One coordination-free row absorbed into the declaration seam.
            This constant exists only because the row holds at both carried
            clash documents; `by decide` is a kernel-checked side condition. -/
            def $nextId :=
              Uwueave.Spec.SegVerdict.absorbFree $currentSeam $freeProof
                (by decide) (by decide))) with
        | .ok _ =>
            floorCheck declId "absorbed document seam verdict" (ns ++ nextId.getId)
            currentSeam := nextId
            absorbed := absorbed + 1
        | .error _ => pure ()
      elabCommand (← `(command|
        /-- The declaration's composed document seam: its two seam rows, plus
        every coordination-free row whose legality at the carried clash pair
        the registry also proved. A free row without that inhabitance proof is
        omitted from this conjunction, never silently assumed. -/
        def $documentSeamId := $currentSeam))
      floorCheck declId "document seam verdict" (fullDecl ++ `documentSeam)
  -- §3.5 Named futures. The surface must say which `WorldModel` indexes the
  -- declaration. Elaboration only checks the supplied `FutureDecl` at that
  -- model; it never reconstructs a world relation from materialized state.
  for future in futures do
    let `(preoFuture| future $nm on $model := $body) := future
      | throwErrorAt future "preo: malformed future declaration"
    let modelId := mkIdent (declName ++ (nm.getId ++ `WorldModel))
    let futureId := mkIdent (declName ++ nm.getId)
    elabCommand (← `(command|
      /-- The explicit retained-world model indexing this named future. -/
      abbrev $modelId : Uwueave.Preo.Future.WorldModel := $model))
    elabCommand (← `(command|
      /-- A checked named relation on the retained world carrier. -/
      def $futureId : Uwueave.Preo.Future.FutureDecl $modelId := $body))
    floorCheck nm "future declaration" (ns ++ futureId.getId)
    rows := rows.push {
      decl := fullDecl, kind := .future, name := nm.getId.toString
      detail := pp model, detail₂ := pp body
      evidence := ns ++ futureId.getId, isObligation := false
      cite := "Preo.Future.FutureDecl at the explicit WorldModel (kernel-checked)"
      seamCite := "" }
  -- §3.6 Intrinsically typed programs. `Raw.infer` is executed by the
  -- kernel-reduced `success` proof in `Expr.Program`; if it returns `none`, no
  -- checked term, analysis, cache, update function, or report row exists.
  for typedDer in typedDers do
    let `(preoTypedDerive| typed derive $nm over { schema := $schema, reach := $reach } := $raw) := typedDer
      | throwErrorAt typedDer "preo: malformed `typed derive`"
    let schemaId := mkIdent (declName ++ (nm.getId ++ `Schema))
    let rawId := mkIdent (declName ++ (nm.getId ++ `Raw))
    let programId := mkIdent (declName ++ (nm.getId ++ `Program))
    let checkedId := mkIdent (declName ++ (nm.getId ++ `Checked))
    let typeId := mkIdent (declName ++ (nm.getId ++ `Type))
    let termId := mkIdent (declName ++ (nm.getId ++ `Term))
    let evalId := mkIdent (declName ++ (nm.getId ++ `Eval))
    let holesId := mkIdent (declName ++ (nm.getId ++ `Holes))
    let readsId := mkIdent (declName ++ (nm.getId ++ `Reads))
    let mergeSafeId := mkIdent (declName ++ (nm.getId ++ `MergeSafe?))
    let monotoneSafeId := mkIdent (declName ++ (nm.getId ++ `MonotoneSafe?))
    let cacheId := mkIdent (declName ++ (nm.getId ++ `Cache))
    let buildCacheId := mkIdent (declName ++ (nm.getId ++ `buildCache))
    let updateId := mkIdent (declName ++ (nm.getId ++ `update))
    let updateCacheId := mkIdent (declName ++ (nm.getId ++ `updateCache))
    let updateCorrectId := mkIdent (declName ++ (nm.getId ++ `update_correct))
    let zeroId := mkIdent (declName ++ (nm.getId ++ `update_off_dependency_zero))
    let reachId := mkIdent (declName ++ (nm.getId ++ `Reach))
    let resultFutureId := mkIdent (declName ++ (nm.getId ++ `ResultFuture))
    let resultId := mkIdent (declName ++ (nm.getId ++ `Result))
    let resultCarrierId := mkIdent (declName ++ (nm.getId ++ `ResultCarrier))
    let reachReportId := mkIdent (declName ++ (nm.getId ++ `ReachReport))
    let reportAtId := mkIdent (declName ++ (nm.getId ++ `reportAt))
    elabCommand (← `(command|
      /-- The explicitly written first-order input schema. -/
      abbrev $schemaId : Uwueave.Preo.Expr.Schema := $schema))
    elabCommand (← `(command|
      /-- The raw typed-derive syntax before inference. -/
      def $rawId : Uwueave.Preo.Expr.Raw := $raw))
    match ← tryEmit (← `(command|
        /-- The checked program. Its only typed term is extracted from
        `Raw.infer`; the success proof is kernel reduction, not a cast. -/
        def $programId : Uwueave.Preo.Expr.Program $schemaId where
          raw := $rawId
          success := by decide)) with
    | .error why =>
        throwErrorAt raw "preo: `typed derive {nm.getId}` was refused by \
          `Preo.Expr.Raw.infer`. The expression is malformed, reads a field \
          outside its schema, applies an operator at the wrong type, or uses \
          raw `.custom`, which has no implementation/locality proof. No typed \
          term or positive analysis was emitted. Kernel reduction said: {why}"
    | .ok _ => pure ()
    floorCheck nm "typed program" (fullDecl ++ (nm.getId ++ `Program))
    elabCommand (← `(command|
      /-- The exact existential result returned by `Raw.infer`. -/
      def $checkedId : Uwueave.Preo.Expr.Checked $schemaId :=
        Uwueave.Preo.Expr.Program.checked $programId))
    elabCommand (← `(command|
      /-- The result type inferred from the raw expression. -/
      abbrev $typeId : Uwueave.Preo.Expr.Ty :=
        Uwueave.Preo.Expr.Program.type $programId))
    elabCommand (← `(command|
      /-- The intrinsically typed term extracted from `Raw.infer`. -/
      def $termId : Uwueave.Preo.Expr.Term $schemaId $typeId :=
        Uwueave.Preo.Expr.Program.term $programId))
    elabCommand (← `(command|
      /-- Evaluation hook for runtime and six-state result adapters. -/
      def $evalId : Uwueave.Preo.Expr.Env $schemaId →
          Uwueave.Preo.Expr.Ty.denote $typeId :=
        Uwueave.Preo.Expr.Program.eval $programId))
    elabCommand (← `(command|
      /-- Exact positional dependency occurrences. -/
      def $holesId : List Uwueave.Preo.Expr.Hole :=
        Uwueave.Preo.Expr.Program.holes $programId))
    elabCommand (← `(command|
      /-- Exact field reads, definitionally the erasure of `Holes`. -/
      def $readsId : List Nat := Uwueave.Preo.Expr.Program.reads $programId))
    elabCommand (← `(command|
      /-- Proof-carrying positive merge classification; `none` is no claim. -/
      def $mergeSafeId :
          Option (Uwueave.Preo.Expr.MergeSafe $termId) :=
        Uwueave.Preo.Expr.certifyMergeSafe $termId))
    elabCommand (← `(command|
      /-- Proof-carrying positive monotonicity classification; `none` is no
      claim and is not a refutation. -/
      def $monotoneSafeId :
          Option (Uwueave.Preo.Expr.MonotoneSafe $termId) :=
        Uwueave.Preo.Expr.certifyMonotone $termId))
    elabCommand (← `(command|
      /-- A cache indexed by this exact inferred term. -/
      abbrev $cacheId := Uwueave.Preo.Incremental.ProgramCache $programId))
    elabCommand (← `(command|
      /-- Build a cache whose value is proved equal to fresh evaluation. -/
      def $buildCacheId (env : Uwueave.Preo.Expr.Env $schemaId) : $cacheId :=
        Uwueave.Preo.Incremental.buildProgramCache $programId env))
    elabCommand (← `(command|
      /-- Checked differential update: zero root evaluations on a proved miss,
      exactly one full root evaluation on a conservative hit. -/
      def $updateId (cache : $cacheId)
          (delta : Uwueave.Preo.Incremental.EnvDelta cache.env) :=
        Uwueave.Preo.Incremental.updateProgram $programId cache delta))
    elabCommand (← `(command|
      theorem $updateCorrectId (cache : $cacheId)
          (delta : Uwueave.Preo.Incremental.EnvDelta cache.env) :
          ($updateId cache delta).value = $evalId delta.after :=
        Uwueave.Preo.Incremental.updateProgram_correct $programId cache delta))
    elabCommand (← `(command|
      /-- Chain a checked update into the cache for the next typed delta,
      without reevaluating the term. -/
      def $updateCacheId (cache : $cacheId)
          (delta : Uwueave.Preo.Incremental.EnvDelta cache.env) : $cacheId :=
        Uwueave.Preo.Incremental.updateProgramCache $programId cache delta))
    elabCommand (← `(command|
      theorem $zeroId (cache : $cacheId)
          (delta : Uwueave.Preo.Incremental.EnvDelta cache.env)
          (h : Uwueave.Preo.Incremental.touched delta $termId = false) :
          ($updateId cache delta).recomputations = 0 ∧
            ($updateId cache delta).value = cache.value :=
        Uwueave.Preo.Incremental.updateProgram_off_dependency_zero
          $programId cache delta h))
    elabCommand (← `(command|
      /-- The author-declared finite reach used for least six-status effect
      inference. It is intentionally independent of the document State unless
      the author supplies a projection into this typed environment. -/
      def $reachId : List (Uwueave.Preo.Expr.Env $schemaId) := $reach))
    elabCommand (← `(command|
      /-- The honest snapshot future for this pure query: equality only. -/
      abbrev $resultFutureId :
          Uwueave.Evidence.Future (Uwueave.Preo.Expr.Env $schemaId) :=
        Uwueave.Preo.Incremental.TypedResult.Future $programId))
    let resultName := Syntax.mkStrLit s!"{fullDecl}.{nm.getId}"
    let futureName := Syntax.mkStrLit s!"{fullDecl}.{nm.getId}/snapshot-equality"
    let surfaceName := Syntax.mkStrLit s!"{fullDecl}.{nm.getId}/inspectable"
    elabCommand (← `(command|
      /-- A checked six-status declaration consuming this exact typed
      evaluator and finite reach. Resolution is explicitly preserve-fork;
      equality is the only admitted future. -/
      def $resultId :=
        Uwueave.Preo.Incremental.TypedResult.declaration $programId
          $resultName $futureName $surfaceName $reachId))
    floorCheck nm "typed result program" (fullDecl ++ (nm.getId ++ `Result))
    elabCommand (← `(command|
      /-- The reference six-way carrier used by the generated checked report. -/
      abbrev $resultCarrierId :=
        Uwueave.RenderSix.stdCarrier6 $resultFutureId
          (Uwueave.Preo.Expr.Ty.denote $typeId)))
    elabCommand (← `(command|
      /-- A checked report that retains proof its evaluated site belongs to the
      finite reach used by effect inference. -/
      structure $reachReportId where
        checked :
          Uwueave.Preo.ResultProgram.CheckedReport $resultId $resultCarrierId
        inReach : checked.state ∈ $reachId))
    elabCommand (← `(command|
      /-- A checked report whose site, status, future, resolution, visibility
      and disclosure are all computed from the generated result declaration. -/
      def $reportAtId (env : Uwueave.Preo.Expr.Env $schemaId)
          (inReach : env ∈ $reachId) : $reachReportId where
        checked := Uwueave.Preo.ResultProgram.CheckedReport.renderAt
          $resultId $resultCarrierId env
        inReach := inReach))
    rows := rows.push {
      decl := fullDecl, kind := .typedDerive, name := nm.getId.toString
      detail := pp schema, detail₂ := pp raw ++ " on reach " ++ pp reach
      evidence := fullDecl ++ (nm.getId ++ `Program), isObligation := false
      cite := "Expr.Raw.infer → proof-carrying merge/monotone analyses → checked cache/update → finite-reach six-status Result/report"
      seamCite := "" }

  -- §3.7 Ordinary Lean derives — the fourth verdict and the deliberate
  -- unrestricted escape hatch alongside the first-order typed fragment.
  for der in ders do
    let `(preoDerive| derive $nm : $ty = $body $[:= $ev]?) := der
      | throwErrorAt der "preo: malformed derive"
    let used := mentions fieldNames body
    if used.size != 1 then
      throwErrorAt nm "preo: `derive {nm.getId}` reads {used.size} field(s) \
        ({String.intercalate ", " (used.toList.map toString)}) — this fragment \
        classifies a computation over EXACTLY ONE field, because the transport \
        that carries its answer to the declared state \
        (`Preo.mergeability_comp`) is along one projection. A multi-field \
        derive needs a joint-merge argument, which is the `derive custom = \
        opaque …` escape hatch of `PREOSCRIPTING.md` §7.1 and is not built."
    let some fi := fieldNames.findIdx? (· == used[0]!) | throwErrorAt nm "preo: internal"
    let fname := fieldNames[fi]!
    let carrier := carriers[fi]!
    let accId := mkIdent (declName ++ fname)
    let homId := mkIdent (declName ++ (fname ++ `merge_hom))
    let surjId := mkIdent (declName ++ (fname ++ `surj))
    let onId := mkIdent (declName ++ (nm.getId ++ `on))
    let dId := mkIdent (declName ++ nm.getId)
    let mergeId := mkIdent (declName ++ (nm.getId ++ `merge))
    let row : Row ← withRef nm do
      elabCommand (← `(command|
        /-- The computation, at the field's own carrier. -/
        @[reducible] def $onId : $carrier → $ty := fun $(fieldIdents[fi]!) => $body))
      elabCommand (← `(command|
        /-- The computation, at the declared document. -/
        def $dId : $stateId → $ty := fun s => $onId ($accId s)))
      -- The mergeability rule registry: closed theorems, tried by TYPECHECKING
      -- against the emitted computation. A shape none of them fits is a
      -- refusal, never a guess.
      let cand : List (String × Term × Term × String) :=
        [ ("author-supplied", ← `(Uwueave.JoinHom.Fourth.fromResults),
            ev.getD (← `(Uwueave.JoinHom.verdict_exists)),
            "author-supplied (fromResults), kernel-checked"),
          ("author-supplied", ← `(Uwueave.JoinHom.Fourth.needsEvidence),
            ev.getD (← `(Uwueave.JoinHom.verdict_card)),
            "author-supplied (needsEvidence), kernel-checked"),
          ("∃-read", ← `(Uwueave.JoinHom.Fourth.fromResults),
            ← `(Uwueave.JoinHom.verdict_exists),
            "JoinHom.exists_joinHom — ∃ distributes over ∨, so the summary is a \
             join homomorphism and `summaryFold_iff_joinHom` licenses shipping it"),
          ("filtered view", ← `(Uwueave.JoinHom.Fourth.fromResults),
            ← `(Uwueave.JoinHom.verdict_restrict _),
            "JoinHom.restrict_joinHom — && distributes over ||"),
          ("high-water mark", ← `(Uwueave.JoinHom.Fourth.fromResults),
            ← `(Uwueave.JoinHom.verdict_high),
            "JoinHom.high_joinHom — max regroups"),
          ("set image", ← `(Uwueave.JoinHom.Fourth.fromResults),
            ← `(Uwueave.JoinHom.verdict_image _),
            "JoinHom.evalSet_joinHom (Holes.evalSet_hom)"),
          ("count", ← `(Uwueave.JoinHom.Fourth.needsEvidence),
            ← `(Uwueave.JoinHom.verdict_card),
            "⚠ JoinHom.no_count_merge_without_provenance — for EVERY candidate \
             combiner there are two scenarios with equal local counts and \
             different merged counts, so the summary architecture is wrong in \
             one gossip step (JoinHom.card_fold_disagrees). Ship the evidence.") ]
      let mut fired : Option (String × String) := none
      for (label, ansT, proofT, cite) in cand do
        if fired.isSome then continue
        if label == "author-supplied" && ev.isNone then continue
        match ← tryEmit (← `(command|
            def $mergeId : Uwueave.Preo.MergeFacet $dId where
              answer := $ansT
              correct :=
                Uwueave.Preo.mergeability_comp (π := $accId) (g := $onId)
                  $homId $surjId (($proofT : Uwueave.JoinHom.Fourth.Correct $onId $ansT))
              cite := $(Syntax.mkStrLit cite))) with
        | .ok _ =>
            floorCheck nm "mergeability facet" (fullDecl ++ (nm.getId ++ `merge))
            fired := some (label, cite)
        | .error _ => pure ()
      let mut oblId? : Option Ident := none
      if fired.isNone then
        let why :=
          "no mergeability rule fits this computation. The registry knows: an \
           EXISTENTIAL read over a grow-only set, a FILTERED view, a HIGH-WATER \
           mark over a G-Counter, a SET IMAGE, and a COUNT over a two-element \
           universe — each tried by typechecking a closed theorem against the \
           emitted computation, so a shape it does not know is this refusal and \
           never a guess. DISCHARGE by supplying the answer with `evidence \
           := <proof of JoinHom.Fourth.Correct>`, or prove the computation is a \
           `JoinHom` and go through `joinHom_incrementallyMergeable`. ⚠ Note \
           which way the missing answer fails safe: NO answer is not \
           `fromResults`, and shipping a summary on the strength of an \
           unclassified derive is exactly the error `JoinHom.lean` §4 exists \
           to refute."
        let oId := mkIdent (declName ++ (nm.getId ++ `obligation))
        elabCommand (← `(command|
          def $oId : Uwueave.Preo.Obligation (S := $stateId) (fun _ => True) where
            invName := $(Syntax.mkStrLit nm.getId.toString)
            onField := $(Syntax.mkStrLit fname.toString)
            tried := ["∃-read", "filtered view", "high-water mark", "set image", "count"]
            discharge := $(Syntax.mkStrLit why)))
        oblId? := some oId
      let classId := mkIdent (declName ++ (nm.getId ++ `classification))
      let mList : Term ←
        if fired.isSome then `([$mergeId])
        else `(([] : List (Uwueave.Preo.MergeFacet $dId)))
      let oList : Term ← match oblId? with
        | none => `(([] : List (Uwueave.Preo.Obligation (S := $stateId) (fun _ => True))))
        | some oId => `([$oId])
      elabCommand (← `(command|
        /-- The derive's accumulated facets. Its `global`/`seams` are empty by
        construction: a computation has no confluence verdict, it has a
        mergeability one. -/
        def $classId :
            Uwueave.Preo.Classification (S := $stateId) (fun _ => True) $dId where
          global := []
          seams := []
          mergeability := $mList
          obligations := $oList))
      return {
        decl := fullDecl, kind := .derive, name := nm.getId.toString
        detail := fname.toString
        detail₂ := match fired with | some (l, _) => l | none => "—"
        evidence := fullDecl ++ (nm.getId ++ `classification)
        isObligation := fired.isNone
        cite := match fired with
          | some (_, c) => c
          | none => "UNRESOLVED — see the row's `.obligation`"
        seamCite := "" }
    rows := rows.push row
  -- §3.8 Typed protocol terms. The body is the deliberate opaque Lean escape
  -- hatch into `Protocol.Term`: the semantic recursion remains in one API.
  for protocol in protocols do
    let `(preoProtocol| protocol $nm over $strategyTy := $body) := protocol
      | throwErrorAt protocol "preo: malformed protocol declaration"
    let protocolId := mkIdent (declName ++ nm.getId)
    elabCommand (← `(command|
      /-- A typed protocol AST. Its denotation and profile are supplied only by
      `Protocol.Term.denote` and `.profile`. -/
      def $protocolId : Uwueave.Protocol.Term $strategyTy := $body))
    floorCheck nm "protocol declaration" (ns ++ protocolId.getId)
    rows := rows.push {
      decl := fullDecl, kind := .protocol, name := nm.getId.toString
      detail := pp strategyTy, detail₂ := pp body
      evidence := ns ++ protocolId.getId, isObligation := false
      cite := "Protocol.Term (typed AST; semantics stay in Term.denote/profile)"
      seamCite := "" }
  -- §3.9 Sessions. Each emitted artifact is one named call to the modular
  -- protocol elaborator; projections reuse it and never recompute a count.
  for session in sessions do
    let `(preoSession| session $nm $mode:preoSessionMode at $strategy $[:= $h]?) := session
      | throwErrorAt session "preo: malformed session declaration"
    let keywords : Array Name := #[`runs, `under, `composes, `with]
    let payload : Array Ident := mode.raw.getArgs.filterMap fun arg =>
      if arg.isIdent && !keywords.contains arg.getId.eraseMacroScopes then
        some ⟨arg⟩
      else none
    let sessionId := mkIdent (declName ++ nm.getId)
    if mode.raw.getKind == ``preoSessionRuns then
      if h.isSome || payload.size != 1 then
        throwErrorAt session "preo: `session … runs …` takes no membership proof"
      let protocol := payload[0]!
      let protocolId := mkIdent (declName ++ protocol.getId)
      let planId := mkIdent (declName ++ (nm.getId ++ `Plan))
      let upperId := mkIdent (declName ++ (nm.getId ++ `UpperBound))
      elabCommand (← `(command|
        /-- Proof-carrying protocol elaboration at the selected strategy. -/
        def $sessionId := Uwueave.Protocol.elaborate $protocolId $strategy))
      elabCommand (← `(command|
        /-- The checked schedule projected from this elaboration. -/
        def $planId := Uwueave.Protocol.Elaboration.plan $sessionId))
      elabCommand (← `(command|
        /-- The witnessed identity-schedule upper bound; not a verdict bit and
        not a claim that crossings equal meetings. -/
        def $upperId := Uwueave.Protocol.Elaboration.upperBound $sessionId))
      floorCheck nm "session elaboration" (ns ++ sessionId.getId)
      floorCheck nm "session plan" (ns ++ planId.getId)
      floorCheck nm "session upper bound" (ns ++ upperId.getId)
      rows := rows.push {
        decl := fullDecl, kind := .session, name := nm.getId.toString
        detail := protocol.getId.toString, detail₂ := "Protocol.elaborate"
        evidence := ns ++ sessionId.getId, isObligation := false
        cite := "Protocol.Elaboration with checked .plan and .upperBound"
        seamCite := "" }
    else if mode.raw.getKind == ``preoSessionProfile then
      let some h := h
        | throwErrorAt session "preo: a profiled session needs its strategy-membership proof"
      if payload.size != 2 then throwErrorAt session "preo: malformed profiled session"
      let admissible := payload[0]!
      let protocol := payload[1]!
      let protocolId := mkIdent (declName ++ protocol.getId)
      let planId := mkIdent (declName ++ (nm.getId ++ `Plan))
      let upperId := mkIdent (declName ++ (nm.getId ++ `UpperBound))
      let profileId := mkIdent (declName ++ (nm.getId ++ `ProfilePlan))
      elabCommand (← `(command|
        def $sessionId := Uwueave.Protocol.elaborate $protocolId $strategy))
      elabCommand (← `(command|
        def $planId := Uwueave.Protocol.Elaboration.plan $sessionId))
      elabCommand (← `(command|
        def $upperId := Uwueave.Protocol.Elaboration.upperBound $sessionId))
      elabCommand (← `(command|
        /-- The named admissible-space plan; strategy selection happens once
        for the entire protocol profile. -/
        def $profileId :=
          Uwueave.Protocol.elaborateProfilePlan $admissible $protocolId
            $strategy $h))
      floorCheck nm "session elaboration" (ns ++ sessionId.getId)
      floorCheck nm "session plan" (ns ++ planId.getId)
      floorCheck nm "session upper bound" (ns ++ upperId.getId)
      floorCheck nm "session profile plan" (ns ++ profileId.getId)
      rows := rows.push {
        decl := fullDecl, kind := .session, name := nm.getId.toString
        detail := protocol.getId.toString
        detail₂ := "Protocol.elaborate + elaborateProfilePlan"
        evidence := ns ++ sessionId.getId, isObligation := false
        cite := s!"one strategy selected from `{admissible.getId}` (proof checked)"
        seamCite := "" }
    else if mode.raw.getKind == ``preoSessionComposed then
      let some h := h
        | throwErrorAt session "preo: a composed session needs its strategy-membership proof"
      if payload.size != 3 then throwErrorAt session "preo: malformed composed session"
      let admissible := payload[0]!
      let left := payload[1]!
      let right := payload[2]!
      let leftId := mkIdent (declName ++ left.getId)
      let rightId := mkIdent (declName ++ right.getId)
      elabCommand (← `(command|
        /-- A composed profile plan built only after choosing the one admissible
        strategy shared by both protocol terms. -/
        def $sessionId :=
          Uwueave.Protocol.elaborateComposedProfilePlan $admissible
            $leftId $rightId $strategy $h))
      floorCheck nm "composed session profile plan" (ns ++ sessionId.getId)
      rows := rows.push {
        decl := fullDecl, kind := .session, name := nm.getId.toString
        detail := left.getId.toString ++ " × " ++ right.getId.toString
        detail₂ := "Protocol.elaborateComposedProfilePlan"
        evidence := ns ++ sessionId.getId, isObligation := false
        cite := s!"pointwise composition under one strategy from `{admissible.getId}`"
        seamCite := "" }
    else
      throwErrorAt session "preo: unknown session form"
  modifyEnv fun env => rows.foldl (fun e r => preoExt.addEntry e r) env
  logInfo m!"preo {declName}: {n} field(s), {invs.size} invariant(s), \
    {futures.size} future(s), {typedDers.size} typed derive(s), \
    {ders.size} ordinary derive(s), {protocols.size} protocol(s), \
    {sessions.size} session(s) — \
    `#preo_report {declName}` for the table"

/-! §3.9 Named future certificates. This is intentionally a separate command:
its fully dependent type is ordinary Lean syntax, and no additional repeated
item family can interfere with the declaration parser. -/

@[command_elab preoCertificate]
def elabPreoCertificate : CommandElab := fun stx => do
  let `(command| preo_certificate $nm : $ty := $proof) := stx
    | throwError "preo_certificate: malformed declaration"
  unless ← isCheckedCertificateType ty do
    throwErrorAt ty "preo_certificate: the declared type must reduce to \
      `Uwueave.Preo.Future.CheckedCertificate ...`. Write the complete future, \
      answer, key, certificate predicate, and exact `WorldIndex`; this command \
      does not infer any of them from materialized state or from the proof."
  elabCommand (← `(command|
    /-- A named, proof-carrying certificate at its explicitly written world. -/
    def $nm : $ty := $proof))
  let ns ← getCurrNamespace
  floorCheck nm "named future certificate" (ns ++ nm.getId)

/-! §3.10 Five-currency budgets. Like certificates, these remain standalone so
their proof term has a punctuation-delimited end and the main declaration does
not acquire another ambiguous repeated item family. -/

@[command_elab preoBudget]
def elabPreoBudget : CommandElab := fun stx => do
  let `(command| preo_budget $nm for $session : $limits := $proof) := stx
    | throwError "preo_budget: malformed declaration"
  let limitsId := mkIdent (nm.getId ++ `Limits)
  let sessionId := mkIdent (nm.getId ++ `Session)
  let planId := mkIdent (nm.getId ++ `Plan)
  let peerId := mkIdent (nm.getId ++ `PeerUpperBound)
  elabCommand (← `(command|
    /-- The five explicit currency limits; no total or crossing conversion. -/
    abbrev $limitsId : Uwueave.Scheduling.Currency → Nat := $limits))
  elabCommand (← `(command|
    /-- The exact semantic session selected by the named elaboration. -/
    abbrev $sessionId : Uwueave.Scheduling.Session :=
      Uwueave.Protocol.Elaboration.session $session))
  elabCommand (← `(command|
    /-- One checked plan satisfying every currency coordinate. -/
    def $nm : Uwueave.Scheduling.ProfileUpperBound $sessionId $limitsId :=
      $proof))
  elabCommand (← `(command|
    /-- The exhibited plan carried by this profile acceptance. -/
    def $planId : Uwueave.Scheduling.Plan $sessionId :=
      Uwueave.Scheduling.ProfileUpperBound.plan $nm))
  elabCommand (← `(command|
    /-- Compatibility projection for the peer-barrier coordinate only. -/
    def $peerId : Uwueave.Scheduling.UpperBound $sessionId
        ($limitsId .peerBarrier) :=
      Uwueave.Scheduling.ProfileUpperBound.toUpperBound $nm))
  let ns ← getCurrNamespace
  floorCheck nm "five-currency budget" (ns ++ nm.getId)

/-! §3.11 Explicit checked export manifests. Every row extends one
`Export.DeclarationBundle` term immediately. The elaborator retains source
names only long enough to select already checked constants; stable IDs remain
the literal manifest terms and no report metadata enters the builder. -/

@[command_elab preoExport]
def elabPreoExport : CommandElab := fun stx => do
  let `(command| preo_export $exportId from $declId : $config :=
    declaration := {
      id := $declarationId, stateType := $stateTypeId,
      schema := $schemaVersion }
    $items:preoExportItem*) := stx
    | throwError "preo_export: malformed manifest"
  let exportName := exportId.getId
  let declName := declId.getId
  let stateId := mkIdent (declName ++ `State)
  let declarationName := mkIdent (exportName ++ `Declaration)
  let bundleName := mkIdent (exportName ++ `Bundle)
  let artifactName := mkIdent (exportName ++ `Artifact)
  let projectionName := mkIdent (exportName ++ `Projection)
  let encodingName := mkIdent (exportName ++ `Encoding)
  let formatName := mkIdent (exportName ++ `ArtifactDurableFormat)
  let bytesName := mkIdent (exportName ++ `ArtifactDurableBytes)
  let v2Name := mkIdent (exportName ++ `ProjectionV2)
  let configName := mkIdent (exportName ++ `ValidationConfig)
  let validationName := mkIdent (exportName ++ `Validation)
  let validationOkName := mkIdent (exportName ++ `validation_ok)
  let validatedName := mkIdent (exportName ++ `Validated)
  let renderedName := mkIdent (exportName ++ `Rendered)
  let renderResultName := mkIdent (exportName ++ `RenderResult)

  elabCommand (← `(command|
    /-- The declaration row, indexed by the actual elaborated state type. -/
    def $declarationName :
        Uwueave.Preo.Artifact.CheckedDeclaration $stateId :=
      Uwueave.Preo.Artifact.CheckedDeclaration.ofState
        ⟨$declarationId⟩ $stateTypeId $schemaVersion))

  let mut bundle : Term ←
    `(Uwueave.Preo.Export.DeclarationBundle.ofDeclaration $declarationName)
  for item in items do
    if item.raw.getKind == ``preoExportField then
      let `(preoExportItem| | field $fieldId:ident := {
          id := $id, kind := $kindId, carrier := $carrierId, key := $keyId }) := item
        | throwErrorAt item "preo_export: malformed field row"
      let carrierName := mkIdent (declName ++ (fieldId.getId ++ `Carrier))
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addField
        (Carrier := $carrierName) $bundle ⟨$id⟩ $kindId $carrierId $keyId)
    else if item.raw.getKind == ``preoExportInvariant then
      let `(preoExportItem| | invariant $invId:ident := {
          id := $id, carrier := $carrierId, codec := $codec,
          answered := $answered }) := item
        | throwErrorAt item "preo_export: malformed invariant row"
      let classificationName :=
        mkIdent (declName ++ (invId.getId ++ `classification))
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addClassification
        $bundle $classificationName $answered ⟨$id⟩ $carrierId $codec)
    else if item.raw.getKind == ``preoExportFuture then
      let `(preoExportItem| | future $futureId:ident := {
          certificate := $certificate:ident, id := $id,
          world := $worldId, relation := $relationId }) := item
        | throwErrorAt item "preo_export: malformed future row"
      let futureName := mkIdent (declName ++ futureId.getId)
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addCertifiedFuture
        $bundle $futureName $certificate ⟨$id⟩ $worldId $relationId)
    else if item.raw.getKind == ``preoExportSession then
      let `(preoExportItem| | session $sessionId:ident := {
          id := $id, plan := $planId }) := item
        | throwErrorAt item "preo_export: malformed session row"
      let sessionName := mkIdent (declName ++ sessionId.getId)
      unless ← isProtocolElaborationTerm sessionName do
        throwErrorAt sessionId "preo_export: session `{sessionId.getId}` must be a \
          generated `Protocol.Elaboration`. Composed `ProfilePlan` values are \
          refused in V2: `DeclarationBundle` has no checked builder that can \
          project one as a single session/plan pair."
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addElaboration
        $bundle $sessionName ⟨$id⟩ ⟨$planId⟩)
    else if item.raw.getKind == ``preoExportBudget then
      let `(preoExportItem| | budget $budget:ident for $sessionId:ident := {
          id := $budgetId, session := $stableSessionId,
          plan := $stablePlanId, samePlan := $samePlan }) := item
        | throwErrorAt item "preo_export: malformed budget row"
      let sessionName := mkIdent (declName ++ sessionId.getId)
      unless ← isProtocolElaborationTerm sessionName do
        throwErrorAt sessionId "preo_export: budget `{budget.getId}` must be tied \
          to a generated `Protocol.Elaboration`; composed `ProfilePlan` values \
          have no exact plan-indexed budget builder in V2."
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addElaborationWithBudget
        $bundle $sessionName ⟨$stableSessionId⟩ ⟨$stablePlanId⟩
          ⟨$budgetId⟩ $budget $samePlan)
    else
      throwErrorAt item "preo_export: unknown manifest row"

  elabCommand (← `(command|
    /-- The one proof-indexed builder chain, in manifest row order. -/
    noncomputable def $bundleName :
        Uwueave.Preo.Export.DeclarationBundle $stateId := $bundle))
  elabCommand (← `(command|
    /-- The checked bundle with all proof indices eliminated to neutral data. -/
    noncomputable def $artifactName : Uwueave.Preo.Artifact.Artifact :=
      Uwueave.Preo.Export.DeclarationBundle.toArtifact $bundleName))
  elabCommand (← `(command|
    /-- Artifact paired with its uniquely canonical first-order encoding. -/
    noncomputable def $projectionName :
        Uwueave.Preo.Export.DeclarationBundle.Projection :=
      Uwueave.Preo.Export.DeclarationBundle.project $bundleName))
  elabCommand (← `(command|
    /-- The canonical first-order encoding selected by the checked projection. -/
    noncomputable def $encodingName : Uwueave.Preo.Artifact.ArtifactEncoding :=
      ($projectionName).encoding))
  elabCommand (← `(command|
    /-- The explicit durable format tag for this generated byte sequence. -/
    def $formatName : Uwueave.Durable.FormatTag :=
      Uwueave.Preo.ArtifactDurable.artifactFormat))
  elabCommand (← `(command|
    /-- Canonical, versioned bytes of the neutral encoding; no runtime FFI. -/
    noncomputable def $bytesName : Uwueave.Preo.ArtifactDurable.Bytes :=
      Uwueave.Preo.ArtifactDurable.projectionBytes $encodingName))
  elabCommand (← `(command|
    /-- The raw V2 input, still requiring fail-closed validation. -/
    noncomputable def $v2Name : Uwueave.Preo.ProjectionV2.Projection :=
      Uwueave.Preo.ProjectionV2.Projection.ofEncoding $encodingName))
  elabCommand (← `(command|
    /-- The application's explicit finite validation policy. -/
    def $configName : Uwueave.Preo.ProjectionV2.ValidationConfig := $config))
  elabCommand (← `(command|
    /-- Validation result before private-boundary extraction. -/
    noncomputable def $validationName :
        Uwueave.Preo.ProjectionV2.ValidationResult
          Uwueave.Preo.ProjectionV2.ValidatedProjectionV2 :=
      Uwueave.Preo.ProjectionV2.validate $configName $v2Name))
  elabCommand (← `(command|
    /-- Compile-time validation gate. Literal duplicate stable IDs, invalid
    references, noncanonical profiles and bounds violations cannot pass it. -/
    theorem $validationOkName : ($validationName).isOk = true := by decide))
  elabCommand (← `(command|
    /-- The private validated boundary, obtained only from successful
    `ProjectionV2.validate`; the error branch contradicts `validation_ok`. -/
    noncomputable def $validatedName :
        Uwueave.Preo.ProjectionV2.ValidatedProjectionV2 :=
      match h : $validationName with
      | .ok value => value
      | .error _ => False.elim (by
          have accepted := $validationOkName
          rw [h] at accepted
          cases accepted)))
  elabCommand (← `(command|
    /-- Deterministic data-only source rendered from the validated boundary. -/
    noncomputable def $renderedName : String :=
      Uwueave.Preo.ProjectionV2.renderRustSource $validatedName))
  elabCommand (← `(command|
    /-- The public validation-first render route, retained for direct equality
    checks against the separately named validated output. -/
    noncomputable def $renderResultName :
        Uwueave.Preo.ProjectionV2.ValidationResult String :=
      Uwueave.Preo.ProjectionV2.validateAndRender $configName $v2Name))

  let ns ← getCurrNamespace
  floorCheck exportId "export bundle" (ns ++ bundleName.getId)
  floorCheck exportId "validated export" (ns ++ validatedName.getId)

/-! ## §4. The report -/

private def pad (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ "".pushn ' ' (w - s.length)

@[command_elab preoReport]
def elabPreoReport : CommandElab := fun stx => do
  let `(command| #preo_report $n:ident) := stx | throwError "preo: malformed report"
  let ns ← getCurrNamespace
  let all := preoExt.getState (← getEnv)
  let want := ns ++ n.getId
  let rows := all.filter fun r => r.decl == want || r.decl == n.getId
  let rows := if rows.isEmpty then all.filter (fun r => n.getId.isSuffixOf r.decl) else rows
  if rows.isEmpty then
    let known := (all.map (·.decl)).toList.eraseDups
    throwErrorAt n "#preo_report: no `preo` declaration named `{n.getId}`. \
      Known: {known}"
  let decl := rows[0]!.decl
  let mut out := s!"preo {decl}\n  state    {decl}.State  \
    (MergeState by inferInstance — checked by an emitted `example`)\n"
  out := out ++ "\n  FIELD                 KIND                  CARRIER\n"
  for r in rows do
    if r.kind == .field then
      out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
  if rows.any (fun r => r.kind == .invariant || r.kind == .cross) then
    out := out ++ "\n  INVARIANT             READS            GLOBAL      SEAM        ROUTES\n"
    for r in rows do
      if r.kind == .invariant || r.kind == .cross then
        let global ←
          match ← readAnswer r.evidence with
          | some (some true) => pure "FREE"
          | some (some false) => pure "ESCALATES"
          | some none => pure "UNRESOLVED"
          | none => pure "?? (the classification did not reduce — report this)"
        let seam := if r.seamCite.isEmpty then "—" else "FREE·seg"
        let tag := if r.kind == .cross then " [cross]" else ""
        out := out ++
          s!"  {pad (r.name ++ tag) 20}  {pad r.detail 15}  {pad global 10}  \
{pad seam 10}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
        unless r.seamCite.isEmpty do
          out := out ++ s!"      ↳ SEAM: {r.seamCite}\n"
  if rows.any (fun r => r.kind == .typedDerive) then
    out := out ++ "\n  TYPED DERIVE          SCHEMA                RAW PROGRAM\n"
    for r in rows do
      if r.kind == .typedDerive then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .derive) then
    out := out ++ "\n  DERIVE                READS       MERGEABILITY    ROUTE\n"
    for r in rows do
      if r.kind == .derive then
        let m ←
          match ← readMergeAnswer r.evidence with
          | some (some s) => pure s
          | some none => pure "UNRESOLVED"
          | none => pure "?? (the classification did not reduce — report this)"
        out := out ++
          s!"  {pad r.name 20}  {pad r.detail 10}  {pad m 14}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .future) then
    out := out ++ "\n  FUTURE                WORLD MODEL           DECLARATION\n"
    for r in rows do
      if r.kind == .future then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .protocol) then
    out := out ++ "\n  PROTOCOL              STRATEGY              TYPED TERM\n"
    for r in rows do
      if r.kind == .protocol then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .session) then
    out := out ++ "\n  SESSION               PROTOCOL(S)           ELABORATION\n"
    for r in rows do
      if r.kind == .session then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .invariant || r.kind == .cross ||
      r.kind == .derive || r.kind == .typedDerive) then
    out := out ++ "\n  Every VERDICT column above is REDUCED out of the row's `.classification`\n"
    out := out ++ "  constant at print time — `Classification.answer` and `.mergeAnswer`,\n"
    out := out ++ "  whose order-independence is `Preo.run_answer_congr`. No verdict is stored.\n"
    out := out ++ "  FREE rows are also stated at document scale as `<invariant>.onState`;\n"
    out := out ++ "  SEAM rows as `<invariant>.seamOnState` (`Preo.seamAlong` — the clash is\n"
    out := out ++ "  transported by PLANTING the field replicas in a document, which is what\n"
    out := out ++ "  fragment 1 said it could not synthesize).\n"
    if rows.any (fun r => r.kind == .typedDerive) then
      out := out ++ "  TYPED DERIVE rows expose `.Holes`, `.Reads`, `.MergeSafe?`,\n"
      out := out ++ "  `.MonotoneSafe?`, `.buildCache`, `.updateCache`, `.Result`, and\n"
      out := out ++ "  membership-gated `.reportAt`;\n"
      out := out ++ "  positive badges are\n"
      out := out ++ "  proof values, while `none` remains an honest non-answer.\n"
  if rows.any (fun r => r.kind == .future || r.kind == .protocol || r.kind == .session) then
    out := out ++ "\n  FUTURE/PROTOCOL/SESSION rows have no verdict column: they name typed\n"
    out := out ++ "  semantic artifacts, and their cited constructors carry the proofs.\n"
  logInfo out

end Uwueave.Preo
