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

@[reducible] def N.dₖ.on : cⱼ → T        := fun fⱼ => <expr>
def     N.dₖ : N.State → T               := fun s => N.dₖ.on (N.fⱼ s)
def     N.dₖ.merge : MergeFacet N.dₖ                              -- Fourth + its proof
def     N.dₖ.classification : Classification _ N.dₖ
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

  * an unknown field kind — the six are named in the error;
  * a field kind with a missing or surplus argument;
  * an invariant mentioning **no** field (it would have no carrier);
  * an invariant mentioning **three or more** fields — the cross machinery is
    binary (`Spec.Verdict.cross` is over `A × B`), and a ternary lift is not
    in the tree;
  * a `derive` reading zero or more than one field — the mergeability transport
    (`Preo.mergeability_comp`) is along **one** projection;
  * a declaration with no fields.
-/
import Uwueave.Preo.Classification

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

/-- The carrier type of a field kind. Six kinds, each an existing catalog or
`Segmented` type with a proved `MergeState`; nothing new is minted here. -/
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
        concrete (timestamp, value) register. For a keyed family of registers, \
        this fragment has no `per` yet."
  | _, _ =>
      throwErrorAt kind "preo: unknown field kind `{k}`. The fragment has six: \
        `GrowSet α` (grow-only set), `Slot α` (a grow-only set carrying a \
        uniqueness ceiling), `Escrow ι` (per-replica quota spend), `Quota ι` \
        (allocation PLUS spend — the carrier the seam lives on), `Counter` \
        (`Nat` under max), `LWW` (last-writer-wins register). Each supplies a \
        carrier and a proved `MergeState` from `Uwueave.Catalog` or \
        `Uwueave.Segmented`."

/-- A legal value of each field kind — the *other* fields' contents when the
elaborator plants a field-scale state in a document. This is what fragment 1
said it could not synthesize ("transporting a clash needs a legal value for
every other field"); it is a closed term per kind, and it is why fragment 2 can
lift a seam and a `needsEvidence` verdict to document scale. -/
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

@[command_elab preoDecl]
def elabPreoDecl : CommandElab := fun stx => do
  let `(command| preo $declId:ident where
      $fs:preoField* $invs:preoInv* $ders:preoDerive*) := stx
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
  let mut carriers : Array Term := #[]
  let mut defaults : Array Term := #[]
  for f in fs do
    let `(preoField| field $nm : $k $[$a]?) := f
      | throwErrorAt f "preo: malformed field"
    if fieldIdents.any (·.getId == nm.getId) then
      throwErrorAt nm "preo: duplicate field `{nm.getId}`"
    fieldIdents := fieldIdents.push nm
    fieldKinds := fieldKinds.push (pp k ++ (a.map (fun t => " " ++ pp t)).getD "")
    carriers := carriers.push (← carrierOf k a)
    defaults := defaults.push (← defaultOf k a)
  let n := carriers.size
  let fieldNames := fieldIdents.map (·.getId)
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
      /-- A document holding the given field value, and a legal default in
      every other field — the section the seam and mergeability transports
      need. -/
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
    let row : Row ← withRef nm do
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
               RE-ALLOCATION is a meeting. Globally refuted by the carried clash \
               (Preo.budget_not_iconfluent_at).")
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
            one entry, `Preo.budgetSeam`, is a single-carrier fiber); "
          else "the seam registry (`Preo.budgetSeam`) did not typecheck at this \
            invariant; "
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
                      "seam (Preo.budgetSeam)"]
            discharge := $(Syntax.mkStrLit why)))
        oblId? := some oId
      -- ── The accumulated Classification. Every column the report prints is
      -- reduced out of THIS constant.
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
      if ans == some (some true) then
        let onStateId := mkIdent (declName ++ (nm.getId ++ `onState))
        if isCross then
          let accA := mkIdent (declName ++ fieldNames[idxs[0]!]!)
          let accB := mkIdent (declName ++ fieldNames[idxs[1]!]!)
          let _ ← tryEmit (← `(command|
            theorem $onStateId :
                Uwueave.IConfluent (S := $stateId) (fun s => $invId ($accA s, $accB s)) :=
              Uwueave.Preo.proj_iconfluent (π := fun s : $stateId => ($accA s, $accB s))
                (fun _ _ => rfl)
                (Uwueave.Tactics.iconfluent_of_isFree
                  (v := $(globals[0]!.const)) rfl)))
        else
          let accId := mkIdent (declName ++ fieldNames[idxs[0]!]!)
          let homId := mkIdent (declName ++ (fieldNames[idxs[0]!]! ++ `merge_hom))
          let _ ← tryEmit (← `(command|
            theorem $onStateId :
                Uwueave.IConfluent (S := $stateId) (fun s => $invId ($accId s)) :=
              Uwueave.Preo.proj_iconfluent $homId
                (Uwueave.Tactics.iconfluent_of_isFree
                  (v := $(globals[0]!.const)) rfl)))
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
      return r
    rows := rows.push row
  -- §3.5 Derives — the fourth verdict.
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
  modifyEnv fun env => rows.foldl (fun e r => preoExt.addEntry e r) env
  logInfo m!"preo {declName}: {n} field(s), {invs.size} invariant(s), \
    {ders.size} derive(s) — `#preo_report {declName}` for the table"

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
  out := out ++ "\n  Every column above is REDUCED out of the row's `.classification`\n"
  out := out ++ "  constant at print time — `Classification.answer` and `.mergeAnswer`,\n"
  out := out ++ "  whose order-independence is `Preo.run_answer_congr`. Nothing is stored.\n"
  out := out ++ "  FREE rows are also stated at document scale as `<invariant>.onState`;\n"
  out := out ++ "  SEAM rows as `<invariant>.seamOnState` (`Preo.seamAlong` — the clash is\n"
  out := out ++ "  transported by PLANTING the field replicas in a document, which is what\n"
  out := out ++ "  fragment 1 said it could not synthesize).\n"
  logInfo out

end Uwueave.Preo
