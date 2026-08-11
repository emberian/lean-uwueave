/-
# Uwueave.Preo.Elab — the elaborator: a `preo` declaration becomes Lean, and
its invariants become verdict **terms**.

This is the half of `PREOSCRIPTING.md` §10's unbuilt row that does the work.
`Uwueave.Preo.Syntax` holds the grammar, the field kinds and the one lift;
here is what a declaration turns into and how the answers are reached.

## What one `preo N where …` emits, in order

For fields `f₁ : k₁ … fₙ : kₙ` and invariants `i₁ … iₘ`:

```
abbrev  N.State                          := c₁ × (c₂ × … cₙ)      -- right-nested
abbrev  N.fⱼ (s : N.State)               := s.2…2.1               -- the projection
example : MergeState N.State             := inferInstance         -- CHECKED, not assumed
theorem N.fⱼ.merge_hom (x y : N.State)   : N.fⱼ (x ⊔ y) = N.fⱼ x ⊔ N.fⱼ y := rfl
@[reducible] def N.iₖ : Invariant cⱼ     := fun fⱼ => <predicate>
def     N.iₖ.verdict : Verdict N.iₖ      := <route>               -- a real term…
def     N.iₖ.obligation : Obligation N.iₖ                         -- …or, if no route, this
theorem N.iₖ.onState : IConfluent (fun s => N.iₖ (N.fⱼ s))        -- FREE rows only
```

Two of those lines are the point of the whole exercise:

  * `N.iₖ.verdict` is a `Spec.Verdict` **value**, so it cannot exist without
    its evidence — `free` carries an `IConfluent` proof and `clash` carries two
    legal replicas plus the refutation. A wrong verdict is not a thing this
    elaborator can print; the failure available to it is to produce *no*
    verdict, which is `Syntax`'s §3 `Obligation`.
  * `N.iₖ.onState` is the field-scoped result read at the declared document's
    scale, through `Preo.proj_iconfluent` with a `rfl` homomorphism. Its proof
    argument is `Tactics.iconfluent_of_isFree … rfl`, so it typechecks **only
    if the verdict really computed `free`** — the lift is welded to the
    computed answer rather than to the elaborator's opinion of it.

## The routes — four, in order, first match wins

  1. **supplied** — the author wrote `:= <term>`; it is elaborated at type
     `Verdict N.iₖ` and the kernel checks it. Reported as `supplied`, never as
     `derived`, because the elaborator did not classify anything.
  2. **selection** — `Tactics.SelectionMerge cⱼ` synthesizes, so the carrier's
     merge picks a side and `Catalog.selection_iconfluent` makes *every*
     invariant over it free. Works on infinite carriers (`LWW`, `Counter`).
  3. **finite decision** — `Tactics.FinEnum cⱼ` and `DecidablePred N.iₖ`
     synthesize, so `Tactics.classifyFinite` returns a verdict for every input
     and `classifyFinite_isFree_iff` says it answers `free` exactly when the
     invariant is I-confluent. Total, decisive both ways, and backed by the
     enumeration's own completeness rather than a probe pool's silence — which
     is why it is tried before the search below.
  4. **search** — the `verdict` tactic (`Uwueave.Tactics`), run through
     `tryEmit` so that a route which does not apply leaves *nothing* behind.
     This is what reaches infinite grow-only sets: `classify`'s
     monotone-closure route frees `notes 0 = true` over `GrowSet Nat`, and its
     probe pool refutes a mutex-shaped invariant there. It can fail, and when
     it does its error is quoted into the `Obligation` rather than discarded —
     `classify`'s errors are written to be the bug report.

Otherwise: an `Obligation`, naming the routes tried and what would close it.
There is no fifth branch and no default — `classify`'s discipline ("a tactic
that can produce a wrong verdict is worse than no tactic") is inherited whole,
and every route above ends in a term the kernel checked.

⚠ And whichever route ran, the emitted verdict is checked against the tree's
axiom floor (`propext · Classical.choice · Quot.sound`) **before a row
exists**. That guard is what makes the *supplied* route safe: a `sorry`-backed
`Verdict` prints exactly like a real one, and no amount of reading the table
would tell.

## What it refuses, loudly

  * an unknown field kind — the five are named in the error;
  * a field kind with a missing or surplus argument;
  * an invariant mentioning **no** field (it would have no carrier);
  * an invariant mentioning **two or more** fields — that is
    `Spec.Verdict.cross`, where no per-field lift applies and none can
    (`Catalog.lww_cross_field_not_iconfluent`). Refused rather than guessed;
  * a declaration with no fields.
-/
import Uwueave.Preo.Syntax

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

/-- Reduce `<const>.isFree` to a `Bool`. This is how the report reads a verdict
back off the term that carries it — the answer is never stored. -/
private def verdictIsFree (c : Name) : CommandElabM (Option Bool) :=
  liftTermElabM do
    try
      let e ← mkAppM ``Uwueave.Spec.Verdict.isFree #[← mkConstWithFreshMVarLevels c]
      let r ← withDefault <| whnf e
      if r.isConstOf ``Bool.true then pure (some true)
      else if r.isConstOf ``Bool.false then pure (some false)
      else pure none
    catch _ => pure none

/-- Emit a command, and roll the environment (and the message log) back if it
did not go through cleanly. This is how a *route* may be attempted rather than
merely probed — `by verdict` cannot be predicted without running it, and a
route that does not apply must leave no trace, not a logged error and a
`sorry`-bodied definition.

Only `env` and `messages` are restored: rolling back the whole command state
would rewind the macro-scope counter, and two commands sharing a scope is a
hygiene bug waiting to be blamed on something else.

On failure it returns *what went wrong*, so an `Obligation` can quote the
classifier's own words rather than a generic shrug: `classify`'s errors are
written to be the bug report ("the invariant is not decidable at a concrete
state", with the state), and throwing that away would be the honest-label sin
in miniature. -/
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

/-- The axioms a constant depends on, minus Lean's own floor. `Uwueave.Audit`
holds every constant in the tree to `{propext, Classical.choice, Quot.sound}`;
a verdict recorded in a `preo` report answers to it **at emission**, because
the report is read by a human who will not run the audit first, and because
`sorry` and `native_decide` both produce a `Verdict` that prints exactly like
a real one. -/
private def offFloor (c : Name) : CommandElabM (Array Name) := do
  let axs ← collectAxioms c
  return axs.filter fun a =>
    !([``propext, ``Classical.choice, ``Quot.sound].contains a)

/-- The carrier type of a field kind. Five kinds, each an existing catalog
type with a proved `MergeState`; nothing new is minted here. -/
private def carrierOf (kind : Ident) (arg? : Option Term) : CommandElabM Term := do
  let k := kind.getId.toString
  match k, arg? with
  | "GrowSet", some a => `(Uwueave.Catalog.GSet $a)
  | "Slot",    some a => `(Uwueave.Preo.Slot $a)
  | "Escrow",  some a => `(Uwueave.Catalog.Escrow $a)
  | "Counter", none   => `(Nat)
  | "LWW",     none   => `(Uwueave.Catalog.LWW)
  | "GrowSet", none | "Slot", none | "Escrow", none =>
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
      throwErrorAt kind "preo: unknown field kind `{k}`. The fragment has five: \
        `GrowSet α` (grow-only set), `Slot α` (a grow-only set carrying a \
        uniqueness ceiling), `Escrow ι` (per-replica quota spend), `Counter` \
        (`Nat` under max), `LWW` (last-writer-wins register). Each supplies a \
        carrier and a proved `MergeState` from `Uwueave.Catalog`."

/-- Every field name mentioned in a term. This is the *entire* syntactic
analysis the elaborator performs on a predicate: which field it reads decides
the carrier the invariant is classified over. Everything else about the
predicate is left to Lean.

The root component is what counts, because dot notation arrives as **one**
identifier: `title.ts` is a single ident named `title.ts`, and reading it as
"mentions no field" cost a real (and initially baffling) failure on an `LWW`
row.

⚠ It is a syntactic over-approximation, deliberately: an occurrence shadowed by
an inner binder (`∀ notes, …` inside an invariant) still counts as a mention.
That can misattribute a row to the wrong field or refuse a declaration that
would have been fine — both loud — but it cannot produce a wrong verdict,
because whatever carrier it picks, the invariant is then classified *on that
carrier* by a route that ends in a checked term. -/
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

/-! ## §2. The declaration elaborator -/

/-- The projection path to field `i` of `n`, as syntax over `s`: `.2` repeated,
then `.1` unless it is the last field. A one-field declaration projects with
the identity, so its state type *is* the field's carrier. -/
private def projPath (i n : Nat) : CommandElabM Term := do
  let mut e : Term ← `(s)
  for _ in [0:i] do
    e ← `($e.2)
  if i + 1 < n then e ← `($e.1)
  return e

@[command_elab preoDecl]
def elabPreoDecl : CommandElab := fun stx => do
  let `(command| preo $declId:ident where $fs:preoField* $invs:preoInv*) := stx
    | throwError "preo: malformed declaration"
  let declName := declId.getId
  let ns ← getCurrNamespace
  let fullDecl := ns ++ declName
  if fs.isEmpty then
    throwErrorAt declId "preo: `{declName}` declares no fields — a state type \
      with no fields has nothing to classify. Add `field <name> : <kind>`."
  -- §2.1 Fields: name, kind syntax, carrier.
  let mut fieldIdents : Array Ident := #[]
  let mut fieldKinds : Array String := #[]
  let mut carriers : Array Term := #[]
  for f in fs do
    let `(preoField| field $nm : $k $[$a]?) := f
      | throwErrorAt f "preo: malformed field"
    if fieldIdents.any (·.getId == nm.getId) then
      throwErrorAt nm "preo: duplicate field `{nm.getId}`"
    fieldIdents := fieldIdents.push nm
    fieldKinds := fieldKinds.push (pp k ++ (a.map (fun t => " " ++ pp t)).getD "")
    carriers := carriers.push (← carrierOf k a)
  let n := carriers.size
  -- §2.2 The state type: carriers, right-nested.
  let mut stateTy : Term := carriers[n - 1]!
  for i in [0:n-1] do
    stateTy ← `($(carriers[n - 2 - i]!) × $stateTy)
  let stateId := mkIdent (declName ++ `State)
  elabCommand (← `(command|
    /-- The declared state: the field carriers, right-nested. Its `MergeState`
    is inherited from the product and pointwise instances — the `example` below
    is the check that it really is. -/
    abbrev $stateId : Type := $stateTy))
  -- §2.3 Accessors, the checked `MergeState`, and each field's merge
  -- homomorphism (`rfl`, because the product merge is componentwise by
  -- definition — `Uwueave.prod_merge_fst`).
  for i in [0:n] do
    let accId := mkIdent (declName ++ fieldIdents[i]!.getId)
    let body ← projPath i n
    elabCommand (← `(command| abbrev $accId (s : $stateId) : $(carriers[i]!) := $body))
    let homId := mkIdent (declName ++ (fieldIdents[i]!.getId ++ `merge_hom))
    elabCommand (← `(command|
      theorem $homId (x y : $stateId) :
          $accId (Uwueave.MergeState.merge x y)
            = Uwueave.MergeState.merge ($accId x) ($accId y) := rfl))
  elabCommand (← `(command| example : Uwueave.MergeState $stateId := inferInstance))
  let mut rows : Array Row := #[]
  for i in [0:n] do
    rows := rows.push
      { decl := fullDecl, isField := true, name := fieldIdents[i]!.getId.toString
        detail := fieldKinds[i]!, detail₂ := pp carriers[i]!
        evidence := fullDecl ++ (fieldIdents[i]!.getId ++ `merge_hom)
        isObligation := false, cite := "MergeState by inferInstance (checked)" }
  -- §2.4 Invariants.
  for inv in invs do
    let `(preoInv| invariant $nm : $pred $[:= $supplied]?) := inv
      | throwErrorAt inv "preo: malformed invariant"
    let fieldNames := fieldIdents.map (·.getId)
    let used := mentions fieldNames pred
    if used.isEmpty then
      throwErrorAt nm "preo: invariant `{nm.getId}` mentions no field of \
        `{declName}` — there is no carrier to classify it over. Fields are: \
        {String.intercalate ", " (fieldNames.toList.map toString)}."
    if used.size > 1 then
      throwErrorAt nm "preo: invariant `{nm.getId}` mentions {used.size} fields \
        ({String.intercalate ", " (used.toList.map toString)}) — that is a \
        CROSS-FIELD invariant, and it is outside this fragment. No per-field \
        lift produces one and none can \
        (`Catalog.lww_cross_field_not_iconfluent` refutes the candidate); it \
        must be earned against the joint merge as a `Spec.Verdict.cross`, by \
        hand, as `Spec.refIntVerdict` and `WeaveState.bookmarksVerdict` are. \
        Classify one field per invariant, or write the cross verdict yourself."
    let fieldName := used[0]!
    let some fi := fieldNames.findIdx? (· == fieldName) | throwErrorAt nm "preo: internal"
    let fieldIdent := fieldIdents[fi]!
    let carrier := carriers[fi]!
    let invId := mkIdent (declName ++ nm.getId)
    let row : Row ← withRef nm do
      -- The invariant, with the FIELD NAME ITSELF as the state binder: the
      -- predicate reads exactly as written. `@[reducible]` so `DecidablePred`
      -- synthesis can see through the definition (a plain `def` hides its own
      -- decidability — `Segmented.BudgetInv` is the tree's standing example).
      elabCommand (← `(command|
        @[reducible] def $invId : Uwueave.Invariant $carrier :=
          fun $fieldIdent => $pred))
      let verdictId := mkIdent (declName ++ (nm.getId ++ `verdict))
      let verdictFull := fullDecl ++ (nm.getId ++ `verdict)
      let mut route : Option (String × String) := none
      let mut tacticSaid : String := ""
      if let some ev := supplied then
        elabCommand (← `(command|
          def $verdictId : Uwueave.Spec.Verdict $invId := $ev))
        route := some ("supplied", "author-supplied, kernel-checked: " ++ pp ev)
      else if ← canSynth (← `(Uwueave.Tactics.SelectionMerge $carrier)) then
        elabCommand (← `(command|
          def $verdictId : Uwueave.Spec.Verdict $invId :=
            Uwueave.Spec.Verdict.free
              (Uwueave.Catalog.selection_iconfluent
                Uwueave.Tactics.SelectionMerge.selects $invId)))
        route := some ("selection", "Catalog.selection_iconfluent (the merge picks a side)")
      else if (← canSynth (← `(Uwueave.Tactics.FinEnum $carrier)))
            && (← canSynth (← `(DecidablePred $invId))) then
        elabCommand (← `(command|
          def $verdictId : Uwueave.Spec.Verdict $invId :=
            Uwueave.Tactics.classifyFinite $invId))
        route := some ("classifyFinite", "Tactics.classifyFinite (total; classifyFinite_isFree_iff)")
      else
        match ← tryEmit (← `(command|
            def $verdictId : Uwueave.Spec.Verdict $invId := by verdict)) with
        | .ok _ => route := some ("verdict tactic",
            "Tactics.verdict (classify's routes; the term it emits is kernel-checked)")
        | .error why => tacticSaid := why
      -- ⚠ Whatever route ran, the evidence answers to the tree's own floor.
      if route.isSome then
        let stray ← offFloor verdictFull
        unless stray.isEmpty do
          throwErrorAt nm "preo: the verdict for `{nm.getId}` depends on \
            {String.intercalate ", " (stray.toList.map toString)} — outside the \
            axiom floor `propext · Classical.choice · Quot.sound` that \
            `#audit_floor` holds the whole tree to. A `sorry` here is a verdict \
            with a hole in it, and `native_decide` is the compiled evaluator \
            rather than the kernel; a row printed off either would be exactly \
            the failure this table exists to make impossible. No row is \
            recorded."
      match route with
      | none =>
        -- No route. Say so as an `Obligation` — never as a verdict, and never
        -- as silence.
        let hasEnum ← canSynth (← `(Uwueave.Tactics.FinEnum $carrier))
        let enumNote :=
          if hasEnum then
            "the carrier enumerates, so `classifyFinite` was blocked on decidability \
             rather than on the carrier (an unbounded `∀ n : Nat` is the usual cause); "
          else
            "the carrier has neither `SelectionMerge` (which would free every invariant \
             over it) nor `FinEnum` (which would let `classifyFinite` decide); "
        let why :=
          enumNote ++ "and `verdict` said: " ++ tacticSaid.take 400 ++
          " — DISCHARGE by supplying evidence with `:= <term>` (a catalog verdict such \
           as `Spec.atMostOneClash`, or a hand proof), or by restating the field over \
           a finite index type."
        let oblId := mkIdent (declName ++ (nm.getId ++ `obligation))
        elabCommand (← `(command|
          def $oblId : Uwueave.Preo.Obligation $invId where
            invName := $(Syntax.mkStrLit nm.getId.toString)
            onField := $(Syntax.mkStrLit fieldName.toString)
            tried := ["selection (Catalog.selection_iconfluent)",
                      "finite decision (Tactics.classifyFinite)",
                      "search (the `verdict` tactic)"]
            discharge := $(Syntax.mkStrLit why)))
        let r : Row :=
          { decl := fullDecl, isField := false, name := nm.getId.toString
            detail := fieldName.toString, detail₂ := "—"
            evidence := fullDecl ++ (nm.getId ++ `obligation)
            isObligation := true, cite := why }
        return r
      | some (routeName, cite) =>
        -- The verdict exists. If it computed `free`, weld it to the declared
        -- state type; a clash does not travel this way and the report says so.
        if (← verdictIsFree verdictFull) == some true then
          let accId := mkIdent (declName ++ fieldName)
          let homId := mkIdent (declName ++ (fieldName ++ `merge_hom))
          let onStateId := mkIdent (declName ++ (nm.getId ++ `onState))
          elabCommand (← `(command|
            theorem $onStateId :
                Uwueave.IConfluent (S := $stateId) (fun s => $invId ($accId s)) :=
              Uwueave.Preo.proj_iconfluent $homId
                (Uwueave.Tactics.iconfluent_of_isFree (v := $verdictId) rfl)))
        let r : Row :=
          { decl := fullDecl, isField := false, name := nm.getId.toString
            detail := fieldName.toString, detail₂ := routeName
            evidence := verdictFull, isObligation := false, cite := cite }
        return r
    rows := rows.push row
  modifyEnv fun env => rows.foldl (fun e r => preoExt.addEntry e r) env
  let nInv := invs.size
  logInfo m!"preo {declName}: {n} field(s), {nInv} invariant(s) — \
    `#preo_report {declName}` for the table"

/-! ## §3. The report -/

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
  let mut out := s!"preo {decl}\n  state    {decl}.State  (MergeState by inferInstance — checked by an emitted `example`)\n"
  out := out ++ "\n  FIELD                 KIND                  CARRIER\n"
  for r in rows do
    if r.isField then
      out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
  out := out ++ "\n  INVARIANT             ON FIELD    VERDICT     ROUTE           EVIDENCE\n"
  for r in rows do
    unless r.isField do
      let verdict ←
        if r.isObligation then pure "UNRESOLVED"
        else match ← verdictIsFree r.evidence with
          | some true => pure "FREE"
          | some false => pure "ESCALATES"
          | none => pure "?? (the verdict term did not reduce — report this)"
      out := out ++
        s!"  {pad r.name 20}  {pad r.detail 10}  {pad verdict 10}  {pad r.detail₂ 14}  {r.evidence}\n"
      out := out ++ s!"      ↳ {r.cite}\n"
  out := out ++ "\n  FREE rows are also stated at document scale as `<invariant>.onState`.\n"
  out := out ++ "  An ESCALATES row is NOT: transporting a clash needs a legal value for every\n"
  out := out ++ "  other field (`Spec.Verdict.prodClashRight`), which this elaborator cannot\n"
  out := out ++ "  synthesize — `WeaveState.core₀` is that job done by hand.\n"
  logInfo out

end Uwueave.Preo
