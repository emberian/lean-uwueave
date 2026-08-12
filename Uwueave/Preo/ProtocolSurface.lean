/-
# Uwueave.Preo.ProtocolSurface — a parser-safe protocol language.

`Uwueave.Protocol` is the semantic core: its `Term` keeps one global strategy
through operations, sequential and parallel composition, finite choice,
bounded repetition, and synchronization.  The original `preo` declaration
accepted that AST only through an opaque Lean term.  This module adds a small,
deliberately data-shaped authoring surface without duplicating the semantics.

Every `preo_protocol` command emits the exact semantic `Term`, the result of
one call to `Protocol.elaborate`, its `Session` and checked `Plan`, an exact
five-currency `ProfileUpperBound`.  There is no scalar cost field and no
per-currency choice of different plans.  Its predictable `Session`, `Plan`, and
`Limits` names are the handoff to the separate planning surface, which owns
catalog generation and search rather than duplicating planner syntax here.

The concrete grammar is punctuation-delimited.  In particular, arbitrary Lean
terms occur only after `over` and `at`; the recursive protocol body is a native
syntax category, so a term cannot greedily consume the following operation or
annotation.  Operation leaves retain all seven demand axes.  Crossing origins
remain `Fin crossings`, hence an out-of-range origin is rejected by the kernel.

Choice is finite and nonempty by grammar.  `selected` is a surface natural for
this first deterministic fragment; the semantic expansion is the constant
selector `fun _ => selected`.  A future strategy-pattern form may enrich the
selector without changing the six-constructor AST or the emitted artifacts.
-/
import Uwueave.Protocol

namespace Uwueave.Preo.ProtocolSurface

open Lean Elab Command

/-! ## §1. Native recursive grammar -/

declare_syntax_cat preoProtocolCurrency
syntax "." &"peerBarrier" : preoProtocolCurrency
syntax "." &"arbiterCut" : preoProtocolCurrency
syntax "." &"networkRound" : preoProtocolCurrency
syntax "." &"userPrompt" : preoProtocolCurrency
syntax "." &"rollback" : preoProtocolCurrency

declare_syntax_cat preoProtocolEvidence
syntax "." &"none" : preoProtocolEvidence
syntax "." &"named" "(" num ")" : preoProtocolEvidence

declare_syntax_cat preoProtocolOrigin
syntax "." &"ambient" : preoProtocolOrigin
syntax "." &"crossing" "(" num ")" : preoProtocolOrigin

declare_syntax_cat preoProtocolAnnotation
syntax "{" &"currency" " := " preoProtocolCurrency ","
  &"participants" " := " "[" num,* "]" ","
  &"scope" " := " num ","
  &"epoch" " := " num ","
  &"evidence" " := " preoProtocolEvidence ","
  &"round" " := " num ","
  &"barrier" " := " num "}" : preoProtocolAnnotation

declare_syntax_cat preoProtocolNeed
syntax "{" &"origin" " := " preoProtocolOrigin ","
  &"demand" " := " preoProtocolAnnotation "}" : preoProtocolNeed

declare_syntax_cat preoProtocolExpr
syntax "." &"operation" "{" &"id" " := " num ","
  &"crossings" " := " num ","
  &"needs" " := " "[" preoProtocolNeed,* "]" "}" : preoProtocolExpr
syntax "." &"seq" "[" preoProtocolExpr "," preoProtocolExpr "]" : preoProtocolExpr
syntax "." &"parallel" "[" preoProtocolExpr "," preoProtocolExpr "]" : preoProtocolExpr
syntax "." &"choice" "{" &"site" " := " num ","
  &"selected" " := " num ","
  &"branches" " := " "[" preoProtocolExpr,+ "]" "}" : preoProtocolExpr
syntax "." &"repeat" "{" &"count" " := " num ","
  &"body" " := " preoProtocolExpr "}" : preoProtocolExpr
syntax "." &"sync" preoProtocolAnnotation : preoProtocolExpr
/-- A parser-recognized refusal sentinel used to make unsupported extensions
fail with a surface-owned diagnostic rather than fall through to Lean terms. -/
syntax "." &"unsupported" "(" str ")" : preoProtocolExpr

/-- Define and elaborate one native protocol at one globally selected strategy.
The emitted namespace contains `Strategy`, `selectedStrategy`, `Term`,
`Elaboration`, `Session`, `Plan`, `Limits`, and `ProfileUpperBound`. -/
syntax (name := preoProtocolCommand) "preo_protocol " ident
  ppSpace "over" ppSpace term:51 ppSpace "at" ppSpace term:51 " := "
  preoProtocolExpr : command

/-! ## §2. Expansion into the one semantic API -/

private def expandCurrency (stx : Syntax) : CommandElabM Term :=
  match stx with
  | `(preoProtocolCurrency| .peerBarrier) =>
      `(Uwueave.Scheduling.Currency.peerBarrier)
  | `(preoProtocolCurrency| .arbiterCut) =>
      `(Uwueave.Scheduling.Currency.arbiterCut)
  | `(preoProtocolCurrency| .networkRound) =>
      `(Uwueave.Scheduling.Currency.networkRound)
  | `(preoProtocolCurrency| .userPrompt) =>
      `(Uwueave.Scheduling.Currency.userPrompt)
  | `(preoProtocolCurrency| .rollback) =>
      `(Uwueave.Scheduling.Currency.rollback)
  | _ => throwErrorAt stx "preo_protocol: unsupported scheduling currency"

private def expandEvidence (stx : Syntax) : CommandElabM Term :=
  match stx with
  | `(preoProtocolEvidence| .none) =>
      `(Uwueave.Scheduling.EvidenceKey.none)
  | `(preoProtocolEvidence| .named($key:num)) =>
      `(Uwueave.Scheduling.EvidenceKey.named $key)
  | _ => throwErrorAt stx "preo_protocol: unsupported evidence key"

private def expandAnnotation (stx : Syntax) : CommandElabM Term := do
  let `(preoProtocolAnnotation| {
      currency := $curStx,
      participants := [$partStxs:num,*],
      scope := $scopeStx:num,
      epoch := $epochStx:num,
      evidence := $evidenceStx,
      round := $roundStx:num,
      barrier := $barrierStx:num }) := stx
    | throwErrorAt stx "preo_protocol: malformed seven-axis demand annotation"
  let curTerm ← expandCurrency curStx
  let evidenceTerm ← expandEvidence evidenceStx
  `( { currency := $curTerm
       participants := [$partStxs,*]
       scope := $scopeStx
       epoch := $epochStx
       evidence := $evidenceTerm
       round := $roundStx
       barrier := $barrierStx : Uwueave.Protocol.Annotation } )

private def expandOrigin (stx : Syntax) : CommandElabM Term :=
  match stx with
  | `(preoProtocolOrigin| .ambient) =>
      `(Uwueave.Scheduling.Origin.ambient)
  | `(preoProtocolOrigin| .crossing($index:num)) =>
      `(Uwueave.Scheduling.Origin.crossing ⟨$index, by omega⟩)
  | _ => throwErrorAt stx "preo_protocol: unsupported demand origin"

private def expandNeed (crossingCount : Syntax) (stx : Syntax) : CommandElabM Term := do
  let `(preoProtocolNeed| {
      origin := $originStx,
      demand := $annotationStx }) := stx
    | throwErrorAt stx "preo_protocol: malformed operation need"
  if let `(preoProtocolOrigin| .crossing($indexStx:num)) := originStx then
    match crossingCount.isNatLit?, indexStx.raw.isNatLit? with
    | some count, some index =>
        if count ≤ index then
          throwErrorAt originStx
            "preo_protocol: crossing origin {index} is outside declared crossing count {count}"
    | _, _ =>
        throwErrorAt originStx
          "preo_protocol: crossing origins and counts must be natural literals"
  let originTerm ← expandOrigin originStx
  let annotationTerm ← expandAnnotation annotationStx
  `( { origin := $originTerm, annotation := $annotationTerm } )

mutual
  private partial def expandBranches (xs : Array Syntax) : CommandElabM Term := do
    if xs.size = 0 then
      throwError "preo_protocol: finite choice requires at least one branch"
    else if xs.size = 1 then
      let last ← expandExpr xs[0]!
      `(Uwueave.Protocol.Branches.one $last)
    else
      let head ← expandExpr xs[0]!
      let tail ← expandBranches xs[1:]
      `(Uwueave.Protocol.Branches.more $head $tail)

  private partial def expandExpr (stx : Syntax) : CommandElabM Term := do
    match stx with
    | `(preoProtocolExpr| .operation {
        id := $opId:num,
        crossings := $crossingCount:num,
        needs := [$needStxs,*] }) =>
        let needTerms ← needStxs.getElems.mapM (expandNeed crossingCount)
        `(Uwueave.Protocol.Term.operation {
            name := $opId
            crossings := fun _ => $crossingCount
            needs := fun _ => [$needTerms,*] })
    | `(preoProtocolExpr| .seq[
        $left, $right]) =>
        let left ← expandExpr left
        let right ← expandExpr right
        `(Uwueave.Protocol.Term.seq $left $right)
    | `(preoProtocolExpr| .parallel[
        $left, $right]) =>
        let left ← expandExpr left
        let right ← expandExpr right
        `(Uwueave.Protocol.Term.parallel $left $right)
    | `(preoProtocolExpr| .choice {
        site := $siteNat:num,
        selected := $chosenNat:num,
        branches := [$branchStxs,*] }) =>
        let branchTerm ← expandBranches branchStxs.getElems
        `(Uwueave.Protocol.Term.choice $siteNat (fun _ => $chosenNat) $branchTerm)
    | `(preoProtocolExpr| .repeat {
        count := $repeatNat:num,
        body := $bodyStx }) =>
        let bodyTerm ← expandExpr bodyStx
        `(Uwueave.Protocol.Term.repeat $repeatNat $bodyTerm)
    | `(preoProtocolExpr| .sync $annotationStx) =>
        let annotationTerm ← expandAnnotation annotationStx
        `(Uwueave.Protocol.Term.sync $annotationTerm)
    | `(preoProtocolExpr| .unsupported($_feature:str)) =>
        throwErrorAt stx
          "preo_protocol: unsupported protocol node; supported nodes are operation, seq, parallel, choice, repeat, and sync"
    | _ => throwErrorAt stx
        "preo_protocol: unsupported protocol node; expected operation, seq, parallel, choice, repeat, or sync"
end

elab_rules : command
  | `(preo_protocol $name:ident over $strategyTy:term at $strategy:term :=
      $treeStx) => do
    let expandedTree ← expandExpr treeStx
    let strategyName := mkIdent (name.getId ++ `Strategy)
    let selectedName := mkIdent (name.getId ++ `selectedStrategy)
    let termName := mkIdent (name.getId ++ `Term)
    let elaborationName := mkIdent (name.getId ++ `Elaboration)
    let sessionName := mkIdent (name.getId ++ `Session)
    let planName := mkIdent (name.getId ++ `Plan)
    let limitsName := mkIdent (name.getId ++ `Limits)
    let boundName := mkIdent (name.getId ++ `ProfileUpperBound)
    let sessionExactName := mkIdent (name.getId ++ `session_exact)
    let planExactName := mkIdent (name.getId ++ `plan_exact)
    let boundExactName := mkIdent (name.getId ++ `profile_bound_exact)
    elabCommand (← `(command|
      /-- The strategy carrier shared by every node in this protocol. -/
      abbrev $strategyName : Type := $strategyTy))
    elabCommand (← `(command|
      /-- The one global strategy selected before denotation and scheduling. -/
      def $selectedName : $strategyName := $strategy))
    elabCommand (← `(command|
      /-- The exact deep AST generated from the native protocol syntax. -/
      def $termName : Uwueave.Protocol.Term $strategyName := $expandedTree))
    elabCommand (← `(command|
      /-- One proof-carrying semantic elaboration of the generated term. -/
      def $elaborationName :
          Uwueave.Protocol.Elaboration $termName $selectedName :=
        Uwueave.Protocol.elaborate $termName $selectedName))
    elabCommand (← `(command|
      /-- The exact session denoted at the selected global strategy. -/
      abbrev $sessionName : Uwueave.Scheduling.Session :=
        ($elaborationName).session))
    elabCommand (← `(command|
      /-- The checked schedule plan carried by the same elaboration. -/
      def $planName : Uwueave.Scheduling.Plan $sessionName :=
        ($elaborationName).plan))
    elabCommand (← `(command|
      /-- All five exact currency coordinates of that one plan. -/
      def $limitsName : Uwueave.Scheduling.Currency → Nat :=
        ($planName).profile))
    elabCommand (← `(command|
      /-- Exact five-currency acceptance; every coordinate uses one plan. -/
      def $boundName :
          Uwueave.Scheduling.ProfileUpperBound $sessionName $limitsName :=
        ($planName).exactProfileUpperBound))
    elabCommand (← `(command|
      theorem $sessionExactName :
          $sessionName = ($termName).denote $selectedName := rfl))
    elabCommand (← `(command|
      theorem $planExactName : $planName = ($elaborationName).plan := rfl))
    elabCommand (← `(command|
      theorem $boundExactName : ($boundName).plan = $planName := rfl))

/-! ## §3. Fully native acceptance fixture -/

preo_protocol NativeFixture over Unit at () :=
  .seq [
    .operation {
      id := 100,
      crossings := 2,
      needs := [
        {
          origin := .crossing(0),
          demand := {
            currency := .peerBarrier,
            participants := [0, 1],
            scope := 7,
            epoch := 3,
            evidence := .named(11),
            round := 0,
            barrier := 5 } },
        {
          origin := .crossing(1),
          demand := {
            currency := .peerBarrier,
            participants := [0, 1],
            scope := 7,
            epoch := 3,
            evidence := .named(11),
            round := 0,
            barrier := 5 } } ] },
    .parallel [
      .choice {
        site := 17,
        selected := 1,
        branches := [
          .sync {
            currency := .arbiterCut,
            participants := [0],
            scope := 20,
            epoch := 4,
            evidence := .none,
            round := 0,
            barrier := 30 },
          .sync {
            currency := .networkRound,
            participants := [0, 1],
            scope := 21,
            epoch := 4,
            evidence := .named(12),
            round := 1,
            barrier := 31 } ] },
      .repeat {
        count := 2,
        body := .sync {
          currency := .userPrompt,
          participants := [1],
          scope := 22,
          epoch := 4,
          evidence := .none,
          round := 2,
          barrier := 32 } } ] ]

/-! The fixture reaches every native constructor with no opaque
`Protocol.Term`.  Its exact session has two crossings and five obligations:
two operation needs, the selected network branch, and two prompt repetitions. -/
theorem native_fixture_exact_shape :
    NativeFixture.Session.crossings = 2
      ∧ NativeFixture.Session.obligations.length = 5 := by
  decide

/-- The emitted profile retains all five currencies independently.  Identity
scheduling deliberately does not coalesce the duplicate peer demands. -/
theorem native_fixture_exact_five_currency_profile :
    NativeFixture.Plan.profile .peerBarrier = 2
      ∧ NativeFixture.Plan.profile .arbiterCut = 0
      ∧ NativeFixture.Plan.profile .networkRound = 1
      ∧ NativeFixture.Plan.profile .userPrompt = 2
      ∧ NativeFixture.Plan.profile .rollback = 0 := by
  decide

/-- Every one of the seven compatibility axes survives native parsing and
semantic elaboration.  The unselected arbiter branch is absent; the selected
network demand and both repeated prompt demands are present verbatim. -/
theorem native_fixture_retains_exact_demands :
    Protocol.sessionDemands NativeFixture.Session =
      [ { currency := .peerBarrier, participants := [0, 1], scope := 7,
          epoch := 3, evidence := .named 11, round := 0, barrier := 5 },
        { currency := .peerBarrier, participants := [0, 1], scope := 7,
          epoch := 3, evidence := .named 11, round := 0, barrier := 5 },
        { currency := .networkRound, participants := [0, 1], scope := 21,
          epoch := 4, evidence := .named 12, round := 1, barrier := 31 },
        { currency := .userPrompt, participants := [1], scope := 22,
          epoch := 4, evidence := .none, round := 2, barrier := 32 },
        { currency := .userPrompt, participants := [1], scope := 22,
          epoch := 4, evidence := .none, round := 2, barrier := 32 } ] := by
  decide

/-! ## §4. Refusals and the effect/coeffect boundary -/

/--
error: preo_protocol: crossing origin 1 is outside declared crossing count 1
-/
#guard_msgs in
preo_protocol BadCrossing over Unit at () :=
  .operation {
    id := 404,
    crossings := 1,
    needs := [
      {
        origin := .crossing(1),
        demand := {
          currency := .peerBarrier,
          participants := [0, 1],
          scope := 7,
          epoch := 3,
          evidence := .none,
          round := 0,
          barrier := 5 } } ] }

/--
error: preo_protocol: unsupported protocol node; supported nodes are operation, seq, parallel, choice, repeat, and sync
-/
#guard_msgs in
preo_protocol UnsupportedRace over Unit at () := .unsupported("race")

/- A native spelling of the two-crossing, one-least-meeting witness. -/
preo_protocol NativeCoalescing over Unit at () :=
  .operation {
    id := 100,
    crossings := 2,
    needs := [
      { origin := .crossing(0),
        demand := {
          currency := .peerBarrier,
          participants := [0, 1],
          scope := 7,
          epoch := 3,
          evidence := .named(11),
          round := 0,
          barrier := 5 } },
      { origin := .crossing(1),
        demand := {
          currency := .peerBarrier,
          participants := [0, 1],
          scope := 7,
          epoch := 3,
          evidence := .named(11),
          round := 0,
          barrier := 5 } } ] }

/- A native ambient synchronization has no crossing but still demands one
peer meeting. -/
preo_protocol NativeAmbient over Unit at () :=
  .sync {
    currency := .peerBarrier,
    participants := [0, 1],
    scope := 7,
    epoch := 3,
    evidence := .named(11),
    round := 0,
    barrier := 5 }

theorem native_coalescing_is_exact_session :
    NativeCoalescing.Session = Scheduling.coalescingSession := rfl

theorem native_ambient_is_exact_session :
    NativeAmbient.Session = Scheduling.ambientBarrierSession := rfl

/-- Native syntax does not turn crossings into meetings. -/
theorem crossings_can_still_exceed_meetings :
    NativeCoalescing.Session.crossings = 2
      ∧ Scheduling.LeastMeetings NativeCoalescing.Session 1
      ∧ 1 < NativeCoalescing.Session.crossings := by
  rw [native_coalescing_is_exact_session]
  exact Scheduling.crossings_can_exceed_meetings

theorem meetings_can_still_exceed_crossings :
    NativeAmbient.Session.crossings = 0
      ∧ Scheduling.LeastMeetings NativeAmbient.Session 1
      ∧ NativeAmbient.Session.crossings < 1 := by
  rw [native_ambient_is_exact_session]
  exact Scheduling.meetings_can_exceed_crossings

end Uwueave.Preo.ProtocolSurface
