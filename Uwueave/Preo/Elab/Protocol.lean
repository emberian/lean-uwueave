/-
# Uwueave.Preo.Elab.Protocol — protocol/session elaboration cores.

This module contains no registered command elaborator.  The public surface
facades own registration and delegate here, so importing the implementation
cannot install a second parser handler.  Both protocol spellings end in the
same `Uwueave.Protocol` semantic API.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Protocol

namespace Uwueave.Preo.Elab

open Lean Elab Command Internal

namespace Protocol

/-- Emit the opaque `protocol` items nested in a `preo` declaration and return
their report rows.  Registration and row-extension mutation remain in the
facade. -/
def emitOpaqueProtocols (declName ns fullDecl : Name) (protocols : Array Syntax) :
    CommandElabM (Array Row) := withEnvTransaction do
  let mut rows : Array Row := #[]
  for protocol in protocols do
    let `(preoProtocol| protocol $nm over $strategyTy := $body) := protocol
      | throwErrorAt protocol "preo: malformed protocol declaration"
    let protocolId := mkIdent (declName ++ nm.getId)
    emitRequired (← `(command|
      /-- A typed protocol AST. Its denotation and profile are supplied only by
      `Protocol.Term.denote` and `.profile`. -/
      def $protocolId : Uwueave.Protocol.Term $strategyTy := $body))
    floorCheck nm "protocol declaration" (ns ++ protocolId.getId)
    rows := rows.push {
      decl := fullDecl, kind := .protocol, name := nm.getId.toString
      detail := renderSyntax strategyTy, detail₂ := renderSyntax body
      evidence := ns ++ protocolId.getId, isObligation := false
      cite := "Protocol.Term (typed AST; semantics stay in Term.denote/profile)"
      seamCite := "" }
  pure rows

/-- Emit the `session` items nested in a `preo` declaration and return their
report rows.  The three modes preserve the exact historical names, types,
diagnostics, and one-global-strategy construction. -/
def emitSessions (declName ns fullDecl : Name) (sessions : Array Syntax) :
    CommandElabM (Array Row) := withEnvTransaction do
  let mut rows : Array Row := #[]
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
      emitRequired (← `(command|
        /-- Proof-carrying protocol elaboration at the selected strategy. -/
        def $sessionId := Uwueave.Protocol.elaborate $protocolId $strategy))
      emitRequired (← `(command|
        /-- The checked schedule projected from this elaboration. -/
        def $planId := Uwueave.Protocol.Elaboration.plan $sessionId))
      emitRequired (← `(command|
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
      emitRequired (← `(command|
        def $sessionId := Uwueave.Protocol.elaborate $protocolId $strategy))
      emitRequired (← `(command|
        def $planId := Uwueave.Protocol.Elaboration.plan $sessionId))
      emitRequired (← `(command|
        def $upperId := Uwueave.Protocol.Elaboration.upperBound $sessionId))
      emitRequired (← `(command|
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
      emitRequired (← `(command|
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
  pure rows

end Protocol
end Uwueave.Preo.Elab

namespace Uwueave.Preo.ProtocolSurface

open Lean Elab Command Uwueave.Preo.Elab.Internal

/-! Native recursive grammar.  These parser declarations live with the core;
the facade installs the sole public handler. -/

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
syntax "." &"unsupported" "(" str ")" : preoProtocolExpr

syntax (name := preoProtocolCommand) "preo_protocol " ident
  ppSpace "over" ppSpace term:51 ppSpace "at" ppSpace term:51 " := "
  preoProtocolExpr : command

private def expandCurrency (stx : Syntax) : CommandElabM Term :=
  match stx with
  | `(preoProtocolCurrency| .peerBarrier) => `(Uwueave.Scheduling.Currency.peerBarrier)
  | `(preoProtocolCurrency| .arbiterCut) => `(Uwueave.Scheduling.Currency.arbiterCut)
  | `(preoProtocolCurrency| .networkRound) => `(Uwueave.Scheduling.Currency.networkRound)
  | `(preoProtocolCurrency| .userPrompt) => `(Uwueave.Scheduling.Currency.userPrompt)
  | `(preoProtocolCurrency| .rollback) => `(Uwueave.Scheduling.Currency.rollback)
  | _ => throwErrorAt stx "preo_protocol: unsupported scheduling currency"

private def expandEvidence (stx : Syntax) : CommandElabM Term :=
  match stx with
  | `(preoProtocolEvidence| .none) => `(Uwueave.Scheduling.EvidenceKey.none)
  | `(preoProtocolEvidence| .named($key:num)) => `(Uwueave.Scheduling.EvidenceKey.named $key)
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
  | `(preoProtocolOrigin| .ambient) => `(Uwueave.Scheduling.Origin.ambient)
  | `(preoProtocolOrigin| .crossing($index:num)) =>
      `(Uwueave.Scheduling.Origin.crossing ⟨$index, by omega⟩)
  | _ => throwErrorAt stx "preo_protocol: unsupported demand origin"

private def expandNeed (crossingCount : Syntax) (stx : Syntax) : CommandElabM Term := do
  let `(preoProtocolNeed| { origin := $originStx, demand := $annotationStx }) := stx
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
        id := $opId:num, crossings := $crossingCount:num,
        needs := [$needStxs,*] }) =>
        let needTerms ← needStxs.getElems.mapM (expandNeed crossingCount)
        `(Uwueave.Protocol.Term.operation {
            name := $opId
            crossings := fun _ => $crossingCount
            needs := fun _ => [$needTerms,*] })
    | `(preoProtocolExpr| .seq[$left, $right]) =>
        let left ← expandExpr left
        let right ← expandExpr right
        `(Uwueave.Protocol.Term.seq $left $right)
    | `(preoProtocolExpr| .parallel[$left, $right]) =>
        let left ← expandExpr left
        let right ← expandExpr right
        `(Uwueave.Protocol.Term.parallel $left $right)
    | `(preoProtocolExpr| .choice {
        site := $siteNat:num, selected := $chosenNat:num,
        branches := [$branchStxs,*] }) =>
        let branchTerm ← expandBranches branchStxs.getElems
        `(Uwueave.Protocol.Term.choice $siteNat (fun _ => $chosenNat) $branchTerm)
    | `(preoProtocolExpr| .repeat { count := $repeatNat:num, body := $bodyStx }) =>
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

/-- Non-registered native protocol command core. -/
def elabNativeProtocolCore : CommandElab := fun stx =>
  Uwueave.Preo.Elab.Internal.withEnvTransaction do
  let `(command| preo_protocol $name:ident over $strategyTy:term at $strategy:term :=
      $treeStx) := stx
    | throwError "preo_protocol: malformed declaration"
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
  emitRequired (← `(command|
    /-- The strategy carrier shared by every node in this protocol. -/
    abbrev $strategyName : Type := $strategyTy))
  emitRequired (← `(command|
    /-- The one global strategy selected before denotation and scheduling. -/
    def $selectedName : $strategyName := $strategy))
  emitRequired (← `(command|
    /-- The exact deep AST generated from the native protocol syntax. -/
    def $termName : Uwueave.Protocol.Term $strategyName := $expandedTree))
  emitRequired (← `(command|
    /-- One proof-carrying semantic elaboration of the generated term. -/
    def $elaborationName : Uwueave.Protocol.Elaboration $termName $selectedName :=
      Uwueave.Protocol.elaborate $termName $selectedName))
  emitRequired (← `(command|
    /-- The exact session denoted at the selected global strategy. -/
    abbrev $sessionName : Uwueave.Scheduling.Session := ($elaborationName).session))
  emitRequired (← `(command|
    /-- The checked schedule plan carried by the same elaboration. -/
    def $planName : Uwueave.Scheduling.Plan $sessionName := ($elaborationName).plan))
  emitRequired (← `(command|
    /-- All five exact currency coordinates of that one plan. -/
    def $limitsName : Uwueave.Scheduling.Currency → Nat := ($planName).profile))
  emitRequired (← `(command|
    /-- Exact five-currency acceptance; every coordinate uses one plan. -/
    def $boundName : Uwueave.Scheduling.ProfileUpperBound $sessionName $limitsName :=
      ($planName).exactProfileUpperBound))
  emitRequired (← `(command|
    theorem $sessionExactName : $sessionName = ($termName).denote $selectedName := rfl))
  emitRequired (← `(command|
    theorem $planExactName : $planName = ($elaborationName).plan := rfl))
  emitRequired (← `(command|
    theorem $boundExactName : ($boundName).plan = $planName := rfl))

end Uwueave.Preo.ProtocolSurface
