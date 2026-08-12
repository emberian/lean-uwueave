/-
# Uwueave.Preo.Elab.Invariant — invariant classification worker

This phase owns the ordered global/seam registry for one invariant row.  It
returns the field seam and document-scale free theorem needed by the later
document-seam fold; report metadata is created only after every positive facet
has elaborated and passed the trust-floor check.
-/
import Uwueave.Preo.Elab.State
import Uwueave.Preo.Elab.Readback

namespace Uwueave.Preo.Elab.Invariant

open Lean Elab Command Term
open Uwueave Uwueave.Catalog Uwueave.Spec

/-- One certified global facet, retained in route order. -/
structure Fired where
  const : Ident
  route : String
  cite : String
  deriving Inhabited

/-- A field-scale seam retained for the declaration-scale composition phase. -/
structure FiredSeam where
  field : Nat
  inv : Ident
  const : Ident
  segTy : Term
  deriving Inhabited

/-- Products of classifying one invariant. -/
structure Result where
  row : Row
  seam? : Option FiredSeam
  freeOnState? : Option Ident
  deriving Inhabited

/-- Emit and classify one invariant in the historical route order. -/
def emit (ctx : State.Context) (inv : Syntax) : CommandElabM Result := do
  let `(preoInv| invariant $nm : $pred $[:= $supplied]?) := inv
    | throwErrorAt inv "preo: malformed invariant"
  let used := Internal.mentions ctx.fieldNames pred
  if used.isEmpty then
    throwErrorAt nm "preo: invariant `{nm.getId}` mentions no field of \
      `{ctx.declName}` — there is no carrier to classify it over. Fields are: \
      {String.intercalate ", " (ctx.fieldNames.toList.map toString)}."
  if used.size > 2 then
    throwErrorAt nm "preo: invariant `{nm.getId}` mentions {used.size} fields \
      ({String.intercalate ", " (used.toList.map toString)}). The cross-field \
      machinery is BINARY — `Spec.Verdict.cross` classifies a relation over \
      `A × B`, and no ternary lift exists in the tree. Split it, or earn the \
      ternary verdict by hand against the joint merge."
  let mut idxs : Array Nat := #[]
  for u in used do
    let some k := ctx.fieldNames.findIdx? (· == u)
      | throwErrorAt nm "preo: internal"
    idxs := idxs.push k
  if idxs.size == 2 && idxs[0]! > idxs[1]! then
    idxs := #[idxs[1]!, idxs[0]!]
  let isCross := idxs.size == 2
  let invId := mkIdent (ctx.declName ++ nm.getId)
  let carrier : Term ←
    if isCross then `($(ctx.carriers[idxs[0]!]!) × $(ctx.carriers[idxs[1]!]!))
    else pure ctx.carriers[idxs[0]!]!
  let readsStr := String.intercalate " × " (idxs.toList.map fun k =>
    ctx.fieldNames[k]!.toString)
  withRef nm do
    if isCross then
      let fA := ctx.fieldIdents[idxs[0]!]!
      let fB := ctx.fieldIdents[idxs[1]!]!
      Internal.emitRequired (← `(command|
        @[reducible] def $invId : Uwueave.Invariant $carrier :=
          fun p => (fun $fA => fun $fB => $pred) p.1 p.2))
    else
      Internal.emitRequired (← `(command|
        @[reducible] def $invId : Uwueave.Invariant $carrier :=
          fun $(ctx.fieldIdents[idxs[0]!]!) => $pred))

    let mut globals : Array Fired := #[]
    let mut tacticSaid := ""
    let vBase := nm.getId ++ `verdict
    let vSuffix : Array String := #["", "₂", "₃", "₄", "₅", "₆"]
    let mkVId : Nat → Ident := fun k =>
      mkIdent (ctx.declName ++ vBase.appendAfter vSuffix[k]!)
    if let some ev := supplied then
      let vId := mkVId globals.size
      Internal.emitRequired (← `(command|
        def $vId : Uwueave.Spec.Verdict $invId := $ev))
      globals := globals.push {
        const := vId
        route := "supplied"
        cite := "author-supplied, kernel-checked: " ++ Internal.renderSyntax ev }
    if ← Internal.canSynth (← `(Uwueave.Tactics.SelectionMerge $carrier)) then
      let vId := mkVId globals.size
      let cite := "Catalog.selection_iconfluent (the merge picks a side)"
      match ← Internal.probeCommand (← `(command|
          def $vId : Uwueave.Spec.Verdict $invId :=
            Uwueave.Spec.Verdict.free
              (Uwueave.Catalog.selection_iconfluent
                Uwueave.Tactics.SelectionMerge.selects $invId))) with
      | .ok _ => globals := globals.push { const := vId, route := "selection", cite }
      | .error _ => pure ()
    if (← Internal.canSynth (← `(Uwueave.Tactics.FinEnum $carrier))) &&
        (← Internal.canSynth (← `(DecidablePred $invId))) then
      let vId := mkVId globals.size
      let cite := "Tactics.classifyFinite (total; classifyFinite_isFree_iff)"
      match ← Internal.probeCommand (← `(command|
          def $vId : Uwueave.Spec.Verdict $invId :=
            Uwueave.Tactics.classifyFinite $invId)) with
      | .ok _ => globals := globals.push { const := vId, route := "classifyFinite", cite }
      | .error _ => pure ()
    if isCross && ctx.fieldKeys[idxs[0]!]!.isNone && ctx.fieldKeys[idxs[1]!]!.isSome then
      let vId := mkVId globals.size
      let cite := "Confluence.keyed_cross_iconfluent applied to \
        Spec.pointsAtExisting_iconfluent (referential integrity for every key, \
        earned once against the JOINT merge and lifted pointwise)"
      match ← Internal.probeCommand (← `(command|
          def $vId : Uwueave.Spec.Verdict $invId :=
            Uwueave.Spec.Verdict.free
              (Uwueave.keyed_cross_iconfluent
                (R := Uwueave.Spec.PointsAtExisting)
                Uwueave.Spec.pointsAtExisting_iconfluent))) with
      | .ok _ => globals := globals.push { const := vId, route := "keyed-cross-FK", cite }
      | .error _ => pure ()
    if isCross then
      let vId := mkVId globals.size
      let cite := "Spec.pointsAtExisting_iconfluent through Verdict.cross_free \
        (referential integrity over grow-only sets, earned against the JOINT merge \
        — no lift produced it and none could)"
      match ← Internal.probeCommand (← `(command|
          def $vId : Uwueave.Spec.Verdict $invId :=
            Uwueave.Spec.Verdict.cross_free Uwueave.Spec.pointsAtExisting_iconfluent)) with
      | .ok _ => globals := globals.push { const := vId, route := "cross-FK", cite }
      | .error _ => pure ()
    if globals.isEmpty then
      let vId := mkVId 0
      let cite := "Tactics.verdict (classify's routes; the term it emits is kernel-checked)"
      match ← Internal.probeCommand (← `(command|
          def $vId : Uwueave.Spec.Verdict $invId := by verdict)) with
      | .ok _ => globals := globals.push { const := vId, route := "verdict tactic", cite }
      | .error why => tacticSaid := why
    for g in globals do
      Internal.floorCheck nm "verdict" (ctx.ns ++ g.const.getId)

    let mut seam? : Option (Ident × Term × String) := none
    if !isCross then
      let seamId := mkIdent (ctx.declName ++ (nm.getId ++ `seam))
      match ← Internal.probeCommand (← `(command|
          def $seamId : Uwueave.Spec.SegVerdict $invId (Bool → Nat) :=
            Uwueave.Preo.budgetSeam _ (by decide))) with
      | .ok _ =>
          Internal.floorCheck nm "seam verdict" (ctx.fullDecl ++ (nm.getId ++ `seam))
          seam? := some (seamId, ← `((Bool → Nat)),
            "FREE within the allocation (Segmented.budget_segmented); the seam is \
             the allocation `Prod.fst`, so spends never coordinate and only a \
             RE-ALLOCATION crosses this seam; scheduling any meeting requires \
             explicit demands. Globally refuted by the carried clash \
             (Preo.budget_not_iconfluent_at).")
      | .error _ => pure ()
      if seam?.isNone then
        match ← Internal.probeCommand (← `(command|
            def $seamId : Uwueave.Spec.SegVerdict $invId $carrier :=
              Uwueave.Spec.SegVerdict.selfSeam
                Uwueave.Spec.atMostOneClash rfl)) with
        | .ok _ =>
            Internal.floorCheck nm "seam verdict" (ctx.fullDecl ++ (nm.getId ++ `seam))
            seam? := some (seamId, carrier,
              "FREE only while the entire field is fixed \
               (SegVerdict.selfSeam on Spec.atMostOneClash). This is the \
               conservative pin seam: every pin-set change coordinates; \
               the carried singleton/singleton clash refutes global freedom.")
        | .error _ => pure ()
      if seam?.isNone && !globals.isEmpty then
        match ← Internal.probeCommand (← `(command|
            def $seamId : Uwueave.Spec.SegVerdict $invId $carrier :=
              Uwueave.Spec.SegVerdict.selfSeam $(globals[0]!.const) rfl)) with
        | .ok _ =>
            Internal.floorCheck nm "seam verdict" (ctx.fullDecl ++ (nm.getId ++ `seam))
            seam? := some (seamId, carrier,
              "FREE only while the entire field is fixed \
               (SegVerdict.selfSeam on the row's certified clash). This is \
               a sound conservative upper bound, not a claim that no coarser \
               seam exists.")
        | .error _ => pure ()
    if globals.isEmpty then
      if let some (seamId, _, _) := seam? then
        let vId := mkVId 0
        Internal.emitRequired (← `(command|
          def $vId : Uwueave.Spec.Verdict $invId :=
            Uwueave.Spec.SegVerdict.toClash $seamId))
        globals := globals.push {
          const := vId
          route := "seam⇒clash"
          cite := "Spec.SegVerdict.toClash — the seam's own carried clash \
            (Preo.seam_forces_clash: a seam FORCES this column to ESCALATES, it \
            never competes with it)" }
        Internal.floorCheck nm "verdict" (ctx.ns ++ vId.getId)

    let mut oblId? : Option Ident := none
    if globals.isEmpty && seam?.isNone then
      let hasEnum ← Internal.canSynth (← `(Uwueave.Tactics.FinEnum $carrier))
      let enumNote := if hasEnum then
          "the carrier enumerates, so `classifyFinite` was blocked on decidability \
           rather than on the carrier (an unbounded `∀ n : Nat` is the usual cause); "
        else
          "the carrier has neither `SelectionMerge` (which would free every invariant \
           over it) nor `FinEnum` (which would let `classifyFinite` decide); "
      let seamNote := if isCross then
          "no seam rule is tried on a cross-field row (the registry's \
           entries are single-carrier fibers); "
        else
          "the seam registry (`Preo.budgetSeam`, the pin ceiling, and the \
           certified-clash self seam) did not typecheck at this invariant; "
      let why := enumNote ++ seamNote ++ "and `verdict` said: " ++ tacticSaid.take 400 ++
        " — DISCHARGE by supplying evidence with `:= <term>` (a catalog verdict such \
         as `Spec.atMostOneClash`, or a hand proof), or by restating the field over \
         a finite index type."
      let oId := mkIdent (ctx.declName ++ (nm.getId ++ `obligation))
      Internal.emitRequired (← `(command|
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

    let classId := mkIdent (ctx.declName ++ (nm.getId ++ `classification))
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
    Internal.emitRequired (← `(command|
      /-- The row's accumulated facets. `#preo_report` reduces its `.answer`;
      nothing about the verdict is stored as text. -/
      def $classId : Uwueave.Preo.Classification $invId (fun _ : $carrier => ()) where
        global := $gList
        seams := $sList
        mergeability := []
        obligations := $oList))
    let classFull := ctx.fullDecl ++ (nm.getId ++ `classification)
    let ans ← Readback.readAnswer classFull
    let mut freeOnState? : Option Ident := none
    if ans == some (some true) then
      let onStateId := mkIdent (ctx.declName ++ (nm.getId ++ `onState))
      if isCross then
        let accA := mkIdent (ctx.declName ++ ctx.fieldNames[idxs[0]!]!)
        let accB := mkIdent (ctx.declName ++ ctx.fieldNames[idxs[1]!]!)
        match ← Internal.probeCommand (← `(command|
            theorem $onStateId :
                Uwueave.IConfluent (S := $(ctx.stateId))
                  (fun s => $invId ($accA s, $accB s)) :=
              Uwueave.Preo.proj_iconfluent
                (π := fun s : $(ctx.stateId) => ($accA s, $accB s))
                (fun _ _ => rfl)
                (Uwueave.Tactics.iconfluent_of_isFree
                  (v := $(globals[0]!.const)) rfl))) with
        | .ok _ => freeOnState? := some onStateId
        | .error _ => pure ()
      else
        let fname := ctx.fieldNames[idxs[0]!]!
        let accId := mkIdent (ctx.declName ++ fname)
        let homId := mkIdent (ctx.declName ++ (fname ++ `merge_hom))
        match ← Internal.probeCommand (← `(command|
            theorem $onStateId :
                Uwueave.IConfluent (S := $(ctx.stateId))
                  (fun s => $invId ($accId s)) :=
              Uwueave.Preo.proj_iconfluent $homId
                (Uwueave.Tactics.iconfluent_of_isFree
                  (v := $(globals[0]!.const)) rfl))) with
        | .ok _ => freeOnState? := some onStateId
        | .error _ => pure ()
    if let some (seamId, segTy, _) := seam? then
      let fname := ctx.fieldNames[idxs[0]!]!
      let accId := mkIdent (ctx.declName ++ fname)
      let homId := mkIdent (ctx.declName ++ (fname ++ `merge_hom))
      let plantId := mkIdent (ctx.declName ++ (fname ++ `plant))
      let projEq := mkIdent (ctx.declName ++ (fname ++ `plant_proj))
      let mergeEq := mkIdent (ctx.declName ++ (fname ++ `plant_merge))
      let _ ← Internal.probeCommand (← `(command|
        /-- ⚠ The row's seam, read at the WHOLE declared document: coordinate
        only when this field's segment changes, and a same-segment sync can
        move nothing else. -/
        def $(mkIdent (ctx.declName ++ (nm.getId ++ `seamOnState))) :
            Uwueave.Spec.SegVerdict (S := $(ctx.stateId))
              (fun d => $invId ($accId d)) $segTy :=
          Uwueave.Preo.seamAlong $accId $homId $plantId $projEq $mergeEq $seamId))
    let routes := String.intercalate " · " (globals.toList.map (·.route)) ++
      (if seam?.isSome then " · seam" else "")
    let row : Row := {
      decl := ctx.fullDecl
      kind := if isCross then .cross else .invariant
      name := nm.getId.toString
      detail := readsStr
      detail₂ := if routes.isEmpty then "—" else routes
      evidence := classFull
      isObligation := oblId?.isSome
      cite := if let some o := oblId? then
          "UNRESOLVED — " ++ (globals.toList.map (·.cite)).foldl (· ++ ·) "" ++
            s!"see `{ctx.fullDecl ++ o.getId.replacePrefix ctx.declName .anonymous}`"
        else String.intercalate " ⊕ " (globals.toList.map (·.cite))
      seamCite := match seam? with | some (_, _, s) => s | none => "" }
    return {
      row
      seam? := seam?.map fun (seamId, segTy, _) =>
        { field := idxs[0]!, inv := invId, const := seamId, segTy }
      freeOnState? }

end Uwueave.Preo.Elab.Invariant
