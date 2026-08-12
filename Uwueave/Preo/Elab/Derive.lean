/-
# Uwueave.Preo.Elab.Derive — ordinary Lean derive worker

This module owns the single-field syntactic dependency check and the ordered
mergeability registry for ordinary `derive` rows.  The registry still proves
every successful route by elaborating the closed theorem against the generated
computation; this worker merely removes it from the monolithic command driver.
-/
import Uwueave.Preo.Classification
import Uwueave.Preo.Elab.Future

namespace Uwueave.Preo.Elab.Derive

open Lean Elab Command Term

/-- The declaration-scale state needed to emit an ordinary derive. Array
indices are shared with the field phase and must remain aligned. -/
structure Context extends Future.Context where
  stateId : Ident
  fieldNames : Array Name
  fieldIdents : Array Ident
  carriers : Array Term
  deriving Inhabited

/-- Emit one ordinary derive, trying the mergeability registry in its stable
order, and return its classification row.

Failure to match a route emits an obligation rather than a positive facet.
Author evidence is attempted only in the answer family explicitly supplied by
the surface row. -/
def emit (ctx : Context) (der : Syntax) : CommandElabM Row := do
  let `(preoDerive| derive $nm : $ty = $body $[:= $ev]?) := der
    | throwErrorAt der "preo: malformed derive"
  let used := Internal.mentions ctx.fieldNames body
  if used.size != 1 then
    throwErrorAt nm "preo: `derive {nm.getId}` reads {used.size} field(s) \
      ({String.intercalate ", " (used.toList.map toString)}) — this fragment \
      classifies a computation over EXACTLY ONE field, because the transport \
      that carries its answer to the declared state \
      (`Preo.mergeability_comp`) is along one projection. A multi-field \
      derive needs a joint-merge argument, which is the `derive custom = \
      opaque …` escape hatch of `PREOSCRIPTING.md` §7.1 and is not built."
  let some fi := ctx.fieldNames.findIdx? (· == used[0]!)
    | throwErrorAt nm "preo: internal"
  let fname := ctx.fieldNames[fi]!
  let carrier := ctx.carriers[fi]!
  let accId := mkIdent (ctx.declName ++ fname)
  let homId := mkIdent (ctx.declName ++ (fname ++ `merge_hom))
  let surjId := mkIdent (ctx.declName ++ (fname ++ `surj))
  let onId := mkIdent (ctx.declName ++ (nm.getId ++ `on))
  let dId := mkIdent (ctx.declName ++ nm.getId)
  let mergeId := mkIdent (ctx.declName ++ (nm.getId ++ `merge))
  withRef nm do
    Internal.emitRequired (← `(command|
      /-- The computation, at the field's own carrier. -/
      @[reducible] def $onId : $carrier → $ty :=
        fun $(ctx.fieldIdents[fi]!) => $body))
    Internal.emitRequired (← `(command|
      /-- The computation, at the declared document. -/
      def $dId : $(ctx.stateId) → $ty := fun s => $onId ($accId s)))
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
      match ← Internal.probeCommand (← `(command|
          def $mergeId : Uwueave.Preo.MergeFacet $dId where
            answer := $ansT
            correct :=
              Uwueave.Preo.mergeability_comp (π := $accId) (g := $onId)
                $homId $surjId
                (($proofT : Uwueave.JoinHom.Fourth.Correct $onId $ansT))
            cite := $(Syntax.mkStrLit cite))) with
      | .ok _ =>
          Internal.floorCheck nm "mergeability facet"
            (ctx.fullDecl ++ (nm.getId ++ `merge))
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
      let oId := mkIdent (ctx.declName ++ (nm.getId ++ `obligation))
      Internal.emitRequired (← `(command|
        def $oId : Uwueave.Preo.Obligation
            (S := $(ctx.stateId)) (fun _ => True) where
          invName := $(Syntax.mkStrLit nm.getId.toString)
          onField := $(Syntax.mkStrLit fname.toString)
          tried := ["∃-read", "filtered view", "high-water mark", "set image", "count"]
          discharge := $(Syntax.mkStrLit why)))
      oblId? := some oId
    let classId := mkIdent (ctx.declName ++ (nm.getId ++ `classification))
    let mList : Term ←
      if fired.isSome then `([$mergeId])
      else `(([] : List (Uwueave.Preo.MergeFacet $dId)))
    let oList : Term ← match oblId? with
      | none => `(([] : List (Uwueave.Preo.Obligation
          (S := $(ctx.stateId)) (fun _ => True))))
      | some oId => `([$oId])
    Internal.emitRequired (← `(command|
      /-- The derive's accumulated facets. Its `global`/`seams` are empty by
      construction: a computation has no confluence verdict, it has a
      mergeability one. -/
      def $classId : Uwueave.Preo.Classification
          (S := $(ctx.stateId)) (fun _ => True) $dId where
        global := []
        seams := []
        mergeability := $mList
        obligations := $oList))
    return {
      decl := ctx.fullDecl, kind := .derive, name := nm.getId.toString
      detail := fname.toString
      detail₂ := match fired with | some (l, _) => l | none => "—"
      evidence := ctx.fullDecl ++ (nm.getId ++ `classification)
      isObligation := fired.isNone
      cite := match fired with
        | some (_, c) => c
        | none => "UNRESOLVED — see the row's `.obligation`"
      seamCite := "" }

end Uwueave.Preo.Elab.Derive
