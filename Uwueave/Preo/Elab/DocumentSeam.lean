/-
# Uwueave.Preo.Elab.DocumentSeam — declaration seam composition worker

Exactly two field seams on distinct components are lifted through their
right-nested projections, composed, and optionally enriched by document-scale
free rows whose witness-side legality is kernel-decidable.  The declaration
order, generated names, and optional absorption order are compatibility ABI.
-/
import Uwueave.Preo.Elab.Invariant

namespace Uwueave.Preo.Elab.DocumentSeam

open Lean Elab Command Term
open Uwueave Uwueave.Spec

/-- Compose the declaration seam when exactly two distinct field seams exist.
Returns the final emitted declaration when the rule applies. -/
def emit (ctx : State.Context) (seams : Array Invariant.FiredSeam)
    (frees : Array Ident) (ref : Syntax) : CommandElabM (Option Ident) := do
  if seams.size != 2 then return none
  let a := seams[0]!
  let b := seams[1]!
  let (left, right) := if a.field < b.field then (a, b) else (b, a)
  if left.field == right.field then return none
  let leftSeam := left.const
  let rightSeam := right.const
  let leftAcc := mkIdent (ctx.declName ++ ctx.fieldNames[left.field]!)
  let rightAcc := mkIdent (ctx.declName ++ ctx.fieldNames[right.field]!)
  let leftHom := mkIdent (ctx.declName ++ (ctx.fieldNames[left.field]! ++ `merge_hom))
  let rightHom := mkIdent (ctx.declName ++ (ctx.fieldNames[right.field]! ++ `merge_hom))
  let rightX : Term ← `(Uwueave.Spec.SegVerdict.x $rightSeam)
  let leftX : Term ← `(Uwueave.Spec.SegVerdict.x $leftSeam)
  let leftPlant ← Internal.plantFn left.field ctx.size (ctx.defaults.set! right.field rightX)
  let rightPlant ← Internal.plantFn right.field ctx.size (ctx.defaults.set! left.field leftX)
  let leftLiftId := mkIdent (ctx.declName ++ `documentSeamLeft)
  let rightLiftId := mkIdent (ctx.declName ++ `documentSeamRight)
  let baseId := mkIdent (ctx.declName ++ `documentSeamBase)
  let documentSeamId := mkIdent (ctx.declName ++ `documentSeam)
  Internal.emitRequired (← `(command|
    /-- The left field's seam at document scale. Its section plants the
    right seam verdict's legal left witness, so the two lifted invariants
    can be conjoined without an unproved default-legality assumption. -/
    def $leftLiftId :=
      Uwueave.Preo.seamAlong $leftAcc $leftHom $leftPlant
        (fun _ => rfl) (fun _ _ => rfl) $leftSeam))
  Internal.emitRequired (← `(command|
    /-- The right field's seam at document scale, with the left seam
    verdict's legal left witness planted symmetrically. -/
    def $rightLiftId :=
      Uwueave.Preo.seamAlong $rightAcc $rightHom $rightPlant
        (fun _ => rfl) (fun _ _ => rfl) $rightSeam))
  Internal.emitRequired (← `(command|
    /-- The two seamed field invariants conjoined at document scale. Its
    seam is the pair of their field seams; replicas sharing a fiber of that
    pair merge without coordination. The carried global clash is the left
    invariant's concrete witness with the right verdict's legal left
    witness held fixed. -/
    def $baseId :=
      Uwueave.Spec.SegVerdict.andSeams $leftLiftId $rightLiftId
        (Uwueave.Spec.SegVerdict.hx $rightSeam)
        (Uwueave.Spec.SegVerdict.hx $rightSeam)))
  let mut currentSeam := baseId
  let mut absorbed : Nat := 0
  for freeProof in frees do
    let suffix := Name.mkSimple s!"documentSeamFree{absorbed + 1}"
    let nextId := mkIdent (ctx.declName ++ suffix)
    match ← Internal.probeCommand (← `(command|
        /-- One coordination-free row absorbed into the declaration seam.
        This constant exists only because the row holds at both carried clash
        documents; `by decide` is a kernel-checked side condition. -/
        def $nextId :=
          Uwueave.Spec.SegVerdict.absorbFree $currentSeam $freeProof
            (by decide) (by decide))) with
    | .ok _ =>
        Internal.floorCheck ref "absorbed document seam verdict" (ctx.ns ++ nextId.getId)
        currentSeam := nextId
        absorbed := absorbed + 1
    | .error _ => pure ()
  Internal.emitRequired (← `(command|
    /-- The declaration's composed document seam: its two seam rows, plus
    every coordination-free row whose legality at the carried clash pair
    the registry also proved. A free row without that inhabitance proof is
    omitted from this conjunction, never silently assumed. -/
    def $documentSeamId := $currentSeam))
  Internal.floorCheck ref "document seam verdict" (ctx.fullDecl ++ `documentSeam)
  return some documentSeamId

end Uwueave.Preo.Elab.DocumentSeam
