/-
# Uwueave.Preo.Elab.Readback -- reduce answers from emitted classifications
-/
import Uwueave.Preo.Classification

namespace Uwueave.Preo.Elab.Readback

open Lean Elab Command Meta

/-- Reduce a classification's accumulated confluence answer.

The outer `none` means reduction failed; inner `none` is a genuine unresolved
classification. -/
def readAnswer (constant : Name) : CommandElabM (Option (Option Bool)) :=
  liftTermElabM do
    try
      let expression ← mkAppM ``Uwueave.Preo.Classification.answer
        #[← mkConstWithFreshMVarLevels constant]
      let result ← withDefault <| whnf expression
      if result.isAppOfArity ``Option.none 1 then return some none
      if result.isAppOfArity ``Option.some 2 then
        let answer ← withDefault <| whnf result.appArg!
        if answer.isConstOf ``Bool.true then return some (some true)
        if answer.isConstOf ``Bool.false then return some (some false)
      return none
    catch _ => return none

/-- Reduce a classification's accumulated mergeability answer. -/
def readMergeAnswer (constant : Name) : CommandElabM (Option (Option String)) :=
  liftTermElabM do
    try
      let expression ← mkAppM ``Uwueave.Preo.Classification.mergeAnswer
        #[← mkConstWithFreshMVarLevels constant]
      let result ← withDefault <| whnf expression
      if result.isAppOfArity ``Option.none 1 then return some none
      if result.isAppOfArity ``Option.some 2 then
        let answer ← withDefault <| whnf result.appArg!
        if answer.isConstOf ``Uwueave.JoinHom.Fourth.fromResults then
          return some (some "fromResults")
        if answer.isConstOf ``Uwueave.JoinHom.Fourth.needsEvidence then
          return some (some "needsEvidence")
      return none
    catch _ => return none

end Uwueave.Preo.Elab.Readback
