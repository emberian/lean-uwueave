/-
# Uwueave.Tactics.Verdict — evidence-carrying classification values.

This is the minimal layer needed by the preoscript surface: checked
`Spec.Verdict` values, total finite classification, and the `verdict` tactic.
The larger `Uwueave.Tactics` module imports this file and adds demonstrations;
production consumers should import this leaf directly.
-/
import Uwueave.Tactics.Core
import Uwueave.Spec
import Lean

namespace Uwueave.Tactics

open Uwueave Uwueave.Catalog Uwueave.Spec

universe u v

/-- Reading a free verdict recovers its I-confluence proof. -/
theorem iconfluent_of_isFree {S : Type u} [MergeState S] {I : Invariant S}
    {v : Verdict I} (h : v.isFree = true) : IConfluent I := by
  cases v with
  | free hI => exact hI
  | clash x y hx hy hbad => simp [Verdict.isFree] at h

/-- Reading a clash verdict recovers its refutation. -/
theorem not_iconfluent_of_isFree_false {S : Type u} [MergeState S] {I : Invariant S}
    {v : Verdict I} (h : v.isFree = false) : ¬ IConfluent I := by
  cases v with
  | free hI => simp [Verdict.isFree] at h
  | clash x y hx hy hbad => exact fun hc => hbad (hc x y hx hy)

/-- A checked clash as the verdict it already is. -/
def Clash.toVerdict {S : Type u} [MergeState S] {I : Invariant S} (c : Clash I) : Verdict I :=
  .clash c.x c.y c.hx c.hy c.hbad

@[simp] theorem Clash.toVerdict_isFree {S : Type u} [MergeState S] {I : Invariant S}
    (c : Clash I) : c.toVerdict.isFree = false := rfl

/-- Search an explicit heuristic pool. `none` means no verdict, never free. -/
def classifyIn? {S : Type u} [MergeState S] (I : Invariant S) [DecidablePred I]
    (pool : List S) : Option (Verdict I) :=
  (findClash I pool).map Clash.toVerdict

/-- Search the registered heuristic pool. `none` means no verdict. -/
def classify? {S : Type u} [MergeState S] [Probes S] (I : Invariant S) [DecidablePred I] :
    Option (Verdict I) :=
  classifyIn? I (Probes.probes (S := S))

/-- A pool search can only return a clash verdict. -/
theorem classifyIn?_never_free {S : Type u} [MergeState S] {I : Invariant S} [DecidablePred I]
    {pool : List S} {v : Verdict I} (h : classifyIn? I pool = some v) : v.isFree = false := by
  unfold classifyIn? at h
  cases hf : findClash I pool with
  | none => simp [hf] at h
  | some c =>
      simp only [hf, Option.map_some] at h
      have hv : c.toVerdict = v := Option.some.inj h
      subst hv
      rfl

/-- Any verdict returned by a pool search refutes I-confluence. -/
theorem classifyIn?_sound {S : Type u} [MergeState S] {I : Invariant S} [DecidablePred I]
    {pool : List S} {v : Verdict I} (h : classifyIn? I pool = some v) : ¬ IConfluent I :=
  not_iconfluent_of_isFree_false (classifyIn?_never_free h)

/-- Total finite classification. Unlike automatic tactic routing, this
explicit value-level function has no implicit work cap. -/
def classifyFinite {S : Type u} [MergeState S] [FinEnum S] (I : Invariant S) [DecidablePred I] :
    Verdict I :=
  match hf : findClash I (FinEnum.enum (S := S)) with
  | some c => c.toVerdict
  | none => .free fun x y hx hy =>
      findClash_none hf x (FinEnum.complete x) y (FinEnum.complete y) hx hy

/-- Finite classification is complete in both directions. -/
theorem classifyFinite_isFree_iff {S : Type u} [MergeState S] [FinEnum S]
    (I : Invariant S) [DecidablePred I] :
    (classifyFinite I).isFree = true ↔ IConfluent I := by
  constructor
  · exact iconfluent_of_isFree
  · intro hc
    cases hv : (classifyFinite I).isFree with
    | true => rfl
    | false => exact absurd hc (not_iconfluent_of_isFree_false hv)

/-- The refutation reading of total finite classification. -/
theorem classifyFinite_not_iconfluent {S : Type u} [MergeState S] [FinEnum S]
    (I : Invariant S) [DecidablePred I] (h : (classifyFinite I).isFree = false) :
    ¬ IConfluent I :=
  not_iconfluent_of_isFree_false h

namespace Classify

open Lean Meta Elab Tactic

/-- `Verdict I` ↦ `(S, MergeState instance, I)`. -/
def verdictArgs? (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Uwueave.Spec.Verdict 3 then
    let a := e.getAppArgs
    some (a[0]!, a[1]!, a[2]!)
  else
    none

end Classify

/-- Build a checked `Verdict I`: first use the shared positive routes, then
search for a checked clash. No default verdict is invented. -/
syntax "verdict" (" using " term)? : tactic

open Lean Meta Elab Tactic Classify in
elab_rules : tactic
  | `(tactic| verdict $[using $poolStx]?) => withMainContext do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (S, inst, I) := verdictArgs? ty
    | throwError "verdict: expected a goal of the form `Verdict I`, got{indentExpr ty}\n\
        For `IConfluent I` / `¬ IConfluent I` goals use `classify`."
  let explicit? ← match poolStx with
    | some stx => do
        let e ← Term.elabTerm stx (some (← mkAppM ``List #[S]))
        Term.synthesizeSyntheticMVars
        pure (some (← instantiateMVars e))
    | none => pure none
  let iconfTy ← mkAppOptM ``Uwueave.IConfluent #[S, inst, I]
  let m ← mkFreshExprSyntheticOpaqueMVar iconfTy
  match ← tryPositiveOnOutcome m.mvarId! S I with
  | .applied =>
      goal.assign (← mkAppOptM ``Uwueave.Spec.Verdict.free #[S, inst, I, m])
      replaceMainGoal []
      return
  | .inapplicable _ _ => pure ()
  | outcome => discard (outcome.toBoolFor "verdict")
  let (pool, source) ← getPool S explicit?
  match ← Classify.findClash S inst I pool with
  | .ok (x, y) =>
      let (px, py, pbad) ← clashParts S inst I x y
      goal.assign (← mkAppOptM ``Uwueave.Spec.Verdict.clash #[S, inst, I, x, y, px, py, pbad])
      replaceMainGoal []
  | .error (legal, total) =>
      throwError "verdict: NO VERDICT — and none is invented.\n\
        No free route applied to{indentExpr ty}\n\
        and no clash was found: {legal} of {total} states in {source} satisfy \
        the invariant, and no pair of them clashes. A probe pool is a \
        heuristic, so this is silence, not freedom. Register a `FinEnum` \
        instance for the carrier (then `classifyFinite` decides), widen the \
        pool with `verdict using <list>`, or build the verdict by hand."

end Uwueave.Tactics
