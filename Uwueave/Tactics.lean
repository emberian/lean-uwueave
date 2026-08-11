/-
# Uwueave.Tactics — the verdict as a value, and the machinery demonstrated.

The tactics themselves live one module down, in `Uwueave.Tactics.Core`, which
imports `Catalog` and nothing else. That split is the point of this file's
shape and is worth stating plainly: `Tactics.lean` imports
`Catalog`/`ORSet`/`Undo`/`Segmented` so that every tactic can be *shown*
closing a goal copied verbatim out of one of them — and that import is exactly
what stopped those files from naming the tactics. A shrink measured across the
tree (~161 → 25 lines over 20 sites) reached 2 of its 20 targets; the rest were
an import cycle (wave 9f). With the machinery below `Catalog`, twelve of the
remaining eighteen are reachable, and the six that are not are
`Catalog.lean`'s own — a tactic cannot shorten the proof of the lemma it is
made of.

What is *added* here, above the tactics, is the layer that turns a
classification into a **term**:

  * `Clash.toVerdict` — a found refutation, as `Spec.Verdict.clash`;
  * `classifyIn?` / `classify?` — `Option (Verdict I)` from a probe pool.
    **Partial by construction**, and the honest half of that is a theorem:
    `classifyIn?_never_free` says the pool route cannot return a `free`
    verdict, so a `none` can never be confused with one. `none` is NO VERDICT;
    it is not evidence of freedom, and §2's budget row is a live case where
    reading it as freedom would be wrong — that invariant is refuted
    elsewhere.
  * `classifyFinite` — **total**. Over a `FinEnum` carrier with a decidable
    invariant it returns a `Verdict I` for every input, and
    `classifyFinite_isFree_iff` is the completeness theorem: it answers `free`
    exactly when the invariant *is* I-confluent. This is the only entry point
    that decides.
  * `verdict` — the tactic form: on a goal `Verdict I` it runs the same
    positive routes `classify` runs (through the shared
    `Classify.tryPositiveRoutes`, so the two cannot drift) and emits
    `Verdict.free`, else searches for a clash and emits `Verdict.clash`, else
    fails loudly.

Codex's proposed split named these `classifyProof` / `findClash` / `classify?`
/ `classifyFinite`. Three are here under those names; `classifyProof` is not,
because it already exists and is called `classify` — renaming a tactic the
tree's total gate audits would buy nothing. `findClash` is in `Tactics.Core`
§4, where it returns `Option (Clash I)`: a `Clash` is a refutation *by
construction*, which is why "the search reports free" is not a bug that can be
written here, and why the search itself needs no `Verdict` and so can sit below
`Spec`.

## Why the value layer is here and not in `Tactics.Core`

`Verdict` is defined in `Spec.lean`, which imports `Move`. Putting these four
in `Core` would drag `Move`, `Acyclicity`, `Exec` and `Segmented` under the
tactic layer and re-block files the split just freed — `Segmented`'s own shrink
entry among them. So `Core` holds everything that does not mention `Verdict`
(including the search), and this file holds everything that does. The clean
version of this would move `Verdict` itself into a leaf below `Spec`; that is a
one-file change nobody has needed yet, and it is the reason this boundary is
where it is rather than where it belongs.
-/
import Uwueave.Tactics.Core
import Uwueave.Spec
import Uwueave.Segmented
import Uwueave.ORSet
import Uwueave.Undo
import Lean

namespace Uwueave.Tactics

open Uwueave Uwueave.Catalog Uwueave.Spec

universe u v

/-! ## §1. The verdict as a value.

`Spec.Verdict` is the evidence-carrying object the DSL composes and a consumer
reads: `free h` carries an `IConfluent` proof, `clash x y …` carries the repro.
Everything below produces one, and the reason none of them can produce a *wrong*
one is structural rather than careful: a `Verdict I` cannot be built without the
evidence, so the only failure available to a search is to produce nothing. -/

/-- A verdict is decisive in the direction it claims — `free` is a proof. This
and its twin below are what let the completeness theorem be proved without ever
inspecting how a verdict was computed. -/
theorem iconfluent_of_isFree {S : Type u} [MergeState S] {I : Invariant S}
    {v : Verdict I} (h : v.isFree = true) : IConfluent I := by
  cases v with
  | free hI => exact hI
  | clash x y hx hy hbad => simp [Verdict.isFree] at h

/-- …and decisive in the other direction too: a `clash` verdict carries its own
refutation. There is no third answer, which is why `Verdict` can be read as a
decision whenever one was reached. -/
theorem not_iconfluent_of_isFree_false {S : Type u} [MergeState S] {I : Invariant S}
    {v : Verdict I} (h : v.isFree = false) : ¬ IConfluent I := by
  cases v with
  | free hI => simp [Verdict.isFree] at h
  | clash x y hx hy hbad => exact fun hc => hbad (hc x y hx hy)

/-- A found clash (`Tactics.Core` §4), as the verdict it is. -/
def Clash.toVerdict {S : Type u} [MergeState S] {I : Invariant S} (c : Clash I) : Verdict I :=
  .clash c.x c.y c.hx c.hy c.hbad

/-- ⚠ **The safety fact, by `rfl`.** Anything the search produces reports
`clash`. Not "in practice" — the search's return type is `Option (Clash I)` and
`Clash` has one constructor, which takes the refutation. -/
@[simp] theorem Clash.toVerdict_isFree {S : Type u} [MergeState S] {I : Invariant S}
    (c : Clash I) : c.toVerdict.isFree = false := rfl

/-- **Classify against an explicit pool.** `some v` carries a real repro;
`none` is **NO VERDICT** — the pool found nothing, which is a fact about the
pool (`findClash_none`) and not about `I`.

⚠ Being an ordinary function, this needs `DecidablePred I` from instance
synthesis. An invariant behind a `def` (`Segmented.BudgetInv`) hides its
decidability from the synthesizer; supply the instance at the use site — §2
does. The `classify` tactic gets past this by exposing the head itself, which
is a thing a tactic can do and a function cannot. -/
def classifyIn? {S : Type u} [MergeState S] (I : Invariant S) [DecidablePred I]
    (pool : List S) : Option (Verdict I) :=
  (findClash I pool).map Clash.toVerdict

/-- `classifyIn?` over the registered `Probes` pool — the default entry point.
Same contract: `none` is no verdict. -/
def classify? {S : Type u} [MergeState S] [Probes S] (I : Invariant S) [DecidablePred I] :
    Option (Verdict I) :=
  classifyIn? I (Probes.probes (S := S))

/-- ⚠ **THE SAFETY THEOREM.** The pool route can never answer `free`. So a
`none` from `classifyIn?` is unambiguous: it is the *absence* of a verdict, and
there is no execution in which it means "coordination-free". A caller that
treats `none` as freedom is making that error unaided by anything here. -/
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

/-- And what a `some` *does* mean: the invariant is refuted. -/
theorem classifyIn?_sound {S : Type u} [MergeState S] {I : Invariant S} [DecidablePred I]
    {pool : List S} {v : Verdict I} (h : classifyIn? I pool = some v) : ¬ IConfluent I :=
  not_iconfluent_of_isFree_false (classifyIn?_never_free h)

/-- **The total one.** Over a carrier that enumerates *with its completeness
proof* and a decidable invariant, classification is a function: every input
gets a verdict, and the verdict carries the evidence either way. The `free`
branch is not a search result promoted to a claim — it is `findClash_none`
composed with `FinEnum.complete`, i.e. the enumeration's own completeness doing
the work that a probe pool cannot do. -/
def classifyFinite {S : Type u} [MergeState S] [FinEnum S] (I : Invariant S) [DecidablePred I] :
    Verdict I :=
  match hf : findClash I (FinEnum.enum (S := S)) with
  | some c => c.toVerdict
  | none => .free fun x y hx hy =>
      findClash_none hf x (FinEnum.complete x) y (FinEnum.complete y) hx hy

/-- **The completeness theorem.** `classifyFinite` answers `free` exactly when
the invariant is I-confluent — no false frees (that direction is
`iconfluent_of_isFree`, and it holds of *any* verdict) and, the half that is
about this function, **no false clashes**: it does not give up and report a
repro on a confluent invariant, because it could not have built one. -/
theorem classifyFinite_isFree_iff {S : Type u} [MergeState S] [FinEnum S]
    (I : Invariant S) [DecidablePred I] :
    (classifyFinite I).isFree = true ↔ IConfluent I := by
  constructor
  · exact iconfluent_of_isFree
  · intro hc
    cases hv : (classifyFinite I).isFree with
    | true => rfl
    | false => exact absurd hc (not_iconfluent_of_isFree_false hv)

/-- The refutation reading of the same call: a `clash` answer is a real one. -/
theorem classifyFinite_not_iconfluent {S : Type u} [MergeState S] [FinEnum S]
    (I : Invariant S) [DecidablePred I] (h : (classifyFinite I).isFree = false) :
    ¬ IConfluent I :=
  not_iconfluent_of_isFree_false h

namespace Classify

open Lean Meta Elab Tactic

/-- `Verdict I` ↦ `(S, MergeState instance, I)`. `Verdict.cross` is an
`abbrev`, so a reducible whnf at the call site lands here too. -/
def verdictArgs? (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Uwueave.Spec.Verdict 3 then
    let a := e.getAppArgs
    some (a[0]!, a[1]!, a[2]!)
  else
    none

end Classify

/-- **The verdict tactic — `classify`, returning a term.** On a goal
`Verdict I` (or `Verdict.cross R`, which reduces to one) it runs the positive
routes on a scratch `IConfluent I` goal and emits `Verdict.free` with the proof
they built; failing that it searches a probe pool and emits `Verdict.clash`
with all three side conditions `decide`d. Both branches are kernel-checked
terms, so the tactic can fail but cannot lie.

`verdict using <list>` supplies the pool explicitly, exactly as `classify`
does. When neither a route nor a clash lands, it throws — there is no
default. -/
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
  -- Free: the same routes `classify` runs, on a scratch `IConfluent I` goal.
  let iconfTy ← mkAppOptM ``Uwueave.IConfluent #[S, inst, I]
  let m ← mkFreshExprSyntheticOpaqueMVar iconfTy
  if ← tryPositiveOn m.mvarId! S I then
    goal.assign (← mkAppOptM ``Uwueave.Spec.Verdict.free #[S, inst, I, m])
    replaceMainGoal []
    return
  -- Clash: the pool search, with every side condition re-derived by `decide`.
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

/-! ## §2. The value layer, demonstrated.

Each row is one of the two answers, produced as a term and then *read back* —
`isFree` is only the label; the evidence is in the term it was computed from. -/

section VerdictDemo

open Uwueave.ORSet

/-- The two allocations from `Segmented.budget_not_iconfluent` — the pool the
defaults cannot supply, because the defaults carry `0`s and `1`s and a budget
of `10` needs a `10`. Used by both the value layer and `classify` below. -/
private def budgetProbes : List Segmented.QuotaState :=
  [((fun b => if b then 10 else 0), (fun b => if b then 10 else 0)),
   ((fun b => if b then 0 else 10), (fun b => if b then 0 else 10))]

/-- `Segmented.BudgetInv` is a `def`, so instance synthesis cannot see its
decidability — the caveat on `classifyIn?`, and its one-line remedy. -/
local instance decidableBudgetInv (B : Nat) : DecidablePred (Segmented.BudgetInv B) := fun s => by
  unfold Segmented.BudgetInv
  infer_instance

/-- **Total, and free.** `GSet Bool` has four states and `FinEnum` carries the
proof that that is all of them, so this answer is a decision. -/
example : (classifyFinite (S := GSet Bool) (fun s => s true = true ∨ s false = true)).isFree
    = true := rfl

/-- **Total, and refuted** — the same call, the other answer, carrying the
two-replica repro. `Spec.mutexClash`'s shape over a finite carrier. -/
example : (classifyFinite (S := GSet Bool)
    (fun s => (s true = true ∧ s false = false) ∨ (s false = true ∧ s true = false))).isFree
    = false := rfl

/-- The pool route on an infinite carrier: `Catalog.or_breaks_iconfluence`'s
invariant, refuted from the default `GSet Nat` probes — as a value this time,
not a closed goal. -/
example : (classify? (S := GSet Nat)
    (fun s => (s 0 = true ∧ s 1 = false) ∨ (s 1 = true ∧ s 0 = false))).isSome = true := rfl

/-- ⚠ **And `none` is not freedom.** The default `QuotaState` probes carry `0`s
and `1`s; `Segmented.BudgetInv 10` needs a `10`, so nothing in the pool even
satisfies the invariant and `classify?` returns `none`. That invariant is in
fact NOT I-confluent (`Segmented.budget_not_iconfluent`) — so this row is
exactly the case where reading `none` as `free` would be a wrong verdict about
a real clash. `classifyIn?_never_free` is why the misreading cannot come from
here. -/
example : (classify? (Segmented.BudgetInv 10)).isNone = true := rfl

/-- Handed a pool with a `10` in it, the same call finds the clash. -/
example : (classifyIn? (Segmented.BudgetInv 10) budgetProbes).isSome = true := rfl

/-- `Spec.lwwSingleFree`, as a tactic call: the selection route, over an
infinite carrier and an arbitrary invariant. -/
example (I : Invariant LWW) : Verdict I := by verdict

/-- `ORSet.clset_present_iconfluent` as a verdict — the one-key selection
route, reached through `Verdict.free`. -/
example {α : Type} (a : α) : Verdict (S := CLSet α) (fun s => CLPresent s a) := by verdict

/-- `Spec.mutexClash`, searched rather than written: the same clash, found in
the default pool. -/
example : Verdict (S := GSet Nat)
    (fun s => (s 0 = true ∧ s 1 = false) ∨ (s 1 = true ∧ s 0 = false)) := by verdict

/-- `Spec.lwwPairLeClash` — the cross-field archetype. `Verdict.cross` is an
`abbrev` over `Verdict`, so the tactic reaches through it and the relational
hole is filled by a searched repro. -/
example : Verdict.cross (fun a b : LWW => a.val ≤ b.val) := by verdict

/-- And the escape hatch, as for `classify`: hand it the pool that has a `10`
in it. -/
example : Verdict (Segmented.BudgetInv 10) := by verdict using budgetProbes

/-- The tactic's answer, read back: a searched clash reports `clash`, and the
`isFree` that says so reduces through the very term the tactic built. -/
example : ((by verdict : Verdict (S := LWW × LWW) (fun p => p.1.val ≤ p.2.val))).isFree
    = false := rfl

end VerdictDemo

/-! ## §3. `classify`, demonstrated.

Each example below is the statement of an existing theorem of this library,
copied verbatim, with the hand proof replaced by one word. -/

section ClassifyDemo

open Uwueave.ORSet

/-- `Catalog.lww_every_invariant_iconfluent` — selection route, infinite
carrier, arbitrary invariant. Original: one term citing two lemmas. -/
example (I : Invariant LWW) : IConfluent I := by classify

/-- `ORSet.clset_present_iconfluent` — one-key selection route over the
pointwise-max lattice. Original: 5 lines (`show`/`rw`/`split`/two cases).
Now applied at the source: `ORSet.lean` imports `Tactics.Core`. -/
example {α : Type} (a : α) : IConfluent (S := CLSet α) (fun s => CLPresent s a) := by
  classify

/-- `ORSet.clset_absent_iconfluent` — same route, same one word. -/
example {α : Type} (a : α) : IConfluent (S := CLSet α) (fun s => s a % 2 = 0) := by
  classify

/-- `Catalog.gcounter_lowerBound_iconfluent` — third instance of the same
route; the tree proves this one by hand with `Nat.le_trans`/`Nat.le_max_left`. -/
example {ι : Type} (i : ι) (k : Nat) : IConfluent (S := GCounter ι) (fun f => k ≤ f i) := by
  classify

/-- `Catalog.gset_mem_iconfluent` — monotone-closure route, over an arbitrary
(infinite) element type. -/
example {α : Type} (a : α) : IConfluent (S := GSet α) (fun s => s a = true) := by classify

/-- Exhaustive-decision route: a finite carrier, an invariant no lemma covers.
`GSet Bool` has four states; `FinEnum` enumerates them *with the proof that
that is all of them*, and `decide` settles the 16 pairs. -/
example : IConfluent (S := GSet Bool) (fun s => s true = true ∨ s false = true) := by
  classify

/-- The exhaustive route decides the **negative** too — same instance, no probe
pool involved. Over `GSet Bool`, "exactly one element" is refuted by decision,
not by search. -/
example : ¬ IConfluent (S := GSet Bool) (fun s => (s true = true) ≠ (s false = true)) := by
  classify

/-- `Catalog.or_breaks_iconfluence` — clash search over the default `GSet Nat`
probes (small-support subsets of `{0,1,2}`). Original: 6 lines. -/
example : ¬ IConfluent (S := GSet Nat)
    (fun s => (s 0 = true ∧ s 1 = false) ∨ (s 1 = true ∧ s 0 = false)) := by classify

/-- `Weave.active_path_not_iconfluent` — the loom's shared active path, found
by the same pool. Original: 6 lines with the witnesses written by hand. -/
example : ¬ IConfluent (S := GSet Nat)
    (fun s => s 0 = true ∧ ((s 1 = true ∧ s 2 = false) ∨ (s 2 = true ∧ s 1 = false))) := by
  classify

/-- `Catalog.pncounter_nonneg_not_iconfluent` — Bailis's motivating example,
found in the 16-state `(Bool → Nat) × (Bool → Nat)` pool. Original: 7 lines. -/
example : ¬ IConfluent (S := PNCounter Bool) (fun c => 0 ≤ net c) := by classify

/-- `Catalog.lww_cross_field_not_iconfluent` — the cross-field register clash.
The search finds a *different* witness than the hand proof's `(2,5)/(1,0),(3,0)`
(the probes only carry `0`s and `1`s), which is the point: any clash refutes. -/
example : ¬ IConfluent (S := LWW × LWW) (fun p => p.1.val ≤ p.2.val) := by classify

/-- The escape hatch, and the honest failure it repairs. `Segmented.BudgetInv 10`
needs states holding a `10`; the default pools carry `0`s and `1`s, so `classify`
alone reports *no verdict* (see the file header — it does not guess). Handing it
the two allocations from `Segmented.budget_not_iconfluent` settles it. -/
example : ¬ IConfluent (Segmented.BudgetInv 10) := by classify using budgetProbes

/-- `ORSet.clset_cross_element_not_iconfluent` — same escape hatch, second
instance. The clash needs a `3` against a `2` (odd beats even at `max`), and
the default `Probes Nat` carries only `0` and `1`; handed the two states, the
search settles it. Original: 16 lines, the longest refutation in that file. -/
example : ¬ IConfluent (S := CLSet Nat) (fun s => s 0 % 2 = 1 → s 1 % 2 = 1) := by
  classify using [(fun n => if n = 0 then 3 else 1), (fun _ => 2)]

end ClassifyDemo

/-! ## §4. The idiom tactics, demonstrated on the tree's real goals.

Every statement below is copied verbatim from another module. Nothing there is
edited — these are the same goals, re-proved by the named tactic, so the
saving is measured rather than asserted. The tactics themselves are
`Tactics.Core` §7. -/

section IdiomDemo

open Uwueave.MVRegister Uwueave.Undo

/-- `Catalog.gset_mem_iconfluent`, opener replaced (was: `intro x y hx hy;
show (x a || y a) = true; simp [hx]`). -/
example {α : Type} (a : α) : IConfluent (S := GSet α) (fun s => s a = true) := by
  iconf_intro x y hx hy
  simp [hx]

/-- `Catalog.escrow_local_bound_iconfluent`, opener replaced. -/
example {ι : Type} (q : ι → Nat) :
    IConfluent (S := Escrow ι) (fun f => ∀ i, f i ≤ q i) := by
  iconf_intro x y hx hy
  intro i
  exact Nat.max_le.mpr ⟨hx i, hy i⟩

/-- `Catalog.lww_cross_field_not_iconfluent` with its own witnesses — the
5-line `intro`/`exact absurd`/`by decide` block becomes the witnesses alone. -/
example : ¬ IConfluent (S := LWW × LWW) (fun p => p.1.val ≤ p.2.val) := by
  clash (⟨2, 5⟩, ⟨2, 5⟩), (⟨1, 0⟩, ⟨3, 0⟩)

/-- `Catalog.pncounter_nonneg_not_iconfluent`, witnesses preserved. -/
example : ¬ IConfluent (S := PNCounter Bool) (fun c => 0 ≤ net c) := by
  clash (fun b => if b then 10 else 0, fun b => if b then 10 else 0),
        (fun b => if b then 10 else 0, fun b => if b then 0 else 10)

/-- `Undo.mem_s01` (8 lines → 1). -/
example {w : Write} (h : s01 w = true) : w = w0 ∨ w = w1 := by
  mem_union h [s01]

/-- `Undo.mem_s01u` (9 lines → 1). -/
example {w : Write} (h : s01u w = true) : w = w0 ∨ w = w1 ∨ w = u1 := by
  mem_union h [s01u, s01]

/-- `Undo.mem_s01ur` (10 lines → 1). -/
example {w : Write} (h : s01ur w = true) : w = w0 ∨ w = w1 ∨ w = u1 ∨ w = r1 := by
  mem_union h [s01ur, s01u, s01]

/-- `Undo.mem_s01uC` (10 lines → 1). -/
example {w : Write} (h : s01uC w = true) : w = w0 ∨ w = w1 ∨ w = u1 ∨ w = wC := by
  mem_union h [s01uC, s01u, s01]

/-- `MVRegister.mem_sAB` (6 lines → 1). -/
example {w : Write} (h : sAB w = true) : w = wA ∨ w = wB := by
  mem_union h [sAB]

/-- `Undo.overwrite_supersedes` (11 lines → 1). -/
example (w : Write) : InView s01 w ↔ w = w1 := by
  view_unique mem_s01, w1

/-- `Undo.undo_restores` (12 lines → 1). -/
example (w : Write) : InView s01u w ↔ w = u1 := by
  view_unique mem_s01u, u1

/-- `Undo.redo_restores` (13 lines → 1). -/
example (w : Write) : InView s01ur w ↔ w = r1 := by
  view_unique mem_s01ur, r1

end IdiomDemo

end Uwueave.Tactics
