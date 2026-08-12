/-
# Uwueave.Preo.Incremental — conservative differential evaluation.

This module adds an executable cache/update layer to `Preo.Expr`.  An
`EnvDelta` describes a new typed environment and identifies changed fields by
typed `Var`, so an update can never confuse two fields merely because their
Lean values happen to have the same type.

The work counter records semantic evaluations of the root expression.  A
cache hit performs zero such evaluations; a miss performs exactly one full
`Term.eval`.  It intentionally does not pretend to count allocations,
dependency tests, or Lean reduction steps.

Structural terms get a conservative built-in dependency analysis.  A custom
node is always considered touched and therefore takes the full-recomputation
path.  Its author may opt into a cheaper path only by providing an
`IncrementalLaw` whose result carries a proof against `Term.eval`.
-/
import Uwueave.Preo.Expr
import Uwueave.Preo.ResultProgram

namespace Uwueave.Preo.Incremental

open Expr

/-! ## Typed environment deltas -/

/-- A transition away from `base`, with a typed change predicate.

`unchanged` makes the predicate conservative: every field reported unchanged
really has the same value.  It may report extra changes, which can only cause
safe extra recomputation. -/
structure EnvDelta {Γ : Schema} (base : Env Γ) where
  after : Env Γ
  changed : {t : Ty} → Var Γ t → Bool
  unchanged : ∀ {t : Ty} (field : Var Γ t), changed field = false →
    base.get field = after.get field

/-- Structural dependency test.  Custom nodes return `true` regardless of
their declared reads: locality is not an incremental cost law. -/
def touched {Γ : Schema} {t : Ty} {base : Env Γ}
    (delta : EnvDelta (Γ := Γ) base) :
    Term Γ t → Bool
  | .litBool _ | .litNat _ | .none => false
  | .var field => delta.changed (t := _) field
  | .pair left right | .boolOr left right | .boolAnd left right
  | .natMax left right | .natAdd left right | .natEq left right =>
      touched delta left || touched delta right
  | .fst pair | .snd pair | .some pair | .isSome pair | .boolNot pair
  | .natSucc pair => touched delta pair
  | .custom _ => true

/-- If the structural dependency test misses, full evaluation cannot change.
The custom case is impossible because `Term.touched` is definitionally true
there. -/
theorem eval_eq_of_not_touched {Γ : Schema} {t : Ty}
    {base : Env Γ}
    (term : Term Γ t) (delta : EnvDelta (Γ := Γ) base)
    (h : touched delta term = false) :
    term.eval base = term.eval delta.after := by
  induction term with
  | litBool | litNat | none => rfl
  | var field =>
      exact delta.unchanged field h
  | pair left right ihLeft ihRight =>
      have hl : touched delta left = false := by
        cases hl : touched delta left <;> simp_all [touched]
      have hr : touched delta right = false := by
        cases hr : touched delta right <;> simp_all [touched]
      simp only [Term.eval, ihLeft hl, ihRight hr]
  | fst pair ih | snd pair ih | some pair ih | isSome pair ih
  | boolNot pair ih | natSucc pair ih =>
      simp only [touched] at h
      simp only [Term.eval, ih h]
  | boolOr left right ihLeft ihRight
  | boolAnd left right ihLeft ihRight
  | natMax left right ihLeft ihRight
  | natAdd left right ihLeft ihRight
  | natEq left right ihLeft ihRight =>
      have hl : touched delta left = false := by
        cases hl : touched delta left <;> simp_all [touched]
      have hr : touched delta right = false := by
        cases hr : touched delta right <;> simp_all [touched]
      simp only [Term.eval, ihLeft hl, ihRight hr]
  | custom node =>
      simp [touched] at h

/-! ## Caches, results, and the conservative evaluator -/

/-- A typed expression value tied by proof to the environment that produced
it. -/
structure Cache {Γ : Schema} {t : Ty} (term : Term Γ t) where
  env : Env Γ
  value : t.denote
  correct : value = term.eval env

/-- Evaluate once and retain the proof that the cache is valid. -/
def buildCache {Γ : Schema} {t : Ty} (term : Term Γ t) (env : Env Γ) :
    Cache term where
  env := env
  value := term.eval env
  correct := rfl

/-- The output of one differential step.  `recomputations` counts root
semantic evaluations, and `correct` prevents a cost-saving implementation from
returning a stale value. -/
structure Result {Γ : Schema} {t : Ty} (term : Term Γ t) (after : Env Γ) where
  value : t.denote
  recomputations : Nat
  correct : value = term.eval after

/-- Promote a checked update result to the cache for the next delta. This is
the runtime chaining seam: no reevaluation occurs, and the result's correctness
proof becomes the next cache's correctness proof verbatim. -/
def Result.toCache {Γ : Schema} {t : Ty} {term : Term Γ t} {after : Env Γ}
    (result : Result term after) : Cache term where
  env := after
  value := result.value
  correct := result.correct

@[simp] theorem Result.toCache_env {Γ : Schema} {t : Ty}
    {term : Term Γ t} {after : Env Γ} (result : Result term after) :
    result.toCache.env = after := rfl

@[simp] theorem Result.toCache_value {Γ : Schema} {t : Ty}
    {term : Term Γ t} {after : Env Γ} (result : Result term after) :
    result.toCache.value = result.value := rfl

/-- The honest miss path: one complete semantic recomputation. -/
def fullRecompute {Γ : Schema} {t : Ty} (term : Term Γ t) (after : Env Γ) :
    Result term after where
  value := term.eval after
  recomputations := 1
  correct := rfl

/-- Differential evaluation for the built-in typed language.

No touched structural subterm is claimed cheap: this first cache layer either
reuses the proved root value or performs one complete root evaluation.  Custom
nodes always reach the latter branch. -/
def incremental {Γ : Schema} {t : Ty} (term : Term Γ t)
    (cache : Cache term) (delta : EnvDelta (Γ := Γ) cache.env) :
    Result term delta.after :=
  if h : touched delta term = true then
    fullRecompute term delta.after
  else
    { value := cache.value
      recomputations := 0
      correct := by
        rw [cache.correct]
        exact eval_eq_of_not_touched term delta (by
          cases ht : touched delta term <;> simp_all) }

/-- The main semantic contract: differential evaluation agrees with a fresh
`Term.eval` in the new environment. -/
theorem incremental_correct {Γ : Schema} {t : Ty} (term : Term Γ t)
    (cache : Cache term) (delta : EnvDelta (Γ := Γ) cache.env) :
    (incremental term cache delta).value = term.eval delta.after :=
  (incremental term cache delta).correct

/-- An off-dependency delta retains the exact cached value and performs no
semantic recomputation. -/
theorem off_dependency_zero {Γ : Schema} {t : Ty} (term : Term Γ t)
    (cache : Cache term) (delta : EnvDelta (Γ := Γ) cache.env)
    (h : touched delta term = false) :
    (incremental term cache delta).recomputations = 0 ∧
      (incremental term cache delta).value = cache.value := by
  simp [incremental, h]

/-- A touched dependency takes the honest miss path: exactly one complete
recomputation whose result is fresh evaluation. -/
theorem touched_dependency_recomputes {Γ : Schema} {t : Ty}
    (term : Term Γ t) (cache : Cache term)
    (delta : EnvDelta (Γ := Γ) cache.env)
    (h : touched delta term = true) :
    (incremental term cache delta).recomputations = 1 ∧
      (incremental term cache delta).value = term.eval delta.after := by
  simp [incremental, h, fullRecompute]

/-- Custom code has no automatic cache-hit path.  This is independent of its
declared dependency list and holds for every environment delta. -/
theorem custom_without_law_recomputes {Γ : Schema} {t : Ty}
    (node : CustomNode Γ t) (cache : Cache (.custom node))
    (delta : EnvDelta (Γ := Γ) cache.env) :
    (incremental (.custom node) cache delta).recomputations = 1 ∧
      (incremental (.custom node) cache delta).value = node.run delta.after := by
  simpa [Term.eval] using
    touched_dependency_recomputes (.custom node) cache delta (by rfl)

/-! ## Explicit laws for custom and future structural nodes -/

/-- An extension node's explicit differential semantics.

The law does not receive any blanket claim that declared reads imply cheap
evaluation.  It must construct a `Result`, including both its work count and a
proof that its value agrees with full evaluation. -/
structure IncrementalLaw {Γ : Schema} {t : Ty} (term : Term Γ t) where
  apply : (cache : Cache term) → (delta : EnvDelta (Γ := Γ) cache.env) →
    Result term delta.after

/-- Apply an explicitly supplied law.  Keeping this entry point separate from
`incremental` makes the trust boundary visible at every call site. -/
def withLaw {Γ : Schema} {t : Ty} {term : Term Γ t}
    (law : IncrementalLaw term) (cache : Cache term)
    (delta : EnvDelta (Γ := Γ) cache.env) : Result term delta.after :=
  law.apply cache delta

theorem withLaw_correct {Γ : Schema} {t : Ty} {term : Term Γ t}
    (law : IncrementalLaw term) (cache : Cache term)
    (delta : EnvDelta (Γ := Γ) cache.env) :
    (withLaw law cache delta).value = term.eval delta.after :=
  (withLaw law cache delta).correct

/-! ## Checked-program adapter

`Expr.Program` is the value emitted by Preoscript's `typed derive`.  These
methods are deliberately generic: the generated surface aliases have no
second evaluator or cache semantics to drift from this one. -/

/-- A cache indexed by the program's inferred term. -/
abbrev ProgramCache (program : Expr.Program Γ) := Cache program.term

/-- Build the initial checked cache. -/
def buildProgramCache (program : Expr.Program Γ) (env : Env Γ) :
    ProgramCache program :=
  buildCache program.term env

/-- Apply a typed environment delta through the conservative evaluator. -/
def updateProgram (program : Expr.Program Γ) (cache : ProgramCache program)
    (delta : EnvDelta (Γ := Γ) cache.env) :
    Result program.term delta.after :=
  incremental program.term cache delta

/-- Run one update and retain its proved value as the cache for the next
typed delta. -/
def updateProgramCache (program : Expr.Program Γ) (cache : ProgramCache program)
    (delta : EnvDelta (Γ := Γ) cache.env) : ProgramCache program :=
  (updateProgram program cache delta).toCache

@[simp] theorem updateProgramCache_env (program : Expr.Program Γ)
    (cache : ProgramCache program)
    (delta : EnvDelta (Γ := Γ) cache.env) :
    (updateProgramCache program cache delta).env = delta.after := rfl

theorem updateProgramCache_correct (program : Expr.Program Γ)
    (cache : ProgramCache program)
    (delta : EnvDelta (Γ := Γ) cache.env) :
    (updateProgramCache program cache delta).value = program.eval delta.after :=
  (updateProgramCache program cache delta).correct

theorem updateProgram_correct (program : Expr.Program Γ)
    (cache : ProgramCache program)
    (delta : EnvDelta (Γ := Γ) cache.env) :
    (updateProgram program cache delta).value = program.eval delta.after :=
  incremental_correct program.term cache delta

theorem updateProgram_off_dependency_zero (program : Expr.Program Γ)
    (cache : ProgramCache program) (delta : EnvDelta (Γ := Γ) cache.env)
    (h : touched delta program.term = false) :
    (updateProgram program cache delta).recomputations = 0 ∧
      (updateProgram program cache delta).value = cache.value :=
  off_dependency_zero program.term cache delta h

/-! ## Exact six-status result adapter

An intrinsically typed pure program has a small but useful honest result
semantics: under the equality future, its singleton answer is settled and its
status is exactly that value. Preoscript instantiates this adapter with the
finite reach written in each `typed derive` row. It does not claim stability
under arbitrary environment changes; callers wanting a larger future must
prove the corresponding six-way contract themselves. -/

namespace TypedResult

/-- The exact future for a pure snapshot query. -/
def Future (_program : Expr.Program Γ) : Evidence.Future (Env Γ) := Eq

/-- The singleton result computed at an environment. -/
def answer (program : Expr.Program Γ) (env : Env Γ) :
    Catalog.GSet program.type.denote :=
  fun value => decide (value = program.eval env)

def settled (_program : Expr.Program Γ) (_env : Env Γ) : Prop := True

def evaluate (program : Expr.Program Γ) (env : Env Γ) :
    ResultStatus.Status program.type.denote :=
  .exact (program.eval env)

def surface (program : Expr.Program Γ) (surfaceId : String) :
    ResultProgram.SurfacePolicy (Env Γ) program.type.denote where
  name := surfaceId
  visibility := fun _ _ => .inspectable
  disclosure := fun _ _ => .shown

theorem totalSound (program : Expr.Program Γ) :
    StatusEffects.TotalSoundEvaluator6 (Future program) (answer program)
      (settled program) (evaluate program) := by
  refine {
    core := ?_
    exact_settled := ?_
    provisional_correct := ?_
    forkedClosed_correct := ?_
    forkedOpen_correct := ?_
    absent_settled := ?_
    pending_correct := ?_
    pending_open := ?_ }
  · refine {
      exact_correct := ?_
      exact_final := ?_
      absent_correct := ?_
      absent_final := ?_
      pending_escapable := ?_ }
    · intro env value h
      simp only [evaluate] at h
      injection h with hv
      subst value
      constructor
      · simp [answer]
      · intro other ho
        simpa [answer] using ho
    · intro before after value same h
      subst after
      exact h
    · intro env h
      simp [evaluate] at h
    · intro before after same h
      simp [evaluate] at h
    · intro env h
      simp [evaluate] at h
  · intro _ _ _
    trivial
  · intro env value h
    simp [evaluate] at h
  · intro env h
    simp [evaluate] at h
  · intro env h
    simp [evaluate] at h
  · intro _ _
    trivial
  · intro env h
    simp [evaluate] at h
  · intro env h
    simp [evaluate] at h

/-- A fully checked result declaration for one typed program and one explicit
finite reach. Future, resolution and default presentation policy are visible
in the value and its type. -/
def declaration (program : Expr.Program Γ) (name futureId surfaceId : String)
    (reach : List (Env Γ)) :
    ResultProgram.CheckedDeclaration (Env Γ) program.type.denote
      (Future program) (.preserveFork) where
  name := name
  futureId := futureId
  reach := reach
  answer := answer program
  settled := settled program
  evaluate := evaluate program
  surface := surface program surfaceId
  totalSound := totalSound program

end TypedResult

/-! ## Executable fixtures -/

abbrev DemoSchema : Schema := [.nat, .nat]

def before : Env DemoSchema :=
  .cons (t := .nat) (2 : Nat) (.cons (t := .nat) (10 : Nat) .nil)
def secondChangedAfter : Env DemoSchema :=
  .cons (t := .nat) (2 : Nat) (.cons (t := .nat) (99 : Nat) .nil)
def firstChangedAfter : Env DemoSchema :=
  .cons (t := .nat) (7 : Nat) (.cons (t := .nat) (10 : Nat) .nil)

def changedSecondField {t : Ty} : Var DemoSchema t → Bool
  | .here => false
  | .there .here => true

def changedFirstField {t : Ty} : Var DemoSchema t → Bool
  | .here => true
  | .there .here => false

/-- Change only the second typed field. -/
def secondChanged : EnvDelta before where
  after := secondChangedAfter
  changed := changedSecondField
  unchanged := by
    intro t field h
    cases field with
    | here => rfl
    | there field =>
        cases field with
        | here => simp [changedSecondField] at h
        | there field => nomatch field

/-- Change only the first typed field. -/
def firstChanged : EnvDelta before where
  after := firstChangedAfter
  changed := changedFirstField
  unchanged := by
    intro t field h
    cases field with
    | here => simp [changedFirstField] at h
    | there field =>
        cases field with
        | here => rfl
        | there field => nomatch field

def firstPlusOne : Term DemoSchema .nat := .natSucc (.var .here)
def firstPlusOneCache : Cache firstPlusOne where
  env := before
  value := firstPlusOne.eval before
  correct := rfl

theorem fixture_off_dependency_zero :
    (incremental firstPlusOne firstPlusOneCache secondChanged).recomputations = 0 :=
  (off_dependency_zero firstPlusOne firstPlusOneCache secondChanged rfl).1

theorem fixture_off_dependency_retained :
    (incremental firstPlusOne firstPlusOneCache secondChanged).value = (3 : Nat) :=
  calc
    _ = firstPlusOneCache.value :=
      (off_dependency_zero firstPlusOne firstPlusOneCache secondChanged rfl).2
    _ = (3 : Nat) := rfl

theorem fixture_touched_dependency_recomputed :
    (incremental firstPlusOne firstPlusOneCache firstChanged).recomputations = 1 :=
  (touched_dependency_recomputes firstPlusOne firstPlusOneCache firstChanged rfl).1

theorem fixture_touched_dependency_fresh :
    (incremental firstPlusOne firstPlusOneCache firstChanged).value =
      firstPlusOne.eval firstChangedAfter :=
  incremental_correct firstPlusOne firstPlusOneCache firstChanged

/-- An opaque spelling of the first-field query.  Its locality proof is not
automatically interpreted as a cost theorem. -/
def opaqueFirst : CustomNode DemoSchema .nat where
  name := "opaque-first"
  run := fun env => env.get .here
  dependencies := [0]
  dependenciesInRange := by simp [DemoSchema]
  respects := by
    intro x y h
    apply Env.get_eq_of_agreeAt .here x y
    exact h 0 (by simp)

def opaqueFirstTerm : Term DemoSchema .nat := .custom opaqueFirst
def opaqueFirstCache : Cache opaqueFirstTerm where
  env := before
  value := opaqueFirstTerm.eval before
  correct := rfl

/-- Without a separate law, even a delta away from the custom node's declared
read takes the full-recomputation path. -/
theorem fixture_custom_falls_back :
    (incremental opaqueFirstTerm opaqueFirstCache secondChanged).recomputations = 1 :=
  (touched_dependency_recomputes opaqueFirstTerm opaqueFirstCache secondChanged rfl).1

/-- The author can explicitly certify this particular custom implementation:
it reads only `.here`, so a false change bit for that typed field permits
reuse.  A touched first field still performs a full evaluation. -/
def opaqueFirstLaw : IncrementalLaw opaqueFirstTerm where
  apply cache delta :=
    if h : delta.changed (t := .nat) .here = true then
      fullRecompute opaqueFirstTerm delta.after
    else
      { value := cache.value
        recomputations := 0
        correct := by
          rw [cache.correct]
          simpa [opaqueFirstTerm, opaqueFirst, Term.eval] using
            delta.unchanged (.here : Var DemoSchema .nat)
              (by cases ht : delta.changed (t := .nat) (.here : Var DemoSchema .nat) <;>
                  simp_all) }

theorem fixture_custom_explicit_law_zero :
    (withLaw opaqueFirstLaw opaqueFirstCache secondChanged).recomputations = 0 :=
  rfl

theorem fixture_custom_explicit_law_correct :
    (withLaw opaqueFirstLaw opaqueFirstCache secondChanged).value =
      opaqueFirstTerm.eval secondChangedAfter :=
  withLaw_correct opaqueFirstLaw opaqueFirstCache secondChanged

theorem fixture_custom_explicit_law_touched :
    (withLaw opaqueFirstLaw opaqueFirstCache firstChanged).recomputations = 1 :=
  rfl

end Uwueave.Preo.Incremental
