/-
# Uwueave.Preo.ContextQueryCompiler — checked typed queries to finite contexts.

`Expr.Program` can exist only after `Expr.Raw.infer` succeeds. This module binds
that intrinsically typed program to application state through a typed
projection, admits it only with a complete finite state enumeration, then
produces `ContextCompiler.Spec` using that same enumeration for states and
merge contexts.

Soundness and completeness are semantic: equal computed signatures are
exactly `MinimalSummary.CtxEquiv` for the checked evaluator.  The scope is the
explicit finite carrier certified by `complete`; no syntax tree is claimed to
enumerate deployment states by itself.
-/
import Uwueave.ContextCompiler
import Uwueave.Preo.Expr

namespace Uwueave.Preo.ContextQueryCompiler

open Uwueave

/-- A checked typed Preoscript query with an admitted complete finite state
universe. -/
structure AdmittedQuery (State : Type) (schema : Expr.Schema)
    [MergeState State] where
  program : Expr.Program schema
  project : State → Expr.Env schema
  states : List State
  complete : ∀ state : State, state ∈ states

variable {State : Type} {schema : Expr.Schema} [MergeState State]

/-- The semantics of the checked expression after its typed state projection. -/
def AdmittedQuery.eval (query : AdmittedQuery State schema) (state : State) :
    query.program.type.denote :=
  query.program.eval (query.project state)

/-- Compile the checked typed evaluator to a one-query contextual classifier. -/
def AdmittedQuery.spec (query : AdmittedQuery State schema) :
    ContextCompiler.Spec State query.program.type.denote where
  states := query.states
  contexts := query.states
  queries := [query.eval]

/-- **Semantic compiler exactness.** The computed signature classes are sound
and complete for the checked query semantics on the admitted finite universe. -/
theorem AdmittedQuery.signature_eq_iff_eval (query : AdmittedQuery State schema)
    (left right : State) :
    query.spec.signature left = query.spec.signature right ↔
      CtxEquiv query.eval left right := by
  have h := ContextCompiler.signature_eq_iff_all_ctxEquiv_of_complete
    query.spec query.complete left right
  simpa [AdmittedQuery.spec] using h

/-- The executable same-class test has exactly the checked query semantics. -/
theorem AdmittedQuery.sameClass_eq_true_iff_eval
    (query : AdmittedQuery State schema)
    [BEq query.program.type.denote]
    [LawfulBEq query.program.type.denote]
    (left right : State) :
    query.spec.sameClass left right = true ↔
      CtxEquiv query.eval left right := by
  rw [ContextCompiler.Spec.sameClass, beq_iff_eq,
    query.signature_eq_iff_eval]

/-- Every admitted carrier state has a computed class key. -/
theorem AdmittedQuery.state_class_present
    (query : AdmittedQuery State schema)
    [BEq query.program.type.denote]
    [LawfulBEq query.program.type.denote]
    (state : State) :
    query.spec.signature state ∈ query.spec.classKeys :=
  (ContextCompiler.mem_classKeys_iff query.spec _).mpr
    ⟨state, query.complete state, rfl⟩

/-- Conversely every computed key comes from an admitted state; no class is
invented by deduplication. -/
theorem AdmittedQuery.class_key_sound
    (query : AdmittedQuery State schema)
    [BEq query.program.type.denote]
    [LawfulBEq query.program.type.denote]
    (key : ContextCompiler.Signature query.program.type.denote) :
    key ∈ query.spec.classKeys ↔
      ∃ state : State, query.spec.signature state = key := by
  rw [ContextCompiler.mem_classKeys_iff]
  constructor
  · rintro ⟨state, _, h⟩
    exact ⟨state, h⟩
  · rintro ⟨state, h⟩
    exact ⟨state, query.complete state, h⟩

namespace Fixtures

open Uwueave.Catalog

abbrev MembershipSchema : Expr.Schema := [.bool]

def membershipProgram : Expr.Program MembershipSchema where
  raw := .field 0
  success := by decide

theorem membership_program_is_checked :
    membershipProgram.raw.infer MembershipSchema =
      some membershipProgram.checked :=
  membershipProgram.inferred

theorem boolStates_complete (state : GSet Bool) :
    state ∈ ContextCompiler.Fixtures.boolStates := by
  cases hfalse : state false <;> cases htrue : state true
  · have hstate : state = ContextCompiler.Fixtures.emptyBool := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]
  · have hstate : state = JoinHom.sawB := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]
  · have hstate : state = JoinHom.sawA := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]
  · have hstate : state = ContextCompiler.Fixtures.fullBool := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]

def membershipQuery : AdmittedQuery (GSet Bool) MembershipSchema where
  program := membershipProgram
  project := fun state => .cons (state true) .nil
  states := ContextCompiler.Fixtures.boolStates
  complete := boolStates_complete

theorem membership_eval_eq (state : GSet Bool) :
    membershipQuery.eval state = MinimalSummary.memQuery true state := rfl

theorem membership_compiles_two_classes :
    membershipQuery.spec.classKeys.length = 2 := by
  decide

theorem membership_classes_exact (left right : GSet Bool) :
    membershipQuery.spec.signature left = membershipQuery.spec.signature right ↔
      CtxEquiv (MinimalSummary.memQuery true) left right := by
  simpa only [membership_eval_eq] using membershipQuery.signature_eq_iff_eval left right

end Fixtures

end Uwueave.Preo.ContextQueryCompiler
