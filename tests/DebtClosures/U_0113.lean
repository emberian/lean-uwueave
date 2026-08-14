import Uwueave.Preo.ContextQueryCompiler

open Uwueave
open Uwueave.Preo.ContextQueryCompiler

theorem debtClosure_U_0113 :
    (∀ {State : Type} {schema : Preo.Expr.Schema} [MergeState State]
      (query : AdmittedQuery State schema) (left right : State),
      query.spec.signature left = query.spec.signature right ↔
        CtxEquiv query.eval left right) ∧
    (∀ {State : Type} {schema : Preo.Expr.Schema} [MergeState State]
      (query : AdmittedQuery State schema)
      [BEq query.program.type.denote]
      [LawfulBEq query.program.type.denote]
      (state : State), query.spec.signature state ∈ query.spec.classKeys) ∧
    (∀ {State : Type} {schema : Preo.Expr.Schema} [MergeState State]
      (query : AdmittedQuery State schema)
      [BEq query.program.type.denote]
      [LawfulBEq query.program.type.denote]
      (key : ContextCompiler.Signature query.program.type.denote),
      key ∈ query.spec.classKeys ↔
        ∃ state : State, query.spec.signature state = key) ∧
    Fixtures.membershipProgram.raw.infer Fixtures.MembershipSchema =
      some Fixtures.membershipProgram.checked ∧
    Fixtures.membershipQuery.spec.classKeys.length = 2 ∧
    (∀ left right : Catalog.GSet Bool,
      Fixtures.membershipQuery.spec.signature left =
          Fixtures.membershipQuery.spec.signature right ↔
        CtxEquiv (MinimalSummary.memQuery true) left right) := by
  exact ⟨fun query left right => query.signature_eq_iff_eval left right,
    fun query _ _ state => query.state_class_present state,
    fun query _ _ key => query.class_key_sound key,
    Fixtures.membership_program_is_checked,
    Fixtures.membership_compiles_two_classes,
    Fixtures.membership_classes_exact⟩
