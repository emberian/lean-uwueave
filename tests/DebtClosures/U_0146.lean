import Uwueave.TextOperational
import Uwueave.Preo.DerivedProgram
import Uwueave.Preo.ContextQueryCompiler

open Uwueave
open Uwueave.TextSummary Uwueave.TextOperational
open Uwueave.Preo Uwueave.Preo.Expr Uwueave.Preo.DerivedProgram
open Uwueave.Preo.ContextQueryCompiler

theorem debtClosure_U_0146 :
    -- Representation/content: retained payloads project to the exact
    -- `TextSummary` labelling, and collisions remain a concrete refusal case.
    ((∀ ops : List ContentInsert, CanonicalBatch ops → CollisionFree ops →
        CollisionFree ops ∧ ∀ operation ∈ ops,
          (project ops).1 (operation.id, operation.anchor) = true ∧
          TextSummary.glyph operation.id = operation.content) ∧
      (∀ state operation,
        projectContent (applyContent state (.insert operation)) =
          (projectSeq (operation :: state.insertions), state.tombstones)) ∧
      (project [collisionLeft] = project [collisionRight] ∧
        collisionLeft.content ≠ collisionRight.content ∧
        ¬ CollisionFree [collisionLeft, collisionRight]) ∧
      (canonicalFugueText 4 (fugueALow ⊔ fugueBMid) =
          fugueText 4 (fugueALow ⊔ fugueBMid) ∧
        canonicalFugueText 4 (fugueALow ⊔ fugueBMid) = [.a, .b])) ∧
    -- U-0086: checked executable combiners, exact work bounds, and refusals.
    ((∀ {Γ : Schema} (program : DerivedProgram.Program Γ)
        (left right : Env Γ),
        program.eval (left ⊔ right) = program.executableCombiner.combine
          (program.eval left) (program.eval right)) ∧
      (∀ {Γ : Schema} (program : DerivedProgram.Program Γ)
          (left right : program.type.denote),
        program.executableCombiner.combineSteps left right ≤
          program.executableCombiner.maxSteps) ∧
      (maxFields.executableCombiner.combine
          (show maxFields.type.denote from (3 : Nat))
          (show maxFields.type.denote from (8 : Nat)) =
            (show maxFields.type.denote from (8 : Nat)) ∧
        maxFields.executableCombiner.combineSteps
          (show maxFields.type.denote from (3 : Nat))
          (show maxFields.type.denote from (8 : Nat)) = 1 ∧
        maxFields.executableCombiner.maxSteps = 1) ∧
      (pairedFieldsProgram.executableCombiner.combineSteps
          (show pairedFieldsProgram.type.denote from
            ((false, 3) : Bool × Nat))
          (show pairedFieldsProgram.type.denote from
            ((true, 8) : Bool × Nat)) = 3 ∧
        pairedFieldsProgram.executableCombiner.maxSteps = 3) ∧
      (¬ Nonempty (ExecutableCombiner JoinHom.card)) ∧
      (¬ PreservesMerge summedFields ∧
        certifyMergeSafe summedFields = none)) ∧
    -- U-0113: typed compiler classes are sound and complete on the admitted
    -- finite universe, with the membership-query fixture compiled exactly.
    ((∀ {State : Type} {schema : Preo.Expr.Schema} [MergeState State]
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
          CtxEquiv (MinimalSummary.memQuery true) left right)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨collision_free_projection_agrees, projectContent_insert,
      collision_counterexample, canonical_fugue_witness_agrees⟩
  · exact ⟨DerivedProgram.Program.executableCombine_correct,
      DerivedProgram.Program.executableCombine_cost_le,
      maxFields_executable_fixture,
      ⟨pairedFields_executable_cost_fixture.1,
        pairedFields_executable_cost_fixture.2.1⟩,
      JoinHom.card_executable_refused,
      summed_fields_refused⟩
  · exact ⟨fun query left right => query.signature_eq_iff_eval left right,
      fun query _ _ state => query.state_class_present state,
      fun query _ _ key => query.class_key_sound key,
      Fixtures.membership_program_is_checked,
      Fixtures.membership_compiles_two_classes,
      Fixtures.membership_classes_exact⟩
