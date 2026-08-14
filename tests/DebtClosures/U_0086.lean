import Uwueave.Preo.DerivedProgram

open Uwueave
open Uwueave.Preo
open Uwueave.Preo.Expr
open Uwueave.Preo.DerivedProgram

theorem debtClosure_U_0086 :
    (∀ {Γ : Schema} (program : DerivedProgram.Program Γ) (left right : Env Γ),
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
        (show pairedFieldsProgram.type.denote from ((false, 3) : Bool × Nat))
        (show pairedFieldsProgram.type.denote from ((true, 8) : Bool × Nat)) = 3 ∧
      pairedFieldsProgram.executableCombiner.maxSteps = 3) ∧
    (¬ Nonempty (ExecutableCombiner JoinHom.card)) ∧
    (¬ PreservesMerge summedFields ∧ certifyMergeSafe summedFields = none) := by
  exact ⟨Program.executableCombine_correct,
    Program.executableCombine_cost_le,
    maxFields_executable_fixture,
    ⟨pairedFields_executable_cost_fixture.1,
      pairedFields_executable_cost_fixture.2.1⟩,
    JoinHom.card_executable_refused,
    summed_fields_refused⟩
