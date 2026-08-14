import Uwueave.HonestRender

open Uwueave

theorem debtClosure_U_0083 :
    (∀ p : Prop,
      (HonestRender.stdCarrier.{1} (fun _ _ : Unit => True) Nat).elim
          (β := Prop)
          ((HonestRender.stdCarrier.{1} (fun _ _ : Unit => True) Nat).report ()
            (Evidence.View.exact 7))
          (fun _ => p) (fun _ => False) False False False = p) ∧
    (HonestRender.stdCarrier.{2} (fun _ _ : Unit => True) Nat).elim
        (β := ULift.{1} Nat)
        ((HonestRender.stdCarrier.{2} (fun _ _ : Unit => True) Nat).report ()
          (Evidence.View.exact 7))
        (fun n => ULift.up n) (fun n => ULift.up n)
        (ULift.up 0) (ULift.up 0) (ULift.up 0) = ULift.up 7 := by
  exact ⟨HonestRender.elim_prop_fixture, HonestRender.elim_type1_fixture⟩
