import PreoAutomationSupport
import Uwueave.Tactics.Core

namespace Canary.PreoAutomation.NoPool

open Uwueave

inductive Bare where
  | only

instance : MergeState Bare where
  merge _ _ := .only
  merge_comm _ _ := rfl
  merge_assoc _ _ _ := rfl
  merge_idem _ := rfl

example : IConfluent (S := Bare) (fun _ => True) := by
  classify

end Canary.PreoAutomation.NoPool
