import PreoAutomationSupport
import Uwueave.Preo.Elab

namespace Canary.PreoAutomation.RollbackReuse

open Uwueave Uwueave.Catalog Uwueave.Preo Uwueave.Spec
open PreoAutomationSupport

axiom poisoned : False

def rejectedVerdict : Verdict (fun s : GSet Nat => s 0 = true) :=
  .free (False.elim poisoned)

/-! The failed command must roll back its entire generated namespace. -/
/--
error: preo: the verdict `Canary.PreoAutomation.RollbackReuse.Reused.has_genesis.verdict` depends on
-/
#guard_msgs (error, substring := true) in
preo Reused where
  field notes : GrowSet Nat
  invariant has_genesis : notes 0 = true := rejectedVerdict

#assert_no_decl Reused.State
#assert_no_decl Reused.notes
#assert_no_decl Reused.has_genesis
#assert_no_decl Reused.has_genesis.verdict
#assert_no_decl Reused.has_genesis.classification

/-! Reusing the identical top-level name is the observable rollback test. -/
preo Reused where
  field notes : GrowSet Nat
  invariant has_genesis : notes 0 = true

#assert_decl Reused.State
#assert_decl Reused.notes
#assert_decl Reused.has_genesis
#assert_decl Reused.has_genesis.verdict
#assert_decl Reused.has_genesis.classification
#assert_decl Reused.has_genesis.onState

end Canary.PreoAutomation.RollbackReuse
