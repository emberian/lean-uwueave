import Uwueave.TrustFloor

namespace Canary.RootHeader

theorem checked : True := True.intro

end Canary.RootHeader

open Lean Elab Command in
elab "#assert_indented_root_import" : command => do
  let imports ← liftIO <| Uwueave.TrustFloor.directImports "Uwueave.lean"
  unless imports.any (fun imp => imp.module == `Uwueave.TrustFloor) do
    throwError "Lean's header parser did not retain the indented TrustFloor import"

#assert_indented_root_import
#audit_floor_prefix Canary.RootHeader
