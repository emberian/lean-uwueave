import Uwueave.TrustFloor

open Lean Elab Command

elab "#scan_trust_canary_tree" : command => do
  let some directory ← liftIO <| IO.getEnv "UWUEAVE_TRUST_CANARY_ROOT"
    | throwError "UWUEAVE_TRUST_CANARY_ROOT is required"
  discard <| liftIO <| Uwueave.TrustFloor.leanModulesUnder directory

-- The runner supplies a temporary tree containing a source symlink.  The real
-- filesystem census must reject it before deriving any module coverage set.
#scan_trust_canary_tree
