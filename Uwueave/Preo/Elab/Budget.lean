/-
# Uwueave.Preo.Elab.Budget — five-currency budget command core.

No command elaborator is registered here.  The facade owns the single public
registration and delegates to `elabPreoBudgetCore`.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Protocol

namespace Uwueave.Preo.Elab.Budget

open Lean Elab Command Uwueave.Preo.Elab.Internal

/-- Non-registered implementation of `preo_budget`.  Its generated
`ProfileUpperBound` is one checked plan satisfying all five currency
coordinates; the peer-barrier theorem is only a compatibility projection. -/
def elabPreoBudgetCore : CommandElab := fun stx => withEnvTransaction do
  let `(command| preo_budget $nm for $session : $limits := $proof) := stx
    | throwError "preo_budget: malformed declaration"
  let limitsId := mkIdent (nm.getId ++ `Limits)
  let sessionId := mkIdent (nm.getId ++ `Session)
  let planId := mkIdent (nm.getId ++ `Plan)
  let peerId := mkIdent (nm.getId ++ `PeerUpperBound)
  emitRequired (← `(command|
    /-- The five explicit currency limits; no total or crossing conversion. -/
    abbrev $limitsId : Uwueave.Scheduling.Currency → Nat := $limits))
  emitRequired (← `(command|
    /-- The exact semantic session selected by the named elaboration. -/
    abbrev $sessionId : Uwueave.Scheduling.Session :=
      Uwueave.Protocol.Elaboration.session $session))
  emitRequired (← `(command|
    /-- One checked plan satisfying every currency coordinate. -/
    def $nm : Uwueave.Scheduling.ProfileUpperBound $sessionId $limitsId :=
      $proof))
  emitRequired (← `(command|
    /-- The exhibited plan carried by this profile acceptance. -/
    def $planId : Uwueave.Scheduling.Plan $sessionId :=
      Uwueave.Scheduling.ProfileUpperBound.plan $nm))
  emitRequired (← `(command|
    /-- Compatibility projection for the peer-barrier coordinate only. -/
    def $peerId : Uwueave.Scheduling.UpperBound $sessionId
        ($limitsId .peerBarrier) :=
      Uwueave.Scheduling.ProfileUpperBound.toUpperBound $nm))
  let ns ← getCurrNamespace
  floorCheck nm "five-currency budget" (ns ++ nm.getId)

end Uwueave.Preo.Elab.Budget
