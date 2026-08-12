import Uwueave.FiniteRepairMenu
import Uwueave.TrustFloor

namespace Canary.Wave29.PositiveFiniteRepairMenu

open Uwueave Uwueave.FiniteRepairMenu
open Uwueave.FiniteRepairMenu.Examples

example : (checkUniverse positiveInput).isAccepted = true :=
  positive_input_is_accepted

example : positiveResult.foundId? = some ⟨20⟩ :=
  positive_finds_least_authored_id

example : positiveResult.price? = some
    (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 2).price :=
  positive_retains_complete_price

example : positiveResult.row?.bind RepairMenu.RepairCandidate.price =
    positiveResult.price? :=
  positive_row_price_is_exact

example : ∀ entry : MenuCandidate RepairMenu.ceilingPromise,
    entry ∈ refusedScope.entries → ¬ entry.candidate.applicable :=
  impossible_refusal_is_exactly_exhaustive

#audit_floor_prefix Uwueave.FiniteRepairMenu

end Canary.Wave29.PositiveFiniteRepairMenu
