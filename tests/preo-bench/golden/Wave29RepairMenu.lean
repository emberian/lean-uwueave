import Uwueave.FiniteRepairMenu

namespace PreoBench.Golden.Wave29RepairMenu

open Uwueave
open Uwueave.FiniteRepairMenu
open Uwueave.FiniteRepairMenu.Examples

def orderedApplicability : List (Nat × Bool) :=
  positiveInput.entries.map fun entry =>
    (entry.id.value, entry.isApplicable)

def selectedId : Option Nat :=
  positiveResult.foundId?.map RepairSynthesis.CandidateId.value

def completePrice : Option Repair.Price := positiveResult.price?

def rowPrice : Option Repair.Price :=
  positiveResult.row?.bind RepairMenu.RepairCandidate.price

def refusalKinds : List (Option Check.RefusalKind) :=
  [ (checkUniverse tooLargeInput).refusalKind?,
    (checkUniverse nonCanonicalInput).refusalKind? ]

#guard orderedApplicability = [(10, false), (20, true), (40, true)]
#guard selectedId = some 20
#guard completePrice = some
  (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 2).price
#guard rowPrice = completePrice
#guard refusedResult.isFound = false
#guard (synthesize emptyScope).isFound = false
#guard refusalKinds = [some .tooLarge, some .nonCanonical]

#eval orderedApplicability
#eval selectedId
#eval completePrice
#eval refusedResult.isFound
#eval refusalKinds

end PreoBench.Golden.Wave29RepairMenu
