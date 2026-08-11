/-
# Uwueave.RepairSynthesis — exact search over an explicit finite repair catalog.

`Repair` and `RepairMenu` make a repair proof-carrying, but deliberately do not
search for one.  This module adds the smallest bounded search layer: a caller
supplies a finite catalog of candidates, a decision procedure for each
candidate's residual applicability proposition, stable candidate identities,
and — only when minimisation is wanted — a valuation of the full eight-axis
`Repair.Price` into `Nat`.

The result keeps the boundary in its type:

* `found` carries a catalog member, its applicability proof, the actual
  `Repair`, its complete `Price`, and leastness under the caller's valuation;
* `refused` carries `forall candidate in catalog, not applicable`.

There is no quantification over repairs outside the supplied list, no claim
that every possible target promise has been enumerated, and no built-in scalar
order on `Price`.  In particular, the valuation is an argument rather than a
library policy.  This is the repair analogue of `Budget.FinitePlanSpace` and
uses `SeamColoring`'s already-proved finite argument-minimum rather than adding
a second minimisation calculus.
-/
import Uwueave.RepairMenu
import Uwueave.Budget

namespace Uwueave.RepairSynthesis

open Uwueave
open Uwueave.Repair (Promise Price Repair PromiseRelation)
open Uwueave.RepairMenu (RepairObligation)

/-! ## §1. Stable, proof-carrying catalog entries -/

/-- A stable identity supplied by the catalog author.  It is deliberately not
derived from a display label or from the position of an entry in a list. -/
structure CandidateId where
  value : Nat
  deriving DecidableEq, Repr

/-- One finitely searchable repair candidate.

`applicable` is the exact residual proposition the search decides.  Its proof
constructs the actual repair, and `priceAgrees` prevents an applicable row from
advertising a price other than the repair's complete eight-axis price.  An
inapplicable row may carry arbitrary display data, but it can never be returned
by `synthesize`. -/
structure Candidate (P : Promise) : Type 2 where
  id : CandidateId
  target : Promise
  applicable : Prop
  decideApplicable : Decidable applicable
  discharge : applicable → Repair P target
  price : Price
  priceAgrees : ∀ h : applicable, (discharge h).price = price

namespace Candidate

/-- An already-constructed repair is an unconditionally applicable candidate. -/
def ofRepair {P Q : Promise} (id : CandidateId) (repair : Repair P Q) : Candidate P where
  id := id
  target := Q
  applicable := True
  decideApplicable := inferInstance
  discharge := fun _ => repair
  price := repair.price
  priceAgrees := fun _ => rfl

/-- A `RepairMenu.RepairObligation` becomes searchable exactly when the caller
also supplies a decision procedure for its residual.  This does not decide an
arbitrary proposition by fiat: the `Decidable` value is explicit input. -/
def ofObligation {P Q : Promise} (id : CandidateId)
    (obligation : RepairObligation P Q)
    (decideResidual : Decidable obligation.residual) : Candidate P where
  id := id
  target := Q
  applicable := obligation.residual
  decideApplicable := decideResidual
  discharge := obligation.discharge
  price := obligation.price
  priceAgrees := obligation.priceAgrees

/-- Executable applicability, using the decision procedure stored in the row. -/
def isApplicable (candidate : Candidate P) : Bool :=
  @decide candidate.applicable candidate.decideApplicable

@[simp] theorem isApplicable_eq_true_iff (candidate : Candidate P) :
    candidate.isApplicable = true ↔ candidate.applicable := by
  exact @decide_eq_true_iff candidate.applicable candidate.decideApplicable

/-- The actual repair carried by a successful candidate. -/
def repair (candidate : Candidate P) (h : candidate.applicable) :
    Repair P candidate.target :=
  candidate.discharge h

/-- A returned repair retains the entire advertised `Price`; the search never
reconstructs a price from its scalar valuation. -/
@[simp] theorem repair_price (candidate : Candidate P) (h : candidate.applicable) :
    (candidate.repair h).price = candidate.price :=
  candidate.priceAgrees h

end Candidate

/-- An explicit finite catalog.  Stable IDs are required to be unique even
though list order is still used as the deterministic tie-breaker. -/
structure Catalog (P : Promise) : Type 2 where
  entries : List (Candidate P)
  stableIds : (entries.map Candidate.id).Nodup

namespace Catalog

variable {P : Promise}

/-- Exactly the supplied entries whose stored residual decider succeeds. -/
def applicableEntries (catalog : Catalog P) : List (Candidate P) :=
  catalog.entries.filter Candidate.isApplicable

theorem mem_applicableEntries_iff (catalog : Catalog P) (candidate : Candidate P) :
    candidate ∈ catalog.applicableEntries ↔
      candidate ∈ catalog.entries ∧ candidate.applicable := by
  simp [applicableEntries]

/-- A valuation is caller policy, never a canonical scalarization of `Price`. -/
abbrev Valuation := Price → Nat

/-- Raw executable search for the least applicable catalog member under the
caller's valuation.  Ties retain the earlier catalog entry. -/
def minimum? (catalog : Catalog P) (valuation : Valuation) : Option (Candidate P) :=
  SeamColoring.argMin? (fun candidate => valuation candidate.price)
    catalog.applicableEntries

theorem minimum_mem {catalog : Catalog P} {valuation : Valuation}
    {candidate : Candidate P} (h : catalog.minimum? valuation = some candidate) :
    candidate ∈ catalog.entries ∧ candidate.applicable := by
  apply (catalog.mem_applicableEntries_iff candidate).mp
  exact SeamColoring.argMin_mem _ h

theorem minimum_le_of_applicable {catalog : Catalog P} {valuation : Valuation}
    {candidate : Candidate P} (h : catalog.minimum? valuation = some candidate)
    {other : Candidate P} (hmem : other ∈ catalog.entries)
    (happ : other.applicable) :
    valuation candidate.price ≤ valuation other.price := by
  apply SeamColoring.argMin_le_of_mem _ h
  exact (catalog.mem_applicableEntries_iff other).mpr ⟨hmem, happ⟩

/-- `none` is exhaustive for exactly the supplied finite catalog. -/
theorem minimum_none_exhaustive (catalog : Catalog P) (valuation : Valuation)
    (h : catalog.minimum? valuation = none) :
    ∀ candidate : Candidate P, candidate ∈ catalog.entries → ¬ candidate.applicable := by
  have hempty : catalog.applicableEntries = [] :=
    (SeamColoring.argMin_eq_none_iff
      (fun candidate : Candidate P => valuation candidate.price)
      catalog.applicableEntries).mp h
  intro candidate hmem happ
  have hin : candidate ∈ catalog.applicableEntries :=
    (catalog.mem_applicableEntries_iff candidate).mpr ⟨hmem, happ⟩
  rw [hempty] at hin
  exact List.not_mem_nil hin

/-! ## §2. Evidence-bearing synthesis -/

/-- The positive branch, separated out so downstream code can retain both the
stable catalog identity and the dependent target/repair pair. -/
structure Found (catalog : Catalog P) (valuation : Valuation) : Type 2 where
  candidate : Candidate P
  member : candidate ∈ catalog.entries
  applies : candidate.applicable
  least : ∀ other : Candidate P, other ∈ catalog.entries → other.applicable →
    valuation candidate.price ≤ valuation other.price

namespace Found

/-- The actual repair, not merely its ID or price. -/
def repair {catalog : Catalog P} {valuation : Valuation}
    (found : Found catalog valuation) : Repair P found.candidate.target :=
  found.candidate.repair found.applies

/-- The complete price of the returned repair. -/
@[simp] theorem repair_price {catalog : Catalog P} {valuation : Valuation}
    (found : Found catalog valuation) :
    found.repair.price = found.candidate.price :=
  found.candidate.repair_price found.applies

end Found

/-- Total proof-carrying result.  Refusal quantifies over `catalog.entries` and
nothing larger. -/
inductive Result (catalog : Catalog P) (valuation : Valuation) : Type 2 where
  | found (witness : Found catalog valuation)
  | refused (exhaustive : ∀ candidate : Candidate P,
      candidate ∈ catalog.entries → ¬ candidate.applicable)

/-- Search the exact finite catalog. -/
def synthesize (catalog : Catalog P) (valuation : Valuation) :
    Result catalog valuation :=
  match h : catalog.minimum? valuation with
  | none => .refused (catalog.minimum_none_exhaustive valuation h)
  | some candidate =>
      let hm := minimum_mem h
      .found {
        candidate := candidate
        member := hm.1
        applies := hm.2
        least := fun other hmem happ =>
          minimum_le_of_applicable (other := other) h hmem happ
      }

namespace Result

/-- A first-order observer used only to test which evidence-bearing branch the
executable search took. -/
def isFound {catalog : Catalog P} {valuation : Valuation} :
    Result catalog valuation → Bool
  | .found _ => true
  | .refused _ => false

/-- The stable identity of the returned candidate, if any. -/
def foundId? {catalog : Catalog P} {valuation : Valuation} :
    Result catalog valuation → Option CandidateId
  | .found witness => some witness.candidate.id
  | .refused _ => none

/-- The full price of the returned repair, if any. -/
def price? {catalog : Catalog P} {valuation : Valuation} :
    Result catalog valuation → Option Price
  | .found witness => some witness.candidate.price
  | .refused _ => none

/-- A negative branch observer can be turned back into the exhaustive theorem;
the proof is not discarded by the Boolean view. -/
theorem exhaustive_of_isFound_false {catalog : Catalog P} {valuation : Valuation}
    (result : Result catalog valuation) (h : result.isFound = false) :
    ∀ candidate : Candidate P, candidate ∈ catalog.entries → ¬ candidate.applicable := by
  cases result with
  | found witness => simp [isFound] at h
  | refused exhaustive => exact exhaustive

end Result

end Catalog

/-! ## §3. Executable examples -/

namespace Examples

open Catalog

/-- An explicit deployment valuation used only by this example.  It charges one
arbiter cut as three seam crossings.  The library does not endorse that
conversion; passing it as an argument is the point. -/
def deploymentValuation : Catalog.Valuation :=
  fun price => price.seamCrossings + 3 * price.arbiterCuts

def fullFour : Candidate RepairMenu.ceilingPromise :=
  Candidate.ofRepair ⟨10⟩
    (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 4)

/-- A deliberately inapplicable row advertises scalar score zero.  It is
filtered before minimisation, so it cannot beat a real repair. -/
def unavailable : Candidate RepairMenu.ceilingPromise :=
  Candidate.ofObligation ⟨20⟩
    (RepairMenu.emptyObligation RepairMenu.ceilingPromise RepairMenu.ceilingPromise
      Price.free PromiseRelation.equivalent)
    (by
      apply isFalse
      intro h
      exact h)

def arbitration : Candidate RepairMenu.ceilingPromise :=
  Candidate.ofRepair ⟨30⟩ RepairMenu.pinArbitrate

def fullTwo : Candidate RepairMenu.ceilingPromise :=
  Candidate.ofRepair ⟨40⟩
    (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 2)

/-- The least applicable row is last, demonstrating that search is not
first-applicable.  The inapplicable zero-price row and the multi-axis
arbitration row make this more than a two-number `min`. -/
def foundCatalog : Catalog RepairMenu.ceilingPromise where
  entries := [fullFour, unavailable, arbitration, fullTwo]
  stableIds := by decide

def foundResult : Catalog.Result foundCatalog deploymentValuation :=
  foundCatalog.synthesize deploymentValuation

theorem finds_least_applicable :
    foundResult.foundId? = some ⟨40⟩ := by decide

/-- The winning repair's entire record survives; only the comparison used the
caller-supplied scalar valuation. -/
theorem found_price_is_complete :
    foundResult.price? = some
      (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 2).price := by
  decide

theorem found_score_is_two :
    foundResult.price?.map deploymentValuation = some 2 := by decide

/-- Two explicitly unsatisfiable obligations form a finite catalog that really
refuses.  This is not a claim that no repair of the ceiling exists. -/
def unavailableAgain : Candidate RepairMenu.ceilingPromise :=
  Candidate.ofObligation ⟨51⟩
    (RepairMenu.emptyObligation RepairMenu.ceilingPromise RepairMenu.ceilingPromise
      { Price.free with seamCrossings := 7 } PromiseRelation.equivalent)
    (by
      apply isFalse
      intro h
      exact h)

def refusedCatalog : Catalog RepairMenu.ceilingPromise where
  entries := [unavailable, unavailableAgain]
  stableIds := by decide

def refusedResult : Catalog.Result refusedCatalog deploymentValuation :=
  refusedCatalog.synthesize deploymentValuation

theorem finite_catalog_refuses : refusedResult.isFound = false := by decide

/-- The computed refusal re-exposes its theorem over exactly the two supplied
rows. -/
theorem refusal_is_exhaustive_for_catalog :
    ∀ candidate : Candidate RepairMenu.ceilingPromise,
      candidate ∈ refusedCatalog.entries → ¬ candidate.applicable :=
  refusedResult.exhaustive_of_isFound_false finite_catalog_refuses

end Examples

end Uwueave.RepairSynthesis
