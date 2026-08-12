/-
# Uwueave.FiniteRepairMenu — bounded, canonical repair-menu search

`RepairSynthesis` searches an already proof-carrying catalog with a caller's
scalar valuation.  This downstream leaf supplies a different policy boundary
for author-facing menus: raw rows are checked for an explicit size bound and a
strict stable-ID order, then the first applicable row is returned.  Because the
checked list is strictly increasing, that row is the least applicable stable
ID in exactly this finite universe.

The result retains the actual typed `Repair`, the generated `RepairCandidate`
menu row, and the complete eight-axis `Price`.  No price field is converted to
another and no order on `Price` is claimed.  Refusal is exhaustive only for the
listed rows.  Nothing here claims that the list contains every possible repair,
menu exit, target promise, colouring, or inhabitant of an infinite carrier.

The leaf is usable as the repair catalog boundary of `Preo.Planning`, which
already composes finite schedule and repair search; it does not duplicate that
paired scheduler.
-/
import Uwueave.RepairSynthesis

namespace Uwueave.FiniteRepairMenu

open Uwueave
open Uwueave.Repair (Promise Price Repair)

/-! ## Canonical finite input -/

/-- One searchable repair with inert menu presentation data.  The generated
row below is not authored: it is definitionally the exact repair discharged by
`candidate`. -/
structure MenuCandidate (P : Promise) : Type 2 where
  candidate : RepairSynthesis.Candidate P
  tag : Exits.Exit P.State
  label : String

namespace MenuCandidate

/-- Stable candidate identity. -/
abbrev id {P : Promise} (entry : MenuCandidate P) :
    RepairSynthesis.CandidateId := entry.candidate.id

/-- Executable residual test inherited from `RepairSynthesis`. -/
def isApplicable {P : Promise} (entry : MenuCandidate P) : Bool :=
  entry.candidate.isApplicable

@[simp] theorem isApplicable_eq_true_iff {P : Promise}
    (entry : MenuCandidate P) :
    entry.isApplicable = true ↔ entry.candidate.applicable :=
  entry.candidate.isApplicable_eq_true_iff

/-- Generate an available menu row only from the exact discharged repair. -/
def row {P : Promise} (entry : MenuCandidate P)
    (h : entry.candidate.applicable) : RepairMenu.RepairCandidate P :=
  .available entry.tag entry.label entry.candidate.target
    (entry.candidate.repair h)

@[simp] theorem row_price {P : Promise} (entry : MenuCandidate P)
    (h : entry.candidate.applicable) :
    (entry.row h).price = some entry.candidate.price := by
  simp [row, RepairMenu.RepairCandidate.price,
    RepairSynthesis.Candidate.repair_price]

@[simp] theorem row_delta {P : Promise} (entry : MenuCandidate P)
    (h : entry.candidate.applicable) :
    (entry.row h).delta =
      some (entry.candidate.repair h).relation := rfl

end MenuCandidate

/-- Untrusted finite menu input.  `maxEntries` is checked before search; the
list order is accepted only when stable IDs are strictly increasing. -/
structure UniverseInput (P : Promise) : Type 2 where
  entries : List (MenuCandidate P)
  maxEntries : Nat

/-- Strict stable-ID order.  It is both the canonical presentation/list order
and the explicit authored total order minimized by this leaf.  Numeric identity
does not semantically rank repairs; choosing these IDs is choosing this
deterministic policy. -/
def Canonical {P : Promise} (entries : List (MenuCandidate P)) : Prop :=
  entries.Pairwise fun left right => left.id.value < right.id.value

instance {P : Promise} (entries : List (MenuCandidate P)) :
    Decidable (Canonical entries) := by
  unfold Canonical
  infer_instance

/-- Proof-carrying universe admitted to search. -/
structure CheckedUniverse (P : Promise) : Type 2 where
  entries : List (MenuCandidate P)
  maxEntries : Nat
  withinBound : entries.length ≤ maxEntries
  canonical : Canonical entries

namespace CheckedUniverse

/-- Canonical stable-ID order implies the uniqueness required by the existing
`RepairSynthesis` catalog interface. -/
theorem stableIds (scope : CheckedUniverse P) :
    (scope.entries.map fun entry => entry.candidate.id).Nodup := by
  have distinct : scope.entries.Pairwise fun left right => left.id ≠ right.id :=
    scope.canonical.imp fun less equal => by
      have valuesEqual : _ := congrArg RepairSynthesis.CandidateId.value equal
      exact Nat.ne_of_lt less valuesEqual
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact distinct

/-- Forget presentation data and expose the exact underlying catalog for
`RepairSynthesis` or `Preo.Planning`; no entries are reordered or invented. -/
def toCatalog (scope : CheckedUniverse P) : RepairSynthesis.Catalog P where
  entries := scope.entries.map MenuCandidate.candidate
  stableIds := by
    simpa only [List.map_map, Function.comp_def] using scope.stableIds

end CheckedUniverse

/-- Evidence-bearing input check.  Rejections retain exact raw input facts,
including the actual length/bound or the negated canonical-order proposition.
For a noncanonical list the latter retains `¬ Canonical input.entries`; it does
not expose an arbitrary diagnostic row or select an offending pair. -/
inductive Check {P : Promise} (input : UniverseInput P) : Type 2 where
  | accepted (scope : CheckedUniverse P)
      (entriesExact : scope.entries = input.entries)
      (boundExact : scope.maxEntries = input.maxEntries)
  | tooLarge (actual : Nat) (maximum : Nat)
      (actualExact : actual = input.entries.length)
      (maximumExact : maximum = input.maxEntries)
      (exceeds : maximum < actual)
  | nonCanonical (notCanonical : ¬ Canonical input.entries)

/-- Check the bound first, then canonical stable-ID order.  No search is run on
either rejected input. -/
def checkUniverse {P : Promise} (input : UniverseInput P) : Check input :=
  if hbound : input.entries.length ≤ input.maxEntries then
    if hcanonical : Canonical input.entries then
      .accepted {
        entries := input.entries
        maxEntries := input.maxEntries
        withinBound := hbound
        canonical := hcanonical
      } rfl rfl
    else
      .nonCanonical hcanonical
  else
    .tooLarge input.entries.length input.maxEntries rfl rfl (by omega)

namespace Check

inductive RefusalKind where
  | tooLarge
  | nonCanonical
  deriving DecidableEq, Repr

def isAccepted {P : Promise} {input : UniverseInput P} : Check input → Bool
  | .accepted .. => true
  | .tooLarge .. => false
  | .nonCanonical .. => false

def refusalKind? {P : Promise} {input : UniverseInput P} :
    Check input → Option RefusalKind
  | .accepted .. => none
  | .tooLarge .. => some .tooLarge
  | .nonCanonical .. => some .nonCanonical

end Check

/-! ## First applicable is least in the checked total order -/

namespace CheckedUniverse

variable {P : Promise}
universe u

/-- Exactly the applicable rows from the checked finite universe, retaining
canonical list order. -/
def applicableEntries (scope : CheckedUniverse P) : List (MenuCandidate P) :=
  scope.entries.filter MenuCandidate.isApplicable

theorem mem_applicableEntries_iff (scope : CheckedUniverse P)
    (entry : MenuCandidate P) :
    entry ∈ scope.applicableEntries ↔
      entry ∈ scope.entries ∧ entry.candidate.applicable := by
  simp [applicableEntries]

/-- Executable canonical choice. -/
def minimum? (scope : CheckedUniverse P) : Option (MenuCandidate P) :=
  scope.applicableEntries.head?

private theorem head?_eq_some_mem {X : Type u} {xs : List X} {x : X}
    (h : xs.head? = some x) : x ∈ xs := by
  cases xs with
  | nil => simp at h
  | cons head tail =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst x
      exact List.mem_cons_self

private theorem pairwise_lt_of_mem_after {X : Type u} {f : X → Nat}
    {head : X} {tail : List X}
    (ordered : (head :: tail).Pairwise fun left right => f left < f right)
    {other : X} (otherMem : other ∈ head :: tail) :
    f head ≤ f other := by
  rcases List.mem_cons.mp otherMem with rfl | inTail
  · exact Nat.le_refl _
  · exact Nat.le_of_lt ((List.pairwise_cons.mp ordered).1 other inTail)

theorem minimum_mem {scope : CheckedUniverse P} {entry : MenuCandidate P}
    (h : scope.minimum? = some entry) :
    entry ∈ scope.entries ∧ entry.candidate.applicable := by
  apply (scope.mem_applicableEntries_iff entry).mp
  exact head?_eq_some_mem (by simpa [minimum?] using h)

theorem minimum_le_of_applicable {scope : CheckedUniverse P}
    {entry : MenuCandidate P} (h : scope.minimum? = some entry)
    {other : MenuCandidate P} (otherMem : other ∈ scope.entries)
    (otherApplies : other.candidate.applicable) :
    entry.id.value ≤ other.id.value := by
  have entryHead : scope.applicableEntries =
      entry :: scope.applicableEntries.tail := by
    cases happ : scope.applicableEntries with
    | nil => simp [minimum?, happ] at h
    | cons head tail =>
        simp only [minimum?, happ, List.head?_cons, Option.some.injEq] at h
        subst head
        rfl
  have applicableOrdered : Canonical scope.applicableEntries :=
    scope.canonical.filter _
  have otherIn : other ∈ scope.applicableEntries :=
    (scope.mem_applicableEntries_iff other).mpr ⟨otherMem, otherApplies⟩
  rw [entryHead] at applicableOrdered otherIn
  exact pairwise_lt_of_mem_after
    (f := fun row : MenuCandidate P => row.id.value)
    applicableOrdered otherIn

/-- `none` is exhaustive for exactly the checked entries. -/
theorem minimum_none_exhaustive (scope : CheckedUniverse P)
    (h : scope.minimum? = none) :
    ∀ entry : MenuCandidate P,
      entry ∈ scope.entries → ¬ entry.candidate.applicable := by
  have empty : scope.applicableEntries = [] := by
    cases he : scope.applicableEntries with
    | nil => rfl
    | cons head tail => simp [minimum?, he] at h
  intro entry member applies
  have : entry ∈ scope.applicableEntries :=
    (scope.mem_applicableEntries_iff entry).mpr ⟨member, applies⟩
  rw [empty] at this
  exact List.not_mem_nil this

end CheckedUniverse

/-! ## Proof-carrying result -/

/-- Successful bounded choice.  `leastId` compares only applicable rows of the
exact checked list.  It is not a theorem about `Price`. -/
structure Found {P : Promise} (scope : CheckedUniverse P) : Type 2 where
  entry : MenuCandidate P
  member : entry ∈ scope.entries
  applies : entry.candidate.applicable
  leastId : ∀ other : MenuCandidate P,
    other ∈ scope.entries → other.candidate.applicable →
      entry.id.value ≤ other.id.value

namespace Found

/-- Exact typed repair selected by this row. -/
def repair {P : Promise} {scope : CheckedUniverse P}
    (found : Found scope) : Repair P found.entry.candidate.target :=
  found.entry.candidate.repair found.applies

/-- Exact available menu row generated from `repair`. -/
def row {P : Promise} {scope : CheckedUniverse P}
    (found : Found scope) : RepairMenu.RepairCandidate P :=
  found.entry.row found.applies

/-- Complete eight-axis price; it is observed, never ordered here. -/
def price {P : Promise} {scope : CheckedUniverse P}
    (found : Found scope) : Price := found.entry.candidate.price

@[simp] theorem repair_price {P : Promise} {scope : CheckedUniverse P}
    (found : Found scope) : found.repair.price = found.price :=
  found.entry.candidate.repair_price found.applies

@[simp] theorem row_price {P : Promise} {scope : CheckedUniverse P}
    (found : Found scope) : found.row.price = some found.price :=
  found.entry.row_price found.applies

end Found

/-- Total result for one checked finite universe. -/
inductive Result {P : Promise} (scope : CheckedUniverse P) : Type 2 where
  | found (witness : Found scope)
  | refused (exhaustive : ∀ entry : MenuCandidate P,
      entry ∈ scope.entries → ¬ entry.candidate.applicable)

/-- Search the already checked canonical universe. -/
def synthesize {P : Promise} (scope : CheckedUniverse P) : Result scope :=
  match h : scope.minimum? with
  | none => .refused (scope.minimum_none_exhaustive h)
  | some entry =>
      let member := scope.minimum_mem h
      .found {
        entry := entry
        member := member.1
        applies := member.2
        leastId := fun _other otherMem otherApplies =>
          scope.minimum_le_of_applicable h otherMem otherApplies
      }

namespace Result

def isFound {P : Promise} {scope : CheckedUniverse P} :
    Result scope → Bool
  | .found _ => true
  | .refused _ => false

def foundId? {P : Promise} {scope : CheckedUniverse P} :
    Result scope → Option RepairSynthesis.CandidateId
  | .found witness => some witness.entry.id
  | .refused _ => none

def price? {P : Promise} {scope : CheckedUniverse P} :
    Result scope → Option Price
  | .found witness => some witness.price
  | .refused _ => none

def row? {P : Promise} {scope : CheckedUniverse P} :
    Result scope → Option (RepairMenu.RepairCandidate P)
  | .found witness => some witness.row
  | .refused _ => none

theorem exhaustive_of_isFound_false {P : Promise}
    {scope : CheckedUniverse P} (result : Result scope)
    (h : result.isFound = false) :
    ∀ entry : MenuCandidate P,
      entry ∈ scope.entries → ¬ entry.candidate.applicable := by
  cases result with
  | found witness => simp [isFound] at h
  | refused exhaustive => exact exhaustive

end Result

/-! ## Executed acceptance and refusal fixtures -/

namespace Examples

def unavailable (id : Nat) : MenuCandidate RepairMenu.ceilingPromise where
  candidate := RepairSynthesis.Candidate.ofObligation ⟨id⟩
    (RepairMenu.emptyObligation RepairMenu.ceilingPromise
      RepairMenu.ceilingPromise Repair.Price.free
      Repair.PromiseRelation.equivalent)
    (isFalse fun impossible => impossible)
  tag := .exposedFork
  label := "unavailable"

def full (id crossings : Nat) : MenuCandidate RepairMenu.ceilingPromise where
  candidate := RepairSynthesis.Candidate.ofRepair ⟨id⟩
    (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise crossings)
  tag := .fullCoordination crossings
  label := "fullCoordination"

/-- One unavailable row precedes two real rows.  Strict authored ID order makes
the first real row the exact finite minimum, while its complete `Price` remains
untouched. -/
def positiveInput : UniverseInput RepairMenu.ceilingPromise where
  entries := [unavailable 10, full 20 2, full 40 4]
  maxEntries := 3

def positiveScope : CheckedUniverse RepairMenu.ceilingPromise :=
  { entries := positiveInput.entries
    maxEntries := positiveInput.maxEntries
    withinBound := by decide
    canonical := by decide }

theorem positive_input_is_accepted :
    (checkUniverse positiveInput).isAccepted = true := by decide

def positiveResult : Result positiveScope := synthesize positiveScope

theorem positive_finds_least_authored_id :
    positiveResult.foundId? = some ⟨20⟩ := by decide

theorem positive_retains_complete_price :
    positiveResult.price? = some
      (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 2).price := by
  decide

theorem positive_row_price_is_exact :
    positiveResult.row?.bind RepairMenu.RepairCandidate.price =
      positiveResult.price? := by decide

/-- Stable numeric IDs are authored ordering policy, not semantic repair cost:
swapping only those IDs selects the other applicable row. -/
def reorderedInput : UniverseInput RepairMenu.ceilingPromise where
  entries := [unavailable 10, full 20 4, full 40 2]
  maxEntries := 3

def reorderedScope : CheckedUniverse RepairMenu.ceilingPromise :=
  { entries := reorderedInput.entries
    maxEntries := reorderedInput.maxEntries
    withinBound := by decide
    canonical := by decide }

def reorderedResult : Result reorderedScope := synthesize reorderedScope

theorem authored_order_changes_choice_not_price_order :
    reorderedResult.foundId? = some ⟨20⟩
      ∧ reorderedResult.price? = some
        (RepairMenu.fullCoordinationRepair RepairMenu.ceilingPromise 4).price := by
  decide

/-! ### Exact exhaustive refusal -/

def refusedInput : UniverseInput RepairMenu.ceilingPromise where
  entries := [unavailable 50, unavailable 60]
  maxEntries := 2

def refusedScope : CheckedUniverse RepairMenu.ceilingPromise :=
  { entries := refusedInput.entries
    maxEntries := refusedInput.maxEntries
    withinBound := by decide
    canonical := by decide }

def refusedResult : Result refusedScope := synthesize refusedScope

theorem impossible_rows_refuse : refusedResult.isFound = false := by decide

theorem impossible_refusal_is_exactly_exhaustive :
    ∀ entry : MenuCandidate RepairMenu.ceilingPromise,
      entry ∈ refusedScope.entries → ¬ entry.candidate.applicable :=
  refusedResult.exhaustive_of_isFound_false impossible_rows_refuse

/-- An empty accepted universe refuses vacuously, without claiming that the
promise has no repair outside the empty list. -/
def emptyScope : CheckedUniverse RepairMenu.ceilingPromise where
  entries := []
  maxEntries := 0
  withinBound := by decide
  canonical := by decide

theorem empty_scope_refuses : (synthesize emptyScope).isFound = false := by decide

/-! ### Input bound and canonical-order refusals -/

def tooLargeInput : UniverseInput RepairMenu.ceilingPromise where
  entries := [full 10 1, full 20 2]
  maxEntries := 1

theorem bound_refusal_is_exact :
    (checkUniverse tooLargeInput).refusalKind? = some .tooLarge
      ∧ tooLargeInput.entries.length = 2
      ∧ tooLargeInput.maxEntries = 1
      ∧ tooLargeInput.maxEntries < tooLargeInput.entries.length := by decide

def nonCanonicalInput : UniverseInput RepairMenu.ceilingPromise where
  entries := [full 20 2, full 10 1]
  maxEntries := 2

theorem reversed_ids_are_refused :
    (checkUniverse nonCanonicalInput).refusalKind? =
      some .nonCanonical := by decide

end Examples

end Uwueave.FiniteRepairMenu
