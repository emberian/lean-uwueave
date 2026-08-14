/-
# Uwueave.FiniteProductClosure — a closed finite quota/repair product

This downstream leaf combines the two-replica quota enumerator from
`Preo.Planning` with caller-supplied certified seams and the unconditional fork
and full-coordination repairs.  Its word "complete" is deliberately qualified:
every non-starving partition of the declared `Bool` budget and every certified
seam seed is present in the closed four-constructor grammar.  Nothing here
enumerates arbitrary `Repair` values or puts a canonical scalar order on
`Repair.Price`.

Bounds are checked before a `BoolQuotaSpace`, its partitions, or a repair
catalog is constructed.  Rejection for size is a resource verdict, while a
budget below two is a semantic refusal of this explicitly non-starving quota
grammar.  The two cases are not conflated.
-/
import Uwueave.FiniteProductSearch
import Uwueave.FiniteRepairMenu
import Uwueave.Preo.Planning

namespace Uwueave.FiniteProductClosure

open Uwueave
open Uwueave.Preo.Planning
open Uwueave.Repair (Price Promise)

/-! ## Resource-first admission -/

/-- Raw bounded input.  `maximumBudget` is a resource cap, not a logical
property of quota partitions. -/
structure QuotaInput where
  budget : Nat
  maximumBudget : Nat
  deriving DecidableEq, Repr

/-- An admitted two-replica quota space, retaining the exact raw budget and
the resource bound which admitted it. -/
structure CheckedQuota (input : QuotaInput) where
  space : BoolQuotaSpace
  budgetExact : space.budget = input.budget
  withinBound : input.budget ≤ input.maximumBudget

/-- Resource and semantic refusals are different constructors.  In
particular, `tooLarge` is checked before attempting to prove `2 ≤ budget`. -/
inductive QuotaCheck (input : QuotaInput) where
  | accepted (scope : CheckedQuota input)
  | tooLarge (exceeds : input.maximumBudget < input.budget)
  | noNonStarvingPartition (tooSmall : input.budget < 2)

/-- Check the resource cap before constructing the finite quota space. -/
def checkQuota (input : QuotaInput) : QuotaCheck input :=
  if hbound : input.budget ≤ input.maximumBudget then
    if htwo : 2 ≤ input.budget then
      .accepted {
        space := { budget := input.budget, two_le := htwo }
        budgetExact := rfl
        withinBound := hbound
      }
    else
      .noNonStarvingPartition (by omega)
  else
    .tooLarge (by omega)

/-- Below two total tokens no exact two-site allocation can give both sites a
positive share.  This is the semantic content of the small-budget refusal. -/
theorem no_nonstarving_partition_of_budget_lt_two {budget : Nat}
    (hsmall : budget < 2) (partition : BoolQuotaPartition budget) :
    ¬ (0 < partition.allocation true ∧
      0 < partition.allocation false) := by
  intro hpositive
  have htotal := partition.allocation_total
  omega

namespace QuotaCheck

inductive Kind where
  | accepted
  | tooLarge
  | noNonStarvingPartition
  deriving DecidableEq, Repr

def kind {input : QuotaInput} : QuotaCheck input → Kind
  | .accepted _ => .accepted
  | .tooLarge _ => .tooLarge
  | .noNonStarvingPartition _ => .noNonStarvingPartition

/-- Reading the semantic refusal recovers exhaustion over every exact
two-site partition, not merely failure of one chosen policy. -/
theorem exhaustive_of_noNonStarvingPartition {input : QuotaInput}
    (result : QuotaCheck input)
    (hkind : result.kind = .noNonStarvingPartition) :
    ∀ partition : BoolQuotaPartition input.budget,
      ¬ (0 < partition.allocation true ∧
        0 < partition.allocation false) := by
  cases result with
  | accepted scope => simp [kind] at hkind
  | tooLarge exceeds => simp [kind] at hkind
  | noNonStarvingPartition tooSmall =>
      exact fun partition =>
        no_nonstarving_partition_of_budget_lt_two tooSmall partition

end QuotaCheck

/-! ## The exact non-starving quota axis -/

/-- Every admitted non-starving partition, turned into its actual typed
strengthening repair.  List order is inherited from the exact `0 .. budget`
partition enumeration; filtering does not invent or reorder a partition. -/
def eligibleCandidates (space : BoolQuotaSpace) (idOffset : Nat) :
    List (RepairSynthesis.Candidate (sharedBudgetPromise space.budget)) :=
  space.eligiblePartitions.map (partitionCandidate space idOffset)

/-- Stable IDs remain duplicate-free after retaining only non-starving
partitions. -/
theorem eligibleCandidateIds_nodup (space : BoolQuotaSpace) (idOffset : Nat) :
    ((eligibleCandidates space idOffset).map
      RepairSynthesis.Candidate.id).Nodup := by
  have hfull := partitionCandidateIds_nodup space idOffset
  have hsub :
      ((space.eligiblePartitions.map (partitionCandidate space idOffset)).map
        RepairSynthesis.Candidate.id).Sublist
      ((space.partitions.map (partitionCandidate space idOffset)).map
        RepairSynthesis.Candidate.id) := by
    exact List.Sublist.map
      (fun candidate => candidate.id)
      (List.Sublist.map (partitionCandidate space idOffset) List.filter_sublist)
  exact List.Sublist.nodup hsub hfull

/-- The generated catalog contains exactly the usable quota repairs. -/
def eligibleCatalog (space : BoolQuotaSpace) (idOffset : Nat) :
    RepairSynthesis.Catalog (sharedBudgetPromise space.budget) where
  entries := eligibleCandidates space idOffset
  stableIds := eligibleCandidateIds_nodup space idOffset

/-- The resource-first public catalog boundary.  The catalog occurs only in
the accepted constructor, so reducing `admitCatalog` on either refusal branch
does not enumerate partitions or construct repair candidates. -/
inductive CatalogAdmission (input : QuotaInput) (idOffset : Nat) : Type 2 where
  | ready (scope : CheckedQuota input)
      (catalog : RepairSynthesis.Catalog
        (sharedBudgetPromise scope.space.budget))
      (exact : catalog = eligibleCatalog scope.space idOffset)
  | tooLarge (exceeds : input.maximumBudget < input.budget)
  | noNonStarvingPartition (tooSmall : input.budget < 2)

def admitCatalog (input : QuotaInput) (idOffset : Nat) :
    CatalogAdmission input idOffset :=
  match checkQuota input with
  | .accepted scope => .ready scope (eligibleCatalog scope.space idOffset) rfl
  | .tooLarge exceeds => .tooLarge exceeds
  | .noNonStarvingPartition tooSmall => .noNonStarvingPartition tooSmall

namespace CatalogAdmission

def isReady {input : QuotaInput} {idOffset : Nat} :
    CatalogAdmission input idOffset → Bool
  | .ready .. => true
  | .tooLarge _ => false
  | .noNonStarvingPartition _ => false

def refusalKind? {input : QuotaInput} {idOffset : Nat} :
    CatalogAdmission input idOffset → Option QuotaCheck.Kind
  | .ready .. => none
  | .tooLarge _ => some .tooLarge
  | .noNonStarvingPartition _ => some .noNonStarvingPartition

end CatalogAdmission

/-- Every non-starving partition occurs in the generated catalog. -/
theorem partition_mem_eligibleCatalog (space : BoolQuotaSpace) (idOffset : Nat)
    (partition : BoolQuotaPartition space.budget)
    (h : space.NonStarving partition) :
    partitionCandidate space idOffset partition ∈
      (eligibleCatalog space idOffset).entries := by
  apply List.mem_map.mpr
  exact ⟨partition, (space.mem_eligiblePartitions_iff partition).mpr h, rfl⟩

/-- Conversely, no catalog row is invented: it is definitionally the repair
candidate generated by a non-starving partition. -/
theorem mem_eligibleCatalog_iff (space : BoolQuotaSpace) (idOffset : Nat)
    (candidate : RepairSynthesis.Candidate
      (sharedBudgetPromise space.budget)) :
    candidate ∈ (eligibleCatalog space idOffset).entries ↔
      ∃ partition : BoolQuotaPartition space.budget,
        space.NonStarving partition ∧
        partitionCandidate space idOffset partition = candidate := by
  constructor
  · intro h
    obtain ⟨partition, hmem, rfl⟩ := List.mem_map.mp h
    exact ⟨partition,
      (space.mem_eligiblePartitions_iff partition).mp hmem, rfl⟩
  · rintro ⟨partition, hnonstarving, rfl⟩
    exact partition_mem_eligibleCatalog space idOffset partition hnonstarving

/-- Candidate count is exactly the non-starving partition count. -/
@[simp] theorem eligibleCatalog_length (space : BoolQuotaSpace)
    (idOffset : Nat) :
    (eligibleCatalog space idOffset).entries.length =
      space.eligiblePartitions.length := by
  simp [eligibleCatalog, eligibleCandidates]

/-! ## Caller policy and proof-carrying result -/

/-- Search retains `RepairSynthesis`'s explicit caller valuation.  This layer
does not compare or convert the eight `Price` coordinates itself. -/
def synthesizeCatalog (space : BoolQuotaSpace) (idOffset : Nat)
    (valuation : Price → Nat) :
    RepairSynthesis.Catalog.Result
      (eligibleCatalog space idOffset) valuation :=
  (eligibleCatalog space idOffset).synthesize valuation

/-- The quota-specific policy remains separate from repair-price valuation.
It chooses a least non-starving allocation under the caller's score and keeps
the exact membership/minimality evidence supplied by `Preo.Planning`. -/
def synthesizePartition (space : BoolQuotaSpace)
    (policy : BoolQuotaPolicy space) : PartitionSelection space policy :=
  selectPartition space policy

/-! ## A finite menu presentation, still exact to the quota grammar -/

/-- Menu presentation for a generated quota repair.  The tag is inert display
data; the row's target, relation, and complete price come from the typed repair. -/
def quotaMenuCandidate (space : BoolQuotaSpace) (idOffset : Nat)
    (partition : BoolQuotaPartition space.budget) :
    FiniteRepairMenu.MenuCandidate (sharedBudgetPromise space.budget) where
  candidate := partitionCandidate space idOffset partition
  tag := Exits.Exit.escrow Bool partition.allocation id
  label := "escrow (generated finite partition)"

/-- Exactly the non-starving finite quota menu rows. -/
def eligibleMenuCandidates (space : BoolQuotaSpace) (idOffset : Nat) :
    List (FiniteRepairMenu.MenuCandidate
      (sharedBudgetPromise space.budget)) :=
  space.eligiblePartitions.map (quotaMenuCandidate space idOffset)

theorem mem_eligibleMenuCandidates_iff (space : BoolQuotaSpace)
    (idOffset : Nat)
    (entry : FiniteRepairMenu.MenuCandidate
      (sharedBudgetPromise space.budget)) :
    entry ∈ eligibleMenuCandidates space idOffset ↔
      ∃ partition : BoolQuotaPartition space.budget,
        space.NonStarving partition ∧
        quotaMenuCandidate space idOffset partition = entry := by
  constructor
  · intro h
    obtain ⟨partition, hmem, rfl⟩ := List.mem_map.mp h
    exact ⟨partition,
      (space.mem_eligiblePartitions_iff partition).mp hmem, rfl⟩
  · rintro ⟨partition, hnonstarving, rfl⟩
    apply List.mem_map.mpr
    exact ⟨partition,
      (space.mem_eligiblePartitions_iff partition).mpr hnonstarving, rfl⟩

/-! ## Closed four-way finite repair grammar

The seam lane is explicit proof-carrying input: discovering all functions out
of an arbitrary promise state would be an unrestricted synthesis claim.  The
escrow lane is generated exactly from the finite quota space.  Fork and full
coordination are generated unconditionally.  Thus completeness below is exact
for this declared grammar, never for all inhabitants of `Repair`. -/

inductive CandidateCode (seamCount escrowCount : Nat) where
  | seam (index : Fin seamCount)
  | escrow (index : Fin escrowCount)
  | exposedFork
  | fullCoordination
  deriving DecidableEq, Repr

namespace CandidateCode

theorem nodup_map_of_injective {α β : Type} {values : List α}
    (hnodup : values.Nodup) (f : α → β) (hinjective : Function.Injective f) :
    (values.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (List.nodup_iff_pairwise_ne.mp hnodup).imp fun unequal equal =>
    unequal (hinjective equal)

def values (seamCount escrowCount : Nat) :
    List (CandidateCode seamCount escrowCount) :=
  (List.finRange seamCount).map .seam ++
  (List.finRange escrowCount).map .escrow ++
  [.exposedFork, .fullCoordination]

theorem values_nodup (seamCount escrowCount : Nat) :
    (values seamCount escrowCount).Nodup := by
  have hseam : ((List.finRange seamCount).map
      (CandidateCode.seam : Fin seamCount →
        CandidateCode seamCount escrowCount)).Nodup :=
    nodup_map_of_injective (finRange_nodup seamCount) _ (by
      intro left right equal
      exact CandidateCode.seam.inj equal)
  have hescrow : ((List.finRange escrowCount).map
      (CandidateCode.escrow : Fin escrowCount →
        CandidateCode seamCount escrowCount)).Nodup :=
    nodup_map_of_injective (finRange_nodup escrowCount) _ (by
      intro left right equal
      exact CandidateCode.escrow.inj equal)
  rw [values, List.nodup_append]
  refine ⟨?_, by simp, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hseam, hescrow, by simp⟩
  · intro code hcode
    have hshape : (∃ index, CandidateCode.seam index = code) ∨
        ∃ index, CandidateCode.escrow index = code := by
      simpa using hcode
    rcases hshape with ⟨index, rfl⟩ | ⟨index, rfl⟩ <;> simp

theorem mem_values (code : CandidateCode seamCount escrowCount) :
    code ∈ values seamCount escrowCount := by
  cases code <;> simp [values]

def carrier (seamCount escrowCount : Nat) :
    FiniteProductSearch.Carrier (CandidateCode seamCount escrowCount) where
  values := values seamCount escrowCount
  nodup := values_nodup seamCount escrowCount
  complete := mem_values

def ordinal : CandidateCode seamCount escrowCount → Nat
  | .seam index => index.val
  | .escrow index => seamCount + index.val
  | .exposedFork => seamCount + escrowCount
  | .fullCoordination => seamCount + escrowCount + 1

theorem ordinal_injective :
    Function.Injective (@ordinal seamCount escrowCount) := by
  intro left right equal
  cases left <;> cases right <;>
    simp [ordinal] at equal ⊢ <;> try omega
  all_goals congr; apply Fin.ext; omega

@[simp] theorem values_length (seamCount escrowCount : Nat) :
    (values seamCount escrowCount).length = seamCount + escrowCount + 2 := by
  simp [values, Nat.add_assoc]

end CandidateCode

/-- A seam lane is admitted only with both the segmentation proof and the
clique-derived `SeamFloor` used to construct its typed repair. -/
structure CertifiedSeamSeed (P : Promise) : Type 2 where
  Seg : Type
  sigma : P.State → Seg
  segmented : Segmented.SegmentedIConfluent sigma P.inv
  floor : RepairMenu.SeamFloor P
  label : String

def CertifiedSeamSeed.toMenuCandidate {P : Promise}
    (seed : CertifiedSeamSeed P) (catalogOrdinal : Nat) :
    FiniteRepairMenu.MenuCandidate P where
  candidate := RepairSynthesis.Candidate.ofRepair ⟨catalogOrdinal⟩
    (RepairMenu.seamRepair P seed.Seg seed.sigma seed.segmented seed.floor)
  tag := .seam seed.Seg seed.sigma seed.floor.floor
  label := seed.label

/-- An untrusted seam proposal carries a decision procedure, not a claimed
proof.  Rejected proposals never enter `ClosedScope`. -/
structure SeamProposal (P : Promise) : Type 2 where
  Seg : Type
  sigma : P.State → Seg
  floor : RepairMenu.SeamFloor P
  label : String
  decideSegmented : Decidable
    (Segmented.SegmentedIConfluent sigma P.inv)

inductive SeamCheck (P : Promise) : Type 2 where
  | accepted (seed : CertifiedSeamSeed P)
  | rejected

def checkSeamProposal {P : Promise} (proposal : SeamProposal P) :
    SeamCheck P :=
  letI := proposal.decideSegmented
  if h : Segmented.SegmentedIConfluent proposal.sigma P.inv then
    .accepted {
      Seg := proposal.Seg
      sigma := proposal.sigma
      segmented := h
      floor := proposal.floor
      label := proposal.label
    }
  else
    .rejected

namespace SeamCheck

def isAccepted {P : Promise} : SeamCheck P → Bool
  | .accepted _ => true
  | .rejected => false

end SeamCheck

/-- A closed scope retains the actual resource-admitted quota certificate.
There is no constructor taking a bare `BoolQuotaSpace`. -/
structure ClosedScope where
  input : QuotaInput
  checked : CheckedQuota input
  seams : List (CertifiedSeamSeed
    (sharedBudgetPromise checked.space.budget))
  workloadLength : Nat

def ClosedScope.space (scope : ClosedScope) : BoolQuotaSpace :=
  scope.checked.space

abbrev ClosedScope.Code (scope : ClosedScope) :=
  CandidateCode scope.seams.length scope.space.eligiblePartitions.length

/-- Candidate IDs inside a generated catalog are local ordinals.  They are
unique tie-break keys, not preserved external identities. -/
def assignCatalogOrdinal {P : Promise} (catalogOrdinal : Nat)
    (entry : FiniteRepairMenu.MenuCandidate P) :
    FiniteRepairMenu.MenuCandidate P where
  candidate := {
    id := ⟨catalogOrdinal⟩
    target := entry.candidate.target
    applicable := entry.candidate.applicable
    decideApplicable := entry.candidate.decideApplicable
    discharge := entry.candidate.discharge
    price := entry.candidate.price
    priceAgrees := entry.candidate.priceAgrees
  }
  tag := entry.tag
  label := entry.label

def forkMenuCandidate (P : Promise) (id : Nat) :
    FiniteRepairMenu.MenuCandidate P where
  candidate := RepairSynthesis.Candidate.ofRepair ⟨id⟩
    (RepairMenu.forkRepair P)
  tag := .exposedFork
  label := "exposedFork (generated)"

def fullMenuCandidate (P : Promise) (id workloadLength : Nat) :
    FiniteRepairMenu.MenuCandidate P where
  candidate := RepairSynthesis.Candidate.ofRepair ⟨id⟩
    (RepairMenu.fullCoordinationRepair P workloadLength)
  tag := .fullCoordination workloadLength
  label := "fullCoordination (generated ceiling)"

def ClosedScope.entry (scope : ClosedScope) : scope.Code →
    FiniteRepairMenu.MenuCandidate
      (sharedBudgetPromise scope.space.budget)
  | .seam index => (scope.seams[index]).toMenuCandidate index.val
  | .escrow index =>
      assignCatalogOrdinal (scope.seams.length + index.val)
        (List.get (eligibleMenuCandidates scope.space 0)
          ⟨index.val, by simpa [eligibleMenuCandidates] using index.isLt⟩)
  | .exposedFork =>
      forkMenuCandidate _
        (scope.seams.length + scope.space.eligiblePartitions.length)
  | .fullCoordination =>
      fullMenuCandidate _
        (scope.seams.length + scope.space.eligiblePartitions.length + 1)
        scope.workloadLength

@[simp] theorem ClosedScope.entry_id_value (scope : ClosedScope)
    (code : scope.Code) :
    (scope.entry code).id.value = code.ordinal := by
  cases code <;> simp [ClosedScope.entry,
    assignCatalogOrdinal, CertifiedSeamSeed.toMenuCandidate,
    forkMenuCandidate, fullMenuCandidate, CandidateCode.ordinal,
    FiniteRepairMenu.MenuCandidate.id,
    RepairSynthesis.Candidate.ofRepair]

def ClosedScope.menuEntries (scope : ClosedScope) :
    List (FiniteRepairMenu.MenuCandidate
      (sharedBudgetPromise scope.space.budget)) :=
  (CandidateCode.values _ _).map scope.entry

/-- Every generated row is the interpretation of a grammar code, and every
grammar code occurs.  These are the soundness/completeness boundaries. -/
theorem ClosedScope.mem_menuEntries_iff (scope : ClosedScope) (entry :
    FiniteRepairMenu.MenuCandidate
      (sharedBudgetPromise scope.space.budget)) :
    entry ∈ scope.menuEntries ↔
      ∃ code : scope.Code, scope.entry code = entry := by
  simp [ClosedScope.menuEntries, CandidateCode.mem_values]

theorem ClosedScope.entry_mem_menuEntries (scope : ClosedScope)
    (code : scope.Code) : scope.entry code ∈ scope.menuEntries :=
  (scope.mem_menuEntries_iff _).mpr ⟨code, rfl⟩

theorem ClosedScope.candidateIds_nodup (scope : ClosedScope) :
    ((scope.menuEntries.map fun entry => entry.candidate.id)).Nodup := by
  rw [ClosedScope.menuEntries, List.map_map]
  apply CandidateCode.nodup_map_of_injective
    (CandidateCode.values_nodup scope.seams.length
      scope.space.eligiblePartitions.length)
  intro left right equal
  apply CandidateCode.ordinal_injective
  have valuesEqual := congrArg RepairSynthesis.CandidateId.value equal
  simpa using valuesEqual

def ClosedScope.catalog (scope : ClosedScope) :
    RepairSynthesis.Catalog (sharedBudgetPromise scope.space.budget) where
  entries := scope.menuEntries.map FiniteRepairMenu.MenuCandidate.candidate
  stableIds := by
    simpa only [List.map_map, Function.comp_def] using
      scope.candidateIds_nodup

theorem ClosedScope.mem_catalog_iff (scope : ClosedScope)
    (candidate : RepairSynthesis.Candidate
      (sharedBudgetPromise scope.space.budget)) :
    candidate ∈ scope.catalog.entries ↔
      ∃ code : scope.Code, (scope.entry code).candidate = candidate := by
  constructor
  · intro hmem
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨code, rfl⟩ := (scope.mem_menuEntries_iff entry).mp hentry
    exact ⟨code, rfl⟩
  · rintro ⟨code, rfl⟩
    apply List.mem_map.mpr
    exact ⟨scope.entry code, scope.entry_mem_menuEntries code, rfl⟩

/-- Catalog minimisation filters applicability first and is wholly
caller-valued; no scalarisation of the eight price axes is hidden here. -/
def ClosedScope.synthesizeCatalog (scope : ClosedScope)
    (valuation : Price → Nat) :
    RepairSynthesis.Catalog.Result scope.catalog valuation :=
  scope.catalog.synthesize valuation

/-- A closed-form upper bound computed without enumerating partitions. -/
def ClosedScope.quotaEnumerationBound (scope : ClosedScope) : Nat :=
  scope.space.budget + 1

def ClosedScope.rowEnumerationBound (scope : ClosedScope) : Nat :=
  scope.seams.length + scope.quotaEnumerationBound + 2

/-- Saturating arithmetic reports at most `maximum + 1`, which is sufficient
to distinguish admission from refusal without constructing an enormous product
count. -/
def saturatingAdd (maximum left right : Nat) : Nat :=
  if maximum < left then maximum + 1
  else if maximum - left < right then maximum + 1
  else left + right

def saturatingMul (maximum left right : Nat) : Nat :=
  if left = 0 ∨ right = 0 then 0
  else if maximum / left < right then maximum + 1
  else left * right

def ClosedScope.rowCountAtCap (scope : ClosedScope) (maximum : Nat) : Nat :=
  saturatingAdd maximum
    (saturatingAdd maximum scope.seams.length scope.quotaEnumerationBound) 2

/-- Check a conservative closed-form row bound before materialising eligible
partitions, evaluating applicability, or invoking the caller valuation. -/
def ClosedScope.synthesizeCatalogCapped (scope : ClosedScope)
    (valuation : Price → Nat) (limits : FiniteProductSearch.Limits) :
    FiniteProductSearch.Capped
      (RepairSynthesis.Catalog.Result scope.catalog valuation) :=
  let count := scope.rowCountAtCap limits.maxProducts
  if hcount : count ≤ limits.maxProducts then
    .ready (scope.synthesizeCatalog valuation)
  else
    .tooLarge .products count limits.maxProducts

def ClosedScope.codeAxis (scope : ClosedScope) :
    FiniteProductSearch.Axis scope.Code where
  values := (CandidateCode.values _ _).filter fun code =>
    (scope.entry code).candidate.isApplicable
  Admissible := fun code => (scope.entry code).candidate.applicable
  sound := by
    intro code hmem
    exact (RepairSynthesis.Candidate.isApplicable_eq_true_iff _).mp
      (List.mem_filter.mp hmem).2
  complete := by
    intro code happlicable
    exact List.mem_filter.mpr ⟨CandidateCode.mem_values code,
      (RepairSynthesis.Candidate.isApplicable_eq_true_iff _).mpr happlicable⟩

def ClosedScope.quotaAxis (scope : ClosedScope) :
    FiniteProductSearch.Axis (BoolQuotaPartition scope.space.budget) where
  values := scope.space.eligiblePartitions
  Admissible := scope.space.NonStarving
  sound := by
    intro partition hmem
    exact (scope.space.mem_eligiblePartitions_iff partition).mp hmem
  complete := by
    intro partition hnonstarving
    exact (scope.space.mem_eligiblePartitions_iff partition).mpr hnonstarving

/-- Caller-owned coupling between a repair code and a non-starving quota.
The valuation and quota score are explicit parts of the objective. -/
structure CouplingPolicy (scope : ClosedScope) where
  compatible : scope.Code → BoolQuotaPartition scope.space.budget → Prop
  decideCompatible : ∀ code partition, Decidable (compatible code partition)
  valuation : Price → Nat
  quotaScore : BoolQuotaPartition scope.space.budget → Nat

def ClosedScope.coupledProblem (scope : ClosedScope)
    (policy : CouplingPolicy scope) :
    FiniteProductSearch.ProductProblem scope.Code
      (BoolQuotaPartition scope.space.budget) where
  left := scope.codeAxis
  right := scope.quotaAxis
  compatible := policy.compatible
  decideCompatible := policy.decideCompatible
  score := fun pair =>
    policy.valuation (scope.entry pair.1).candidate.price +
      policy.quotaScore pair.2

/-- The product bound is tested before the Cartesian list is materialised. -/
def ClosedScope.synthesizeCoupledCapped (scope : ClosedScope)
    (policy : CouplingPolicy scope) (limits : FiniteProductSearch.Limits) :
    FiniteProductSearch.Capped
      (FiniteProductSearch.ProductResult (scope.coupledProblem policy)) :=
  let rows := scope.rowCountAtCap limits.maxProducts
  let count := saturatingMul limits.maxProducts rows
    scope.quotaEnumerationBound
  if hcount : count ≤ limits.maxProducts then
    .ready (FiniteProductSearch.synthesizeProduct
      (scope.coupledProblem policy))
  else
    .tooLarge .products count limits.maxProducts

/-- A found coupled row is applicable and therefore constructs the advertised
typed repair; compatibility and quota evidence remain in the same witness. -/
def ClosedScope.usableRepairOfCoupledFound (scope : ClosedScope)
    (policy : CouplingPolicy scope)
    (found : FiniteProductSearch.ProductFound
      (scope.coupledProblem policy)) :
    Sigma fun target : Promise =>
      Uwueave.Repair.Repair
        (sharedBudgetPromise scope.space.budget) target :=
  ⟨(scope.entry found.value.1).candidate.target,
    (scope.entry found.value.1).candidate.repair found.leftAdmissible⟩

/-! ## Executed admission, quota, and catalog fixtures -/

def tooLargeInput : QuotaInput where
  budget := 5
  maximumBudget := 4

def tooSmallInput : QuotaInput where
  budget := 1
  maximumBudget := 4

def fourTokenInput : QuotaInput where
  budget := 4
  maximumBudget := 4

def fourTokenSpace : BoolQuotaSpace where
  budget := 4
  two_le := by decide

theorem resource_refusal_precedes_space_construction :
    (checkQuota tooLargeInput).kind = .tooLarge := by decide

theorem resource_refusal_precedes_catalog_construction :
    (admitCatalog tooLargeInput 100).refusalKind? = some .tooLarge := by
  decide

theorem one_token_has_no_nonstarving_bool_partition :
    (checkQuota tooSmallInput).kind = .noNonStarvingPartition := by decide

theorem one_token_refusal_is_exhaustive :
    ∀ partition : BoolQuotaPartition tooSmallInput.budget,
      ¬ (0 < partition.allocation true ∧
        0 < partition.allocation false) :=
  QuotaCheck.exhaustive_of_noNonStarvingPartition
    (checkQuota tooSmallInput) one_token_has_no_nonstarving_bool_partition

theorem four_token_scope_is_accepted :
    (checkQuota fourTokenInput).kind = .accepted := by decide

theorem four_token_catalog_is_admitted :
    (admitCatalog fourTokenInput 100).isReady = true := by decide

/-- The inherited enumeration really contains all five exact partitions and
only the three interior, non-starving partitions enter the closed catalog. -/
theorem four_token_exact_counts :
    fourTokenSpace.partitions.length = 5
      ∧ fourTokenSpace.eligiblePartitions.length = 3
      ∧ (eligibleCatalog fourTokenSpace 100).entries.length = 3 := by
  decide

/-- The existing balanced caller policy remains the exact `2 + 2` selection. -/
theorem four_token_balanced_selection :
    (synthesizePartition fourTokenSpace
      (balancedPolicy fourTokenSpace)).partition.left.val = 2 := by
  decide

/-- Every generated quota repair is applicable, so this nonempty exact catalog
finds a row under a caller valuation without claiming that the valuation is a
canonical ordering of `Price`. -/
def zeroValuation : Price → Nat := fun _ => 0

def fourTokenCatalogResult :=
  synthesizeCatalog fourTokenSpace 100 zeroValuation

theorem four_token_catalog_finds_a_generated_repair :
    fourTokenCatalogResult.isFound = true := by decide

/-- A load-bearing certified identity seam.  Its zero floor is derived from an
empty clique workload, rather than supplied as a free numeric field. -/
def fourTokenIdentityFloor : RepairMenu.SeamFloor
    (sharedBudgetPromise fourTokenSpace.budget) where
  Op := Unit
  step := fun state _ => state
  start := fun _ => 0
  streams := []
  clique := List.Pairwise.nil

def fourTokenIdentitySeam : CertifiedSeamSeed
    (sharedBudgetPromise fourTokenSpace.budget) where
  Seg := (sharedBudgetPromise fourTokenSpace.budget).State
  sigma := id
  segmented := Exits.identity_seam_segmented _
  floor := fourTokenIdentityFloor
  label := "identity seam (fixture)"

def fourTokenClosedScope : ClosedScope where
  input := fourTokenInput
  checked := {
    space := fourTokenSpace
    budgetExact := rfl
    withinBound := by decide
  }
  seams := [fourTokenIdentitySeam]
  workloadLength := 4

/-- One seam, three exact non-starving escrows, fork, and full coordination. -/
theorem four_constructor_catalog_has_six_rows :
    fourTokenClosedScope.menuEntries.length = 6 := by decide

theorem four_constructor_catalog_local_ordinals_are_unique :
    (fourTokenClosedScope.catalog.entries.map
      RepairSynthesis.Candidate.id).Nodup :=
  fourTokenClosedScope.catalog.stableIds

def fixtureCoupling : CouplingPolicy fourTokenClosedScope where
  compatible := fun _ _ => True
  decideCompatible := fun _ _ => inferInstance
  valuation := zeroValuation
  quotaScore := fun partition =>
    if partition.left.val = 2 then 0 else 1

def fixtureCoupledProblem :=
  fourTokenClosedScope.coupledProblem fixtureCoupling

theorem coupled_product_has_exact_eighteen_candidates :
    fixtureCoupledProblem.candidates.length = 18 := by decide

theorem coupled_product_finds_a_compatible_pair :
    (FiniteProductSearch.synthesizeProduct fixtureCoupledProblem).isFound =
      true := by decide

def fixtureUsableRepairPrice? : Option Price :=
  match result : FiniteProductSearch.synthesizeProduct fixtureCoupledProblem with
  | .found found => some
      (fourTokenClosedScope.usableRepairOfCoupledFound
        fixtureCoupling found).2.price
  | .refused _ => none

theorem coupled_product_exposes_usable_repair :
    fixtureUsableRepairPrice?.isSome = true := by decide

theorem coupled_product_resource_refusal_precedes_enumeration :
    (fourTokenClosedScope.synthesizeCoupledCapped fixtureCoupling
      FiniteProductSearch.tinyLimits).refusalAxis? = some .products := by
  decide

theorem closed_catalog_resource_refusal_precedes_search :
    (fourTokenClosedScope.synthesizeCatalogCapped zeroValuation
      FiniteProductSearch.tinyLimits).refusalAxis? = some .products := by
  decide

/-- A constant projection cannot repair the pin clash, so the proposal checker
rejects it before it can become a certified seam seed. -/
def badConstantCeilingProposal : SeamProposal RepairMenu.ceilingPromise where
  Seg := Unit
  sigma := fun _ => ()
  floor := RepairMenu.ceilingFloor
  label := "uncertified constant seam"
  decideSegmented := isFalse (by
    intro hseg
    have hclash := SeamColoring.pin_clash_graph.1
    exact hclash.2.2 (hseg SeamColoring.pinT SeamColoring.pinF rfl
      hclash.1 hclash.2.1).1)

theorem uncertified_seam_is_rejected :
    (checkSeamProposal badConstantCeilingProposal).isAccepted = false := by
  rfl

/-- Applicability is a semantic filter: a catalog containing only this false
residual has no usable result under any valuation. -/
def inapplicableCanary : RepairSynthesis.Candidate
    (sharedBudgetPromise fourTokenSpace.budget) where
  id := ⟨77⟩
  target := sharedBudgetPromise fourTokenSpace.budget
  applicable := False
  decideApplicable := isFalse id
  discharge := False.elim
  price := Price.free
  priceAgrees := fun h => nomatch h

def inapplicableCatalog : RepairSynthesis.Catalog
    (sharedBudgetPromise fourTokenSpace.budget) where
  entries := [inapplicableCanary]
  stableIds := by simp

theorem inapplicable_candidate_is_not_returned :
    inapplicableCatalog.minimum? zeroValuation = none := by rfl

def hugeBudgetSmallCap : QuotaInput where
  budget := 1_000_000
  maximumBudget := 4

theorem huge_budget_is_rejected_before_partition_materialization :
    (checkQuota hugeBudgetSmallCap).kind = .tooLarge := by decide

theorem huge_budget_catalog_is_rejected_before_partition_materialization :
    (admitCatalog hugeBudgetSmallCap 0).refusalKind? = some .tooLarge := by
  decide

end Uwueave.FiniteProductClosure
