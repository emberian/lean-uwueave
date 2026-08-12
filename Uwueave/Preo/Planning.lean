/-
# Uwueave.Preo.Planning — finite authored universes become checked plans.

The two bounded engines in `ScheduleSynthesis` and `RepairSynthesis` are useful
only after a caller has assembled their catalogs.  This module supplies the
thin, proof-carrying vocabulary a Preoscript surface can elaborate into:

* an `ActionUniverse` enumerates a bounded set of coordination actions an
  author permits; `generatedPlans` checks every canonical sublist and retains
  exactly the covering schedules;
* a `Problem` keeps that generated schedule scope beside an explicit repair
  catalog, five independent schedule limits, and two explicit ordering
  policies;
* `synthesize` reaches both existing engines and returns either one selected
  schedule bound plus one complete eight-axis repair price, or an exhaustive
  refusal whose theorem names the exact finite scope it exhausted;
* `BoolQuotaSpace` is a genuine bounded escrow generator.  For a two-site
  budget of at least two it enumerates all `B + 1` exact partitions, excludes
  the two starving endpoints from usable escrow selection, and constructs an
  actual strengthening repair for the policy-minimal interior partition.

No coordinate is converted into another.  Schedule feasibility remains the
pointwise five-currency predicate and repair results retain the complete
`Repair.Price`.  The two scalar policies are explicit caller inputs used only
to rank already-valid witnesses, exactly as in the underlying engines.

The scope is deliberately finite and visible.  A schedule refusal ranges over
`ActionUniverse.actionChoices`; a repair refusal ranges over
`RepairSynthesis.Catalog.entries`.  Neither branch claims anything about an
action or repair outside those lists.
-/
import Uwueave.ScheduleSynthesis
import Uwueave.RepairSynthesis
import Uwueave.Preo.ProtocolSurface

namespace Uwueave.Preo.Planning

open Uwueave
open Uwueave.Scheduling
open Uwueave.ScheduleSynthesis
open Uwueave.Repair (Promise Price Repair PromiseRelation)
open Uwueave.RepairSynthesis

/-! ## §1. Generate every canonical action subset over a finite universe -/

/-- All order-preserving sublists of a list.  This is the exact finite search
space used below; its definition is public so a refusal can name its scope
without appealing to an implicit powerset or an unbounded schedule universe. -/
def actionChoices {A : Type} : List A → List (List A)
  | [] => [[]]
  | action :: rest =>
      let tail := actionChoices rest
      tail ++ tail.map (action :: ·)

theorem actionChoices_nil {A : Type} :
    actionChoices ([] : List A) = [[]] := rfl

theorem actionChoices_cons {A : Type} (action : A) (rest : List A) :
    actionChoices (action :: rest) =
      actionChoices rest ++ (actionChoices rest).map (action :: ·) := rfl

/-- Exact characterization: `actionChoices` enumerates every order-preserving
sublist, no more and no less. -/
@[simp] theorem mem_actionChoices_iff_sublist {A : Type} {source choice : List A} :
    choice ∈ actionChoices source ↔ choice.Sublist source := by
  induction source generalizing choice with
  | nil => simp [actionChoices]
  | cons head tail ih =>
      rw [actionChoices_cons, List.mem_append]
      constructor
      · intro h
        rcases h with hskip | htake
        · exact List.Sublist.cons head (ih.mp hskip)
        · obtain ⟨prior, hprior, rfl⟩ := List.mem_map.mp htake
          exact List.Sublist.cons_cons head (ih.mp hprior)
      · intro h
        cases h with
        | cons _ hsub => exact Or.inl (ih.mpr hsub)
        | cons_cons _ hsub =>
            exact Or.inr (List.mem_map.mpr ⟨_, ih.mpr hsub, rfl⟩)

/-- The exact number of candidates is public, making the exponential runtime
cost inspectable before search. -/
@[simp] theorem actionChoices_length {A : Type} (source : List A) :
    (actionChoices source).length = 2 ^ source.length := by
  induction source with
  | nil => simp [actionChoices]
  | cons head tail ih =>
      simp [actionChoices, ih, Nat.pow_succ]
      omega

/-! The recursive equations above are deliberately not global simp rules.
`actionChoices_cons` duplicates its recursive result, so eager simplification
materializes the entire powerset even when a caller asks only a semantic
membership question.  The membership and length theorems are the canonical
normal forms instead.  Fifteen actions is large enough to make the old eager
normal form exceed the default simplifier recursion depth. -/

private def simpRegressionActions : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

private theorem actionChoices_fifteen_empty_mem :
    [] ∈ actionChoices simpRegressionActions := by
  simp [simpRegressionActions]

private theorem actionChoices_fifteen_sublist_mem :
    [2, 4, 8, 14] ∈ actionChoices simpRegressionActions := by
  simp [simpRegressionActions]
  decide

/-- Every generated choice contains only actions from the source scope. -/
theorem mem_of_mem_actionChoice {A : Type} {source choice : List A}
    (hchoice : choice ∈ actionChoices source) :
    ∀ action ∈ choice, action ∈ source := by
  induction source generalizing choice with
  | nil =>
      simp at hchoice
      subst choice
      simp
  | cons head tail ih =>
      rw [actionChoices_cons, List.mem_append] at hchoice
      intro action hmem
      rcases hchoice with htail | hhead
      · exact List.mem_cons_of_mem _ (ih htail action hmem)
      · obtain ⟨prior, hprior, rfl⟩ := List.mem_map.mp hhead
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hprior action hmem)

/-- Stable, explicitly bounded finite action scope.  Duplicate actions add no
expressive power and would make two generated schedules differ only by
occurrence identity, so the author must remove them at this boundary.  The
limit is stated directly in generated-choice units and checked before
materializing `2^n` candidates. -/
structure ActionUniverse where
  actions : List Demand
  unique : actions.Nodup
  maxChoices : Nat
  choicesWithinLimit : 2 ^ actions.length ≤ maxChoices

namespace ActionUniverse

/-- The exact action-list candidates generated from this universe. -/
def choices (scope : ActionUniverse) : List (List Demand) :=
  actionChoices scope.actions

@[simp] theorem choices_length (scope : ActionUniverse) :
    scope.choices.length = 2 ^ scope.actions.length :=
  actionChoices_length scope.actions

/-- A generated choice never smuggles in an action outside the authored
universe. -/
theorem choice_scoped (scope : ActionUniverse) {choice : List Demand}
    (hchoice : choice ∈ scope.choices) :
    ∀ action ∈ choice, action ∈ scope.actions :=
  mem_of_mem_actionChoice hchoice

end ActionUniverse

/-- A runtime-facing checked constructor.  Oversized search spaces and
duplicate action identities are evidence-bearing refusals, not panics or eager
`2^n` allocations. -/
inductive ActionUniverseCheck (actions : List Demand) (maxChoices : Nat) where
  | accepted (scope : ActionUniverse)
      (actionsExact : scope.actions = actions)
      (limitExact : scope.maxChoices = maxChoices)
  | duplicate (notUnique : ¬ actions.Nodup)
  | tooLarge (exceeds : maxChoices < 2 ^ actions.length)

def checkActionUniverse (actions : List Demand) (maxChoices : Nat) :
    ActionUniverseCheck actions maxChoices :=
  if hunique : actions.Nodup then
    if hwithin : 2 ^ actions.length ≤ maxChoices then
      .accepted {
        actions := actions
        unique := hunique
        maxChoices := maxChoices
        choicesWithinLimit := hwithin
      } rfl rfl
    else
      .tooLarge (by omega)
  else
    .duplicate hunique

namespace ActionUniverseCheck

def isAccepted {actions : List Demand} {maxChoices : Nat} :
    ActionUniverseCheck actions maxChoices → Bool
  | .accepted _ _ _ => true
  | .duplicate _ => false
  | .tooLarge _ => false

inductive RefusalKind where
  | duplicate
  | tooLarge
  deriving DecidableEq, Repr

def refusalKind? {actions : List Demand} {maxChoices : Nat} :
    ActionUniverseCheck actions maxChoices → Option RefusalKind
  | .accepted _ _ _ => none
  | .duplicate _ => some .duplicate
  | .tooLarge _ => some .tooLarge

end ActionUniverseCheck

/-- Coverage before it is packaged as a `Schedule`.  It is finite and
decidable because both the session obligations and candidate actions are
lists, and `Scheduling.Compatible` is decidable. -/
def Covers (session : Session) (actions : List Demand) : Prop :=
  ∀ obligation ∈ session.obligations,
    ∃ action ∈ actions, Compatible action obligation.demand

instance (session : Session) (actions : List Demand) :
    Decidable (Covers session actions) := by
  unfold Covers
  unfold Compatible
  infer_instance

/-- Turn one candidate action list into a real plan exactly when its coverage
check succeeds.  There is no unchecked schedule constructor on the success
path. -/
def planOfActions? (session : Session) (actions : List Demand) :
    Option (Plan session) :=
  if h : Covers session actions then
    some { schedule := { actions := actions, covers := h } }
  else
    none

@[simp] theorem planOfActions?_isSome_iff (session : Session)
    (actions : List Demand) :
    (planOfActions? session actions).isSome = true ↔ Covers session actions := by
  simp [planOfActions?]

/-- Every covering sub-universe, now as a list of proof-carrying plans. -/
def generatedPlans (session : Session) (scope : ActionUniverse) :
    List (Plan session) :=
  scope.choices.filterMap (planOfActions? session)

/-- A member of the generated plan catalog came from one of the exact authored
action choices. -/
theorem generatedPlan_has_choice {session : Session}
    {scope : ActionUniverse} {plan : Plan session}
    (hplan : plan ∈ generatedPlans session scope) :
    ∃ actions ∈ scope.choices,
      planOfActions? session actions = some plan := by
  exact List.mem_filterMap.mp hplan

/-- Conversely, every covering action choice occurs as a plan in the generated
catalog.  Proof irrelevance makes the checked coverage witness immaterial. -/
theorem plan_mem_generated {session : Session} {scope : ActionUniverse}
    {actions : List Demand} (hchoice : actions ∈ scope.choices)
    (hcovers : Covers session actions) :
    ({ schedule := { actions := actions, covers := hcovers } } : Plan session) ∈
      generatedPlans session scope := by
  apply List.mem_filterMap.mpr
  refine ⟨actions, hchoice, ?_⟩
  simp [planOfActions?, hcovers]

/-- Generated plan actions are scoped by the authored universe. -/
theorem generatedPlan_actions_scoped {session : Session}
    {scope : ActionUniverse} {plan : Plan session}
    (hplan : plan ∈ generatedPlans session scope) :
    ∀ action ∈ plan.schedule.actions, action ∈ scope.actions := by
  obtain ⟨actions, hchoice, hmade⟩ := generatedPlan_has_choice hplan
  simp only [planOfActions?] at hmade
  split at hmade
  · simp only [Option.some.injEq] at hmade
    subst plan
    exact scope.choice_scoped hchoice
  · contradiction

/-! ## §2. Exact bounded two-site quota synthesis -/

/-- One partition of a two-site budget.  `left` is bounded by construction;
the right share is the exact remainder. -/
structure BoolQuotaPartition (budget : Nat) where
  left : Fin (budget + 1)
  deriving DecidableEq, Repr

namespace BoolQuotaPartition

/-- The local escrow allocation represented by a partition. -/
def allocation {budget : Nat} (partition : BoolQuotaPartition budget) :
    Bool → Nat :=
  fun site => if site then partition.left.val else budget - partition.left.val

theorem left_le {budget : Nat} (partition : BoolQuotaPartition budget) :
    partition.left.val ≤ budget := by
  omega

/-- The generated shares spend the budget exactly; no quota is created or
discarded by the enumerator. -/
theorem allocation_total {budget : Nat} (partition : BoolQuotaPartition budget) :
    partition.allocation true + partition.allocation false = budget := by
  simp [allocation]
  exact Nat.add_sub_of_le partition.left_le

/-- Every local escrow invariant generated by a partition is I-confluent. -/
theorem local_bound_iconfluent {budget : Nat}
    (partition : BoolQuotaPartition budget) :
    IConfluent (S := Catalog.Escrow Bool)
      (fun spent => ∀ site, spent site ≤ partition.allocation site) :=
  Catalog.escrow_local_bound_iconfluent partition.allocation

/-- Local bounds imply the original shared budget. -/
theorem local_implies_shared {budget : Nat}
    (partition : BoolQuotaPartition budget) (spent : Catalog.Escrow Bool)
    (hlocal : ∀ site, spent site ≤ partition.allocation site) :
    spent true + spent false ≤ budget := by
  rw [← partition.allocation_total]
  exact Catalog.escrow_global_bound partition.allocation spent hlocal

end BoolQuotaPartition

/-- The fully enumerated two-site quota search space.  A budget of at least two
is the exact premise needed for an allocation giving both sites positive
capacity.  Endpoint partitions remain visible in `partitions`, but policy
selection below ranges only over non-starving partitions. -/
structure BoolQuotaSpace where
  budget : Nat
  two_le : 2 ≤ budget

namespace BoolQuotaSpace

/-- All `budget + 1` partitions, from all quota on the right through all quota
on the left. -/
def partitions (space : BoolQuotaSpace) :
    List (BoolQuotaPartition space.budget) :=
  (List.finRange (space.budget + 1)).map BoolQuotaPartition.mk

@[simp] theorem partitions_length (space : BoolQuotaSpace) :
    space.partitions.length = space.budget + 1 := by
  simp [partitions]

/-- The enumeration is exhaustive for the precise bounded partition type. -/
theorem mem_partitions (space : BoolQuotaSpace)
    (partition : BoolQuotaPartition space.budget) :
    partition ∈ space.partitions := by
  rcases partition with ⟨left⟩
  exact List.mem_map.mpr ⟨left, List.mem_finRange left, rfl⟩

/-- Both sites receive positive capacity.  This is the load-bearing escrow
availability condition used by `Exits`/`RepairMenu`, made explicit here rather
than silently accepting the starving endpoint partitions. -/
def NonStarving (space : BoolQuotaSpace)
    (partition : BoolQuotaPartition space.budget) : Prop :=
  0 < partition.allocation true ∧ 0 < partition.allocation false

instance (space : BoolQuotaSpace)
    (partition : BoolQuotaPartition space.budget) :
    Decidable (space.NonStarving partition) := by
  unfold NonStarving
  infer_instance

/-- The exact finite policy/search scope for usable two-site escrow. -/
def eligiblePartitions (space : BoolQuotaSpace) :
    List (BoolQuotaPartition space.budget) :=
  space.partitions.filter (fun partition => decide (space.NonStarving partition))

theorem mem_eligiblePartitions_iff (space : BoolQuotaSpace)
    (partition : BoolQuotaPartition space.budget) :
    partition ∈ space.eligiblePartitions ↔ space.NonStarving partition := by
  simp [eligiblePartitions, mem_partitions]

/-- `1 + (B-1)` witnesses that the non-starving search scope is inhabited. -/
def firstInterior (space : BoolQuotaSpace) :
    BoolQuotaPartition space.budget :=
  ⟨⟨1, by have h := space.two_le; omega⟩⟩

theorem firstInterior_nonStarving (space : BoolQuotaSpace) :
    space.NonStarving space.firstInterior := by
  have hbudget := space.two_le
  simp [NonStarving, firstInterior, BoolQuotaPartition.allocation]
  omega

theorem eligiblePartitions_nonempty (space : BoolQuotaSpace) :
    space.eligiblePartitions ≠ [] := by
  intro hempty
  have hmem : space.firstInterior ∈ space.eligiblePartitions :=
    (space.mem_eligiblePartitions_iff space.firstInterior).mpr
      space.firstInterior_nonStarving
  rw [hempty] at hmem
  exact List.not_mem_nil hmem

end BoolQuotaSpace

/-- `List.finRange` is duplicate-free.  Core exposes the range and membership
lemmas but not this packaging theorem, so it is proved once here. -/
theorem finRange_nodup : ∀ n, (List.finRange n).Nodup
  | 0 => by rw [List.finRange_zero]; simp
  | n + 1 => by
      rw [List.finRange_succ]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        obtain ⟨index, _, heq⟩ := List.mem_map.mp hmem
        exact Fin.succ_ne_zero index heq
      · exact List.Pairwise.map Fin.succ
          (fun left right hne heq =>
            hne (Fin.succ_inj.mp heq))
          (finRange_nodup n)

/-- The unpartitioned shared-budget promise used by the generated escrow
repairs. -/
def sharedBudgetPromise (budget : Nat) : Promise where
  State := Catalog.Escrow Bool
  mergeState := inferInstance
  Demand := Bool
  admits := fun spent _ => spent true + spent false < budget
  inv := fun spent => spent true + spent false ≤ budget
  trust := []

/-- The strengthened promise for one exact partition. -/
def partitionedBudgetPromise {budget : Nat}
    (partition : BoolQuotaPartition budget) : Promise where
  State := Catalog.Escrow Bool
  mergeState := inferInstance
  Demand := Bool
  admits := fun spent site => spent site < partition.allocation site
  inv := fun spent => ∀ site, spent site ≤ partition.allocation site
  trust := []

/-- Capacity queries now read the resource that actually governs admission:
the source asks whether the shared pool has room, while the target asks whether
the named site's local share has room. -/
theorem source_admits_iff_shared_room {budget : Nat}
    (spent : Catalog.Escrow Bool) (site : Bool) :
    (sharedBudgetPromise budget).admits spent site ↔
      spent true + spent false < budget := Iff.rfl

theorem target_admits_iff_local_room {budget : Nat}
    (partition : BoolQuotaPartition budget) (spent : Catalog.Escrow Bool)
    (site : Bool) :
    (partitionedBudgetPromise partition).admits spent site ↔
      spent site < partition.allocation site := Iff.rfl

/-- Escrow changes admission from shared room to local room, so those
observation/monotonicity axes are explicitly not claimed preserved. -/
def partitionRelation : PromiseRelation :=
  { PromiseRelation.strengthened with
    singularObservation := false
    shrinkageKept := false }

/-- The real escrow repair derived from a partition.  It spends the
reachability-restriction axis and no seam or meeting currency; the target's
global freedom and the original shared bound are both theorem-backed. -/
def partitionRepair {budget : Nat} (partition : BoolQuotaPartition budget) :
    Repair (sharedBudgetPromise budget) (partitionedBudgetPromise partition) where
  transform := id
  relation := partitionRelation
  price := Repair.restrictionPrice
  discharge := .free partition.local_bound_iconfluent
  entails := by
    intro _ spent hlocal
    exact partition.local_implies_shared spent hlocal
  admitsAll := by simp [partitionRelation, PromiseRelation.strengthened]
  singular := by simp [partitionRelation]
  shrinking := by simp [partitionRelation]
  trustKept := by simp [sharedBudgetPromise, partitionedBudgetPromise]
  premisesCharged := by simp [partitionedBudgetPromise]

/-- A source-legal state excluded by each budget-at-least-two partition. -/
def excludedByPartition (space : BoolQuotaSpace)
    (partition : BoolQuotaPartition space.budget) : Catalog.Escrow Bool :=
  if partition.left.val < space.budget then
    fun site => if site then space.budget else 0
  else
    fun site => if site then 0 else space.budget

/-- Every generated budget-at-least-two escrow repair genuinely restricts
reachability; the charged Boolean is not merely an advertised tag. -/
theorem partitionRepair_restricts (space : BoolQuotaSpace)
    (partition : BoolQuotaPartition space.budget) :
    (partitionRepair partition).RestrictsReachability := by
  refine ⟨excludedByPartition space partition, ?_, ?_⟩
  · unfold excludedByPartition sharedBudgetPromise
    split <;> simp
  · unfold excludedByPartition partitionRepair partitionedBudgetPromise
    split <;> rename_i hleft
    · intro hlocal
      have hbound := hlocal true
      simp [BoolQuotaPartition.allocation] at hbound
      omega
    · intro hlocal
      have heq : partition.left.val = space.budget := by
        have hle := partition.left_le
        omega
      have hbound := hlocal false
      simp [BoolQuotaPartition.allocation, heq] at hbound
      have htwo := space.two_le
      have hpos : 0 < space.budget := by omega
      omega

/-! ### Partition policy is not repair-price scalarization

All partition repairs spend the same kind of `Repair.Price`: reachability is
restricted.  Fairness/location is not a ninth cost currency, so it must not be
smuggled into that record.  A separate policy chooses a non-starving partition
first; only then is the resulting repair handed to `RepairSynthesis`. -/

/-- Caller policy over allocations, separate from every schedule/repair
currency. -/
structure BoolQuotaPolicy (space : BoolQuotaSpace) where
  score : BoolQuotaPartition space.budget → Nat

/-- Proof-carrying least non-starving partition under an explicit policy. -/
structure PartitionSelection (space : BoolQuotaSpace)
    (policy : BoolQuotaPolicy space) where
  partition : BoolQuotaPartition space.budget
  member : partition ∈ space.eligiblePartitions
  nonStarving : space.NonStarving partition
  least : ∀ other ∈ space.eligiblePartitions,
    policy.score partition ≤ policy.score other

/-- Exact bounded partition synthesis. -/
def selectPartition (space : BoolQuotaSpace) (policy : BoolQuotaPolicy space) :
    PartitionSelection space policy :=
  match hmin : SeamColoring.argMin? policy.score space.eligiblePartitions with
  | some partition => {
      partition := partition
      member := SeamColoring.argMin_mem policy.score hmin
      nonStarving :=
        (space.mem_eligiblePartitions_iff partition).mp
          (SeamColoring.argMin_mem policy.score hmin)
      least := fun _ hmem =>
        SeamColoring.argMin_le_of_mem policy.score hmin hmem
    }
  | none => False.elim (by
      have hempty : space.eligiblePartitions = [] :=
        (SeamColoring.argMin_eq_none_iff policy.score
          space.eligiblePartitions).mp hmin
      exact space.eligiblePartitions_nonempty hempty)

/-- Minimize absolute imbalance without converting any coordination or repair
currency. -/
def balancedPolicy (space : BoolQuotaSpace) : BoolQuotaPolicy space where
  score partition :=
    (partition.allocation true - partition.allocation false)
      + (partition.allocation false - partition.allocation true)

/-- Turn one generated partition into an unconditionally applicable repair
candidate with a stable caller-selected ID offset. -/
def partitionCandidate (space : BoolQuotaSpace) (idOffset : Nat)
    (partition : BoolQuotaPartition space.budget) :
    RepairSynthesis.Candidate (sharedBudgetPromise space.budget) :=
  RepairSynthesis.Candidate.ofRepair
    ⟨idOffset + partition.left.val⟩ (partitionRepair partition)

/-- Every bounded partition becomes a genuine repair candidate. -/
def partitionCandidates (space : BoolQuotaSpace) (idOffset : Nat) :
    List (RepairSynthesis.Candidate (sharedBudgetPromise space.budget)) :=
  space.partitions.map (partitionCandidate space idOffset)

@[simp] theorem partitionCandidates_length (space : BoolQuotaSpace)
    (idOffset : Nat) :
    (partitionCandidates space idOffset).length = space.budget + 1 := by
  simp [partitionCandidates]

/-- The generated IDs are distinct because a partition is indexed by its left
share. -/
theorem partitionCandidateIds_nodup (space : BoolQuotaSpace) (idOffset : Nat) :
    ((partitionCandidates space idOffset).map
      RepairSynthesis.Candidate.id).Nodup := by
  have hn :
      ((List.finRange (space.budget + 1)).map
        (fun index =>
          (⟨idOffset + index.val⟩ : RepairSynthesis.CandidateId))).Nodup :=
    List.Pairwise.map
      (R := fun left right : Fin (space.budget + 1) => left ≠ right)
      (S := fun left right : RepairSynthesis.CandidateId => left ≠ right)
      (fun index => (⟨idOffset + index.val⟩ : RepairSynthesis.CandidateId))
      (fun left right hne heq =>
        hne (Fin.ext (Nat.add_left_cancel
          (congrArg RepairSynthesis.CandidateId.value heq))))
      (finRange_nodup (space.budget + 1))
  simpa [partitionCandidates, BoolQuotaSpace.partitions,
    partitionCandidate, RepairSynthesis.Candidate.ofRepair,
    Function.comp_def] using hn

/-- Policy evidence and its derived repair catalog travel together so export or
runtime consumers do not lose the non-starvation and leastness theorems when
they take the catalog projection. -/
structure PartitionCatalogBundle (space : BoolQuotaSpace)
    (policy : BoolQuotaPolicy space) (idOffset : Nat) : Type 2 where
  selection : PartitionSelection space policy
  catalog : RepairSynthesis.Catalog (sharedBudgetPromise space.budget)
  exactEntries : catalog.entries =
    [partitionCandidate space idOffset selection.partition]

/-- Select a least non-starving partition, then build the singleton catalog
that the ordinary repair engine checks. -/
def partitionCatalogBundle (space : BoolQuotaSpace)
    (policy : BoolQuotaPolicy space) (idOffset : Nat) :
    PartitionCatalogBundle space policy idOffset :=
  let selection := selectPartition space policy
  {
    selection := selection
    catalog := {
      entries := [partitionCandidate space idOffset selection.partition]
      stableIds := by simp
    }
    exactEntries := rfl
  }

/-- Compatibility projection for callers that only need the ordinary repair
catalog.  Proof-carrying callers should retain `partitionCatalogBundle`. -/
def partitionCatalog (space : BoolQuotaSpace) (policy : BoolQuotaPolicy space)
    (idOffset : Nat) :
    RepairSynthesis.Catalog (sharedBudgetPromise space.budget) :=
  (partitionCatalogBundle space policy idOffset).catalog

/-- A structural cross-domain contract for a quota-selected row: the plan
really covers the named session and the repair candidate is the exact stable
row chosen for that application.  No meaning is recovered from the numeric ID
and no schedule currency is compared with an escrow token. -/
def SelectedPartitionCompatible {promise : Promise} (session : Session)
    (selectedId : RepairSynthesis.CandidateId)
    (plan : Plan session) (candidate : RepairSynthesis.Candidate promise) : Prop :=
  Covers session plan.schedule.actions ∧ candidate.id = selectedId

/-! ## §3. Universally compatible paired planning -/

/-- The authored inputs for one finite planning run.  The action universe is
expanded by this module; repair entries remain an explicit catalog (which may
itself be obtained from `partitionCatalog`).  `compatible` prevents the two
searches from being presented as related by coincidence: the caller states the
domain coupling and proves the strong universal contract that **every**
feasible schedule is compatible with **every** applicable repair in scope.
This intentionally enables two independent least searches; pair-specific
compatibility would require a different product-space search. -/
structure Problem (promise : Promise) : Type 2 where
  session : Session
  actionUniverse : ActionUniverse
  limits : Currency → Nat
  scheduleOrder : ScheduleSynthesis.OrderPolicy
  repairCatalog : RepairSynthesis.Catalog promise
  repairOrder : RepairSynthesis.Catalog.Valuation
  compatible : Plan session → RepairSynthesis.Candidate promise → Prop
  compatible_of_feasible :
    ∀ plan ∈ generatedPlans session actionUniverse,
      ScheduleSynthesis.Fits plan limits →
      ∀ candidate ∈ repairCatalog.entries, candidate.applicable →
        compatible plan candidate

namespace Problem

variable {promise : Promise}

/-- The exact generated schedule catalog searched for this problem. -/
def scheduleCatalog (problem : Problem promise) : List (Plan problem.session) :=
  generatedPlans problem.session problem.actionUniverse

/-- Reach the existing schedule engine; this is not a parallel reimplementation
of its five-coordinate check. -/
def scheduleResult (problem : Problem promise) :
    ScheduleSynthesis.LeastResult problem.session problem.limits
      problem.scheduleOrder problem.scheduleCatalog :=
  ScheduleSynthesis.selectLeast problem.scheduleOrder problem.limits
    problem.scheduleCatalog

/-- Reach the existing repair engine; the candidate applicability and complete
price coherence proofs remain those of `RepairSynthesis`. -/
def repairResult (problem : Problem promise) :
    RepairSynthesis.Catalog.Result problem.repairCatalog problem.repairOrder :=
  problem.repairCatalog.synthesize problem.repairOrder

end Problem

/-- A successful universally compatible paired selection.  Both leastness theorems are relative to the
two explicit catalogs and both full, non-converted prices remain in the value. -/
structure Selected {promise : Promise} (problem : Problem promise) : Type 2 where
  schedule : ProfileUpperBound problem.session problem.limits
  scheduleMember : schedule.plan ∈ problem.scheduleCatalog
  scheduleLeast : ∀ plan ∈ problem.scheduleCatalog,
    ScheduleSynthesis.Fits plan problem.limits →
      problem.scheduleOrder.score schedule.plan ≤
        problem.scheduleOrder.score plan
  repair : RepairSynthesis.Catalog.Found
    problem.repairCatalog problem.repairOrder
  coupled : problem.compatible schedule.plan repair.candidate

namespace Selected

variable {promise : Promise} {problem : Problem promise}

/-- The exact five-currency profile of the one selected schedule. -/
def scheduleProfile (selected : Selected problem) : Currency → Nat :=
  selected.schedule.plan.profile

/-- The complete eight-axis repair price. -/
def repairPrice (selected : Selected problem) : Price :=
  selected.repair.candidate.price

/-- The selected actual repair agrees with the returned complete price. -/
theorem actualRepair_price (selected : Selected problem) :
    selected.repair.repair.price = selected.repairPrice :=
  selected.repair.repair_price

end Selected

/-- Exhaustive refusal, with the finite scope visible in each constructor.
The repair branch retains the successful schedule so callers can distinguish
"no schedule under these actions" from "schedule exists, no supplied repair". -/
inductive Refusal {promise : Promise} (problem : Problem promise) : Type 2 where
  | schedule
      (exhaustive : ∀ plan ∈ problem.scheduleCatalog,
        ScheduleSynthesis.Violates plan problem.limits)
  | repair
      (schedule : ProfileUpperBound problem.session problem.limits)
      (scheduleMember : schedule.plan ∈ problem.scheduleCatalog)
      (scheduleLeast : ∀ plan ∈ problem.scheduleCatalog,
        ScheduleSynthesis.Fits plan problem.limits →
          problem.scheduleOrder.score schedule.plan ≤
            problem.scheduleOrder.score plan)
      (exhaustive : ∀ candidate : RepairSynthesis.Candidate promise,
        candidate ∈ problem.repairCatalog.entries → ¬ candidate.applicable)

/-- Total paired result under the universal compatibility contract. -/
inductive Result {promise : Promise} (problem : Problem promise) : Type 2 where
  | selected (witness : Selected problem)
  | refused (witness : Refusal problem)

/-- Run the generated schedule catalog through `ScheduleSynthesis`, then the
explicit repair catalog through `RepairSynthesis`. -/
def synthesize {promise : Promise} (problem : Problem promise) : Result problem :=
  match problem.scheduleResult with
  | .refused exhaustive => .refused (.schedule exhaustive)
  | .found bound member least =>
      match problem.repairResult with
      | .found repair => .selected {
          schedule := bound
          scheduleMember := member
          scheduleLeast := least
          repair := repair
          coupled := problem.compatible_of_feasible bound.plan member
            (ScheduleSynthesis.Fits.ofPointwise bound.fits)
            repair.candidate repair.member repair.applies
        }
      | .refused exhaustive => .refused (.repair bound member least exhaustive)

namespace Result

variable {promise : Promise} {problem : Problem promise}

def isSelected : Result problem → Bool
  | .selected _ => true
  | .refused _ => false

/-- A successful Boolean observation recovers both the dependent selected
value and its application coupling theorem. -/
theorem coupled_exists_of_isSelected (result : Result problem)
    (h : result.isSelected = true) :
    ∃ witness : Selected problem,
      result = .selected witness ∧
        problem.compatible witness.schedule.plan witness.repair.candidate := by
  cases result with
  | selected witness => exact ⟨witness, rfl, witness.coupled⟩
  | refused witness => cases h

/-- Observe one named schedule coordinate.  The other four remain stored in the
same selected `ProfileUpperBound`. -/
def selectedCoordinate? (result : Result problem) (currency : Currency) :
    Option Nat :=
  match result with
  | .selected witness => some (witness.scheduleProfile currency)
  | .refused _ => none

/-- Observe the complete repair price; no total or crossing projection is
substituted for it. -/
def selectedPrice? : Result problem → Option Price
  | .selected witness => some witness.repairPrice
  | .refused _ => none

/-- Stable repair candidate identity of the successful paired result. -/
def selectedRepairId? : Result problem → Option RepairSynthesis.CandidateId
  | .selected witness => some witness.repair.candidate.id
  | .refused _ => none

inductive RefusalKind where
  | schedule
  | repair
  deriving DecidableEq, Repr

/-- Exact negative constructor, for host/runtime diagnostics. -/
def refusalKind? : Result problem → Option RefusalKind
  | .selected _ => none
  | .refused (.schedule _) => some .schedule
  | .refused (.repair _ _ _ _) => some .repair

theorem schedule_exhaustive_of_refusalKind (result : Result problem)
    (h : result.refusalKind? = some .schedule) :
    ∀ plan ∈ problem.scheduleCatalog,
      ScheduleSynthesis.Violates plan problem.limits := by
  cases result with
  | selected witness => simp [refusalKind?] at h
  | refused witness =>
      cases witness with
      | schedule exhaustive => exact exhaustive
      | repair _ _ _ _ => simp [refusalKind?] at h

theorem repair_exhaustive_of_refusalKind (result : Result problem)
    (h : result.refusalKind? = some .repair) :
    ∃ bound : ProfileUpperBound problem.session problem.limits,
      bound.plan ∈ problem.scheduleCatalog ∧
      ∀ candidate : RepairSynthesis.Candidate promise,
        candidate ∈ problem.repairCatalog.entries → ¬ candidate.applicable := by
  cases result with
  | selected witness => simp [refusalKind?] at h
  | refused witness =>
      cases witness with
      | schedule _ => simp [refusalKind?] at h
      | repair bound member _ exhaustive =>
          exact ⟨bound, member, exhaustive⟩

/-- Failure always recovers one of the two exact finite exhaustion theorems. -/
theorem refusal_scope (result : Result problem) (h : result.isSelected = false) :
    (∀ plan ∈ problem.scheduleCatalog,
      ScheduleSynthesis.Violates plan problem.limits)
    ∨
    (∃ bound : ProfileUpperBound problem.session problem.limits,
      bound.plan ∈ problem.scheduleCatalog ∧
      ∀ candidate : RepairSynthesis.Candidate promise,
        candidate ∈ problem.repairCatalog.entries → ¬ candidate.applicable) := by
  cases result with
  | selected witness => simp [isSelected] at h
  | refused witness =>
      cases witness with
      | schedule exhaustive => exact Or.inl exhaustive
      | repair bound member _ exhaustive =>
          exact Or.inr ⟨bound, member, exhaustive⟩

end Result

/-! ## §4. Executed acceptance and refusal fixtures -/

namespace Examples

open Uwueave.ScheduleSynthesis

/-- One authored action is enough to cover both compatible coalescing
obligations.  The planner still considers both the empty and singleton choices. -/
def coalescingActions : ActionUniverse where
  actions := [Scheduling.sharedDemand]
  unique := by decide
  maxChoices := 2
  choicesWithinLimit := by decide

def neutralScheduleOrder : ScheduleSynthesis.OrderPolicy where
  scalar := fun _ => 0

def neutralRepairOrder : RepairSynthesis.Catalog.Valuation := fun _ => 0

def fourTokenSpace : BoolQuotaSpace := ⟨4, by decide⟩

def fourTokenSelection :
    PartitionSelection fourTokenSpace (balancedPolicy fourTokenSpace) :=
  selectPartition fourTokenSpace (balancedPolicy fourTokenSpace)

def fourTokenBundle :=
  partitionCatalogBundle fourTokenSpace (balancedPolicy fourTokenSpace) 100

/-- The independent allocation policy selects `2+2`, not a list-order endpoint. -/
theorem four_token_policy_selects_balanced :
    fourTokenSelection.partition.left.val = 2 := by decide

theorem four_token_bundle_selects_balanced :
    fourTokenBundle.selection.partition.left.val = 2 := by decide

/-- The policy witness is usable semantic evidence: the selected partition is
non-starving and its actual repair really excludes a formerly legal state. -/
theorem four_token_selected_partition_is_honest :
    fourTokenSpace.NonStarving fourTokenSelection.partition
      ∧ (partitionRepair fourTokenSelection.partition).RestrictsReachability :=
  ⟨fourTokenSelection.nonStarving,
    partitionRepair_restricts fourTokenSpace fourTokenSelection.partition⟩

/-- Admission follows the selected local share.  With `2+2`, a state that has
spent two on the left still has shared room, but the left site is locally full. -/
theorem balanced_capacity_changes_admission :
    (sharedBudgetPromise fourTokenSpace.budget).admits
        (fun site => if site then 2 else 0) true
      ∧ ¬ (partitionedBudgetPromise fourTokenSelection.partition).admits
        (fun site => if site then 2 else 0) true := by
  constructor
  · change 2 + 0 < 4
    decide
  · intro hadmits
    change 2 < fourTokenSelection.partition.allocation true at hadmits
    have hallocation : fourTokenSelection.partition.allocation true = 2 := by
      simp [BoolQuotaPartition.allocation, four_token_policy_selects_balanced]
    rw [hallocation] at hadmits
    omega

def usableProblem : Problem (sharedBudgetPromise fourTokenSpace.budget) where
  session := Scheduling.coalescingSession
  actionUniverse := coalescingActions
  limits := Scheduling.peerOnlyLimits
  scheduleOrder := neutralScheduleOrder
  repairCatalog := fourTokenBundle.catalog
  repairOrder := neutralRepairOrder
  compatible := SelectedPartitionCompatible Scheduling.coalescingSession ⟨102⟩
  compatible_of_feasible := by
    intro plan _ _ candidate hmember _
    rw [fourTokenBundle.exactEntries] at hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    subst candidate
    constructor
    · exact plan.schedule.covers
    · simp [partitionCandidate, RepairSynthesis.Candidate.ofRepair,
        four_token_bundle_selects_balanced]

def usableResult : Result usableProblem := synthesize usableProblem

/-- The generated catalog is accepted by the existing schedule engine itself. -/
theorem underlying_schedule_engine_found :
    usableProblem.scheduleResult.isFound = true := by decide

/-- The generated quota candidates are searched by the existing repair engine
itself; this observes its stable selected identity before paired packaging. -/
theorem underlying_repair_engine_found :
    usableProblem.repairResult.foundId? = some ⟨102⟩ := by decide

/-- The schedule generator produced an actual one-plan catalog rather than
requiring a hand-authored `Scheduling.Plan`. -/
theorem generated_schedule_catalog_is_singleton :
    usableProblem.scheduleCatalog.length = 1 := by decide

/-- The quota generator enumerates every allocation `0+4` through `4+0` before
filtering endpoints and applying the separate balance policy. -/
theorem generated_repair_catalog_has_all_partitions :
    (partitionCandidates fourTokenSpace 100).length = 5
      ∧ usableProblem.repairCatalog.entries.length = 1 := by decide

/-- The paired call reaches both existing synthesis engines and succeeds. -/
theorem usable_result_selected : usableResult.isSelected = true := by decide

/-- The positive fixture does not use the vacuous `True` contract: the selected
plan covers this exact session and the repair is the exact balanced row. -/
theorem usable_result_carries_structural_coupling :
    ∃ witness : Selected usableProblem,
      usableResult = .selected witness ∧
        SelectedPartitionCompatible Scheduling.coalescingSession ⟨102⟩
          witness.schedule.plan witness.repair.candidate := by
  simpa [usableProblem] using
    usableResult.coupled_exists_of_isSelected usable_result_selected

/-- The complete five-coordinate profile is retained.  In this fixture two
crossing obligations coalesce to one peer action and spend none of the other
four currencies. -/
theorem usable_result_full_schedule_profile :
    usableResult.selectedCoordinate? .peerBarrier = some 1
      ∧ usableResult.selectedCoordinate? .arbiterCut = some 0
      ∧ usableResult.selectedCoordinate? .networkRound = some 0
      ∧ usableResult.selectedCoordinate? .userPrompt = some 0
      ∧ usableResult.selectedCoordinate? .rollback = some 0 := by
  decide

/-- Balanced `2+2` has stable ID `offset + left = 102`. -/
theorem usable_result_repair_id :
    usableResult.selectedRepairId? = some ⟨102⟩ := by decide

/-- The selected repair retains all eight price axes.  It spends only the
reachability-restriction Boolean; no crossing or meeting count was invented. -/
theorem usable_result_full_repair_price :
    usableResult.selectedPrice? = some Repair.restrictionPrice := by decide

/-- Meetings, protocol crossings, and repair seam crossings remain three
different facts.  The fixture has two protocol crossings, coalesces them into
one peer action, and selects an escrow repair with zero seam crossings. -/
theorem no_crossing_meeting_scalar_conversion :
    usableProblem.session.crossings = 2
      ∧ usableResult.selectedCoordinate? .peerBarrier = some 1
      ∧ usableResult.selectedPrice?.map Price.seamCrossings = some 0 := by
  decide

/-! ### Consumption of the native protocol surface

This is the intended seam for a future thin command: the protocol command owns
native syntax and emits `Session`/`Limits`; this module consumes those stable
outputs and owns finite planning. -/

def nativeSurfaceActions : ActionUniverse where
  actions :=
    ProtocolSurface.NativeFixture.Plan.schedule.actions.eraseDups
  unique := by decide
  maxChoices := 8
  choicesWithinLimit := by decide

theorem four_token_bundle_200_selects_balanced :
    (partitionCatalogBundle fourTokenSpace
      (balancedPolicy fourTokenSpace) 200).selection.partition.left.val = 2 := by
  decide

def nativeSurfaceProblem :
    Problem (sharedBudgetPromise fourTokenSpace.budget) where
  session := ProtocolSurface.NativeFixture.Session
  actionUniverse := nativeSurfaceActions
  limits := ProtocolSurface.NativeFixture.Limits
  scheduleOrder := neutralScheduleOrder
  repairCatalog := (partitionCatalogBundle fourTokenSpace
    (balancedPolicy fourTokenSpace) 200).catalog
  repairOrder := neutralRepairOrder
  compatible := SelectedPartitionCompatible
    ProtocolSurface.NativeFixture.Session ⟨202⟩
  compatible_of_feasible := by
    intro plan _ _ candidate hmember _
    rw [(partitionCatalogBundle fourTokenSpace
      (balancedPolicy fourTokenSpace) 200).exactEntries] at hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    subst candidate
    constructor
    · exact plan.schedule.covers
    · simp [partitionCandidate, RepairSynthesis.Candidate.ofRepair,
        four_token_bundle_200_selects_balanced]

def nativeSurfaceResult : Result nativeSurfaceProblem :=
  synthesize nativeSurfaceProblem

/-- Native protocol elaboration feeds the bounded planner without a duplicate
schedule-search declaration in the syntax module. -/
theorem native_protocol_surface_is_plannable :
    nativeSurfaceResult.isSelected = true := by decide

/-- Planning coalesces the duplicate peer demands and duplicate prompt demands
from the native identity plan, while respecting its emitted five limits. -/
theorem native_protocol_surface_selected_profile :
    nativeSurfaceResult.selectedCoordinate? .peerBarrier = some 1
      ∧ nativeSurfaceResult.selectedCoordinate? .arbiterCut = some 0
      ∧ nativeSurfaceResult.selectedCoordinate? .networkRound = some 1
      ∧ nativeSurfaceResult.selectedCoordinate? .userPrompt = some 1
      ∧ nativeSurfaceResult.selectedCoordinate? .rollback = some 0 := by
  decide

/-- The native three-action universe really enumerates all eight canonical
subsets; its one covering subset is not a one-element completeness toy. -/
theorem native_protocol_surface_scope_is_complete :
    nativeSurfaceActions.choices.length = 8
      ∧ nativeSurfaceProblem.scheduleCatalog.length = 1 := by decide

/-- The runtime-facing size check refuses before materializing the eight-way
scope when the deployment allows only four generated choices. -/
def nativeSurfaceTooLarge :=
  checkActionUniverse nativeSurfaceActions.actions 4

theorem native_surface_size_refusal_is_exact :
    nativeSurfaceTooLarge.refusalKind? =
      some ActionUniverseCheck.RefusalKind.tooLarge := by decide

def nativeSurfaceAccepted :=
  checkActionUniverse nativeSurfaceActions.actions 8

theorem native_surface_checked_acceptance_is_exact :
    nativeSurfaceAccepted.isAccepted = true
      ∧ nativeSurfaceAccepted.refusalKind? = none := by decide

def duplicateSurfaceRefusal :=
  checkActionUniverse [Scheduling.sharedDemand, Scheduling.sharedDemand] 4

theorem duplicate_surface_refusal_is_exact :
    duplicateSurfaceRefusal.refusalKind? =
      some ActionUniverseCheck.RefusalKind.duplicate := by decide

/-- Tight schedule limits exhaust the generated action-subset scope. -/
def scheduleRefusalProblem : Problem (sharedBudgetPromise fourTokenSpace.budget) where
  session := usableProblem.session
  actionUniverse := usableProblem.actionUniverse
  limits := Scheduling.zeroLimits
  scheduleOrder := usableProblem.scheduleOrder
  repairCatalog := usableProblem.repairCatalog
  repairOrder := usableProblem.repairOrder
  compatible := fun _ _ => True
  compatible_of_feasible := by simp

def scheduleRefusalResult : Result scheduleRefusalProblem :=
  synthesize scheduleRefusalProblem

theorem generated_schedule_scope_refuses :
    scheduleRefusalResult.refusalKind? = some Result.RefusalKind.schedule := by decide

theorem generated_schedule_scope_not_selected :
    scheduleRefusalResult.isSelected = false := by decide

theorem generated_schedule_refusal_is_exhaustive :
    ∀ plan ∈ scheduleRefusalProblem.scheduleCatalog,
      ScheduleSynthesis.Violates plan scheduleRefusalProblem.limits :=
  scheduleRefusalResult.schedule_exhaustive_of_refusalKind
    generated_schedule_scope_refuses

/-- A nonempty but inapplicable authored row makes the repair-refusal fixture
exercise residual checking rather than only the empty-list base case. -/
def unavailableRepair :
    RepairSynthesis.Candidate (sharedBudgetPromise fourTokenSpace.budget) :=
  RepairSynthesis.Candidate.ofObligation ⟨900⟩
    (RepairMenu.emptyObligation
      (sharedBudgetPromise fourTokenSpace.budget)
      (sharedBudgetPromise fourTokenSpace.budget)
      Price.free PromiseRelation.equivalent)
    (isFalse (fun impossible => impossible))

/-- The explicit repair universe is nonempty, but its only residual is false. -/
def unavailableRepairCatalog :
    RepairSynthesis.Catalog (sharedBudgetPromise fourTokenSpace.budget) where
  entries := [unavailableRepair]
  stableIds := by decide

def repairRefusalProblem : Problem (sharedBudgetPromise fourTokenSpace.budget) where
  session := usableProblem.session
  actionUniverse := usableProblem.actionUniverse
  limits := usableProblem.limits
  scheduleOrder := usableProblem.scheduleOrder
  repairCatalog := unavailableRepairCatalog
  repairOrder := usableProblem.repairOrder
  compatible := fun _ _ => True
  compatible_of_feasible := by simp

def repairRefusalResult : Result repairRefusalProblem :=
  synthesize repairRefusalProblem

theorem generated_repair_scope_refuses :
    repairRefusalResult.refusalKind? = some Result.RefusalKind.repair := by decide

theorem generated_repair_scope_not_selected :
    repairRefusalResult.isSelected = false := by decide

theorem generated_repair_refusal_is_exhaustive :
    ∃ bound : ProfileUpperBound repairRefusalProblem.session
        repairRefusalProblem.limits,
      bound.plan ∈ repairRefusalProblem.scheduleCatalog ∧
      ∀ candidate : RepairSynthesis.Candidate
          (sharedBudgetPromise fourTokenSpace.budget),
        candidate ∈ repairRefusalProblem.repairCatalog.entries →
          ¬ candidate.applicable :=
  repairRefusalResult.repair_exhaustive_of_refusalKind
    generated_repair_scope_refuses

/-- The underlying repair engine itself returns its evidence-bearing refused
branch for the nonempty inapplicable catalog. -/
theorem underlying_repair_engine_refuses :
    repairRefusalProblem.repairResult.isFound = false := by decide

/-- Both negative fixtures expose a theorem over their exact catalogs, not a
global non-existence claim. -/
theorem both_refusals_are_scoped :
    ((∀ plan ∈ scheduleRefusalProblem.scheduleCatalog,
        ScheduleSynthesis.Violates plan scheduleRefusalProblem.limits)
      ∨
      (∃ bound : ProfileUpperBound scheduleRefusalProblem.session
          scheduleRefusalProblem.limits,
        bound.plan ∈ scheduleRefusalProblem.scheduleCatalog ∧
        ∀ candidate : RepairSynthesis.Candidate
            (sharedBudgetPromise fourTokenSpace.budget),
          candidate ∈ scheduleRefusalProblem.repairCatalog.entries →
            ¬ candidate.applicable))
    ∧
    ((∀ plan ∈ repairRefusalProblem.scheduleCatalog,
        ScheduleSynthesis.Violates plan repairRefusalProblem.limits)
      ∨
      (∃ bound : ProfileUpperBound repairRefusalProblem.session
          repairRefusalProblem.limits,
        bound.plan ∈ repairRefusalProblem.scheduleCatalog ∧
        ∀ candidate : RepairSynthesis.Candidate
            (sharedBudgetPromise fourTokenSpace.budget),
          candidate ∈ repairRefusalProblem.repairCatalog.entries →
            ¬ candidate.applicable)) := by
  exact ⟨scheduleRefusalResult.refusal_scope generated_schedule_scope_not_selected,
    repairRefusalResult.refusal_scope generated_repair_scope_not_selected⟩

end Examples

end Uwueave.Preo.Planning
