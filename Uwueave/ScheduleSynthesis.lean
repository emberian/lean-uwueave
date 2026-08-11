/-
# Uwueave.ScheduleSynthesis — finite, proof-carrying schedule search.

`Scheduling` deliberately stopped before schedule search. This module adds the
first bounded rung without pretending that arbitrary schedules are enumerable.
The caller supplies a finite catalog of actual `Scheduling.Plan s` witnesses;
each plan already carries a schedule and its proof that every obligation is
covered. Search checks all five currency coordinates against caller-supplied
limits.

Two result types keep both answers honest:

* `SearchResult.found` carries an actual `ProfileUpperBound` and proof that its
  plan came from the supplied catalog;
* `SearchResult.refused` carries a currency violation for every catalog member.

`selectLeast` additionally chooses the least feasible catalog member under a
caller-supplied `OrderPolicy.scalar`. The scalar ranks plans; it never replaces
the five-currency profile stored in the returned bound. Equal scalar scores are
resolved by catalog order, also caller-controlled. The leastness proof quantifies
over every feasible plan in that exact catalog.

Concrete fixtures exercise:

* two crossings coalescing into one peer meeting;
* one crossing requiring two round-distinct peer meetings;
* pointwise acceptance and refusal, including all five currencies;
* equal crossing counts with opposite search verdicts;
* two explicit policies selecting different full profiles from one catalog.

## Exact boundaries

* ⟨TERMINAL⟩ Refusal is exhaustive only for the supplied finite catalog. It is
  not evidence that no schedule exists, and leastness is catalog-relative.
* ⟨TERMINAL⟩ A scalar is an explicit preference policy, not a semantic collapse.
  Different policies provably select different plans while both results retain
  their pointwise `ProfileUpperBound` evidence.
* ⟨UNDONE⟩ There is no catalog generator. A future generator needs a finite
  action universe and a proved coverage search; neither `Scheduling` nor
  `Protocol` currently supplies arbitrary schedule enumeration.
* ⟨TERMINAL⟩ No unconditional search can be transported from a crossing floor or
  crossing count. `same_crossings_opposite_catalog_verdicts` replays the existing
  obstruction in the executable result: equal crossing counts can accept and
  refuse the same limits. Any restricted transport must declare additional
  hypotheses on the emitted demands.
-/
import Uwueave.Scheduling

namespace Uwueave.ScheduleSynthesis

open Uwueave Uwueave.Scheduling

/-! ## §1. Five-coordinate feasibility and refutation -/

/-- A plan fits all five currency limits. The conjunction makes decidability
explicit; `Fits.pointwise` recovers the function shape required by
`ProfileUpperBound`. -/
def Fits {s : Session} (plan : Plan s) (limits : Currency → Nat) : Prop :=
  plan.profile .peerBarrier ≤ limits .peerBarrier
    ∧ plan.profile .arbiterCut ≤ limits .arbiterCut
    ∧ plan.profile .networkRound ≤ limits .networkRound
    ∧ plan.profile .userPrompt ≤ limits .userPrompt
    ∧ plan.profile .rollback ≤ limits .rollback

instance {s : Session} (plan : Plan s) (limits : Currency → Nat) :
    Decidable (Fits plan limits) := by
  unfold Fits
  infer_instance

/-- The conjunction covers every constructor of the currency type. -/
theorem Fits.pointwise {s : Session} {plan : Plan s} {limits : Currency → Nat}
    (h : Fits plan limits) : ∀ c, plan.profile c ≤ limits c := by
  intro c
  cases c with
  | peerBarrier => exact h.1
  | arbiterCut => exact h.2.1
  | networkRound => exact h.2.2.1
  | userPrompt => exact h.2.2.2.1
  | rollback => exact h.2.2.2.2

/-- Conversely, a pointwise proof supplies the decidable five-field bundle. -/
theorem Fits.ofPointwise {s : Session} {plan : Plan s} {limits : Currency → Nat}
    (h : ∀ c, plan.profile c ≤ limits c) : Fits plan limits :=
  ⟨h .peerBarrier, h .arbiterCut, h .networkRound, h .userPrompt, h .rollback⟩

/-- A concrete reason a plan was rejected: one named currency exceeds its
limit. -/
def Violates {s : Session} (plan : Plan s) (limits : Currency → Nat) : Prop :=
  ∃ c, limits c < plan.profile c

/-- Failure of the five-coordinate check always names an offending currency. -/
theorem violates_of_not_fits {s : Session} {plan : Plan s}
    {limits : Currency → Nat} (h : ¬ Fits plan limits) : Violates plan limits := by
  by_cases hp : plan.profile .peerBarrier ≤ limits .peerBarrier
  · by_cases ha : plan.profile .arbiterCut ≤ limits .arbiterCut
    · by_cases hn : plan.profile .networkRound ≤ limits .networkRound
      · by_cases hu : plan.profile .userPrompt ≤ limits .userPrompt
        · by_cases hr : plan.profile .rollback ≤ limits .rollback
          · exact absurd ⟨hp, ha, hn, hu, hr⟩ h
          · exact ⟨.rollback, by omega⟩
        · exact ⟨.userPrompt, by omega⟩
      · exact ⟨.networkRound, by omega⟩
    · exact ⟨.arbiterCut, by omega⟩
  · exact ⟨.peerBarrier, by omega⟩

/-- A fitting plan cannot carry a violation witness. -/
theorem not_violates_of_fits {s : Session} {plan : Plan s}
    {limits : Currency → Nat} (h : Fits plan limits) : ¬ Violates plan limits := by
  rintro ⟨c, hc⟩
  have hfit := h.pointwise c
  omega

/-- Turn the decidable bundle into Scheduling's public proof-carrying upper
bound. -/
def boundOfFits {s : Session} {plan : Plan s} {limits : Currency → Nat}
    (h : Fits plan limits) : ProfileUpperBound s limits :=
  plan.profileUpperBound limits h.pointwise

/-! ## §2. Exhaustive search of a caller-supplied catalog -/

/-- Convert caller-supplied schedules into plan candidates without discarding
their coverage proofs. -/
def plansOfSchedules {s : Session} (schedules : List (Schedule s)) : List (Plan s) :=
  schedules.map fun schedule => ⟨schedule⟩

/-- The result of finite catalog search. `refused` quantifies only over
`catalog`, visibly in its type. -/
inductive SearchResult (s : Session) (limits : Currency → Nat)
    (catalog : List (Plan s)) where
  /-- A real fitting plan drawn from the catalog. -/
  | found (bound : ProfileUpperBound s limits) (member : bound.plan ∈ catalog)
  /-- Every supplied candidate violates at least one named currency limit. -/
  | refused (exhaustive : ∀ plan ∈ catalog, Violates plan limits)

/-- Whether the proof-carrying result is the found constructor. -/
def SearchResult.isFound {s : Session} {limits : Currency → Nat}
    {catalog : List (Plan s)} : SearchResult s limits catalog → Bool
  | .found _ _ => true
  | .refused _ => false

/-- Observe the full checked bound when one was found. -/
def SearchResult.bound? {s : Session} {limits : Currency → Nat}
    {catalog : List (Plan s)} :
    SearchResult s limits catalog → Option (ProfileUpperBound s limits)
  | .found bound _ => some bound
  | .refused _ => none

/-- A `true` observation can only come from an actual bound whose plan belongs
to the catalog. -/
theorem SearchResult.bound_exists_of_isFound {s : Session}
    {limits : Currency → Nat} {catalog : List (Plan s)}
    (result : SearchResult s limits catalog) (h : result.isFound = true) :
    ∃ bound : ProfileUpperBound s limits, bound.plan ∈ catalog := by
  cases result with
  | found bound member => exact ⟨bound, member⟩
  | refused _ => cases h

/-- A `false` observation exposes exhaustive rejection of the supplied catalog. -/
theorem SearchResult.exhaustive_of_not_isFound {s : Session}
    {limits : Currency → Nat} {catalog : List (Plan s)}
    (result : SearchResult s limits catalog) (h : result.isFound = false) :
    ∀ plan ∈ catalog, Violates plan limits := by
  cases result with
  | found _ _ => cases h
  | refused exhaustive => exact exhaustive

/-- Deterministic first-fit search. The only candidates inspected are the list
constructors supplied by the caller. -/
def searchCatalog {s : Session} (limits : Currency → Nat) :
    (catalog : List (Plan s)) → SearchResult s limits catalog
  | [] => .refused (by intro plan h; cases h)
  | plan :: rest =>
    if hfit : Fits plan limits then
      .found (boundOfFits hfit) List.mem_cons_self
    else
      match searchCatalog limits rest with
      | .found bound member => .found bound (List.mem_cons_of_mem _ member)
      | .refused exhaustive => .refused (by
          intro candidate hmem
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst candidate
            exact violates_of_not_fits hfit
          · exact exhaustive candidate htail)

/-! ## §3. Deterministic least selection under an explicit policy -/

/-- A caller-supplied scalar order policy over the **full** currency profile.
Natural-number order ranks candidates; catalog order breaks equal scores. No
default or canonical policy is declared. -/
structure OrderPolicy where
  scalar : (Currency → Nat) → Nat

/-- The policy score of a plan. The plan's full profile remains available and is
what feasibility checks; this number is used only for ordering. -/
def OrderPolicy.score {s : Session} (policy : OrderPolicy) (plan : Plan s) : Nat :=
  policy.scalar plan.profile

/-- Result of policy-ranked search. The found constructor carries both the
ordinary checked upper bound and a proof of catalog-relative least score. -/
inductive LeastResult (s : Session) (limits : Currency → Nat)
    (policy : OrderPolicy) (catalog : List (Plan s)) where
  | found (bound : ProfileUpperBound s limits) (member : bound.plan ∈ catalog)
      (least : ∀ plan ∈ catalog, Fits plan limits →
        policy.score bound.plan ≤ policy.score plan)
  | refused (exhaustive : ∀ plan ∈ catalog, Violates plan limits)

def LeastResult.isFound {s : Session} {limits : Currency → Nat}
    {policy : OrderPolicy} {catalog : List (Plan s)} :
    LeastResult s limits policy catalog → Bool
  | .found _ _ _ => true
  | .refused _ => false

/-- Observe one coordinate of the selected plan without hiding the full bound
stored in the result. -/
def LeastResult.selectedCoordinate? {s : Session} {limits : Currency → Nat}
    {policy : OrderPolicy} {catalog : List (Plan s)}
    (result : LeastResult s limits policy catalog) (currency : Currency) : Option Nat :=
  match result with
  | .found bound _ _ => some (bound.plan.profile currency)
  | .refused _ => none

/-- Deterministic least feasible candidate. Scores are compared by `Nat`; on a
tie the earlier catalog member wins because the head is chosen on `≤`. -/
def selectLeast {s : Session} (policy : OrderPolicy) (limits : Currency → Nat) :
    (catalog : List (Plan s)) → LeastResult s limits policy catalog
  | [] => .refused (by intro plan h; cases h)
  | plan :: rest =>
    if hfit : Fits plan limits then
      match selectLeast policy limits rest with
      | .refused exhaustive => .found (boundOfFits hfit) List.mem_cons_self (by
          intro candidate hmem candidateFits
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst candidate
            exact Nat.le_refl _
          · exact False.elim
              ((not_violates_of_fits candidateFits) (exhaustive candidate htail)))
      | .found tailBound tailMember tailLeast =>
          if hscore : policy.score plan ≤ policy.score tailBound.plan then
            .found (boundOfFits hfit) List.mem_cons_self (by
              intro candidate hmem candidateFits
              rcases List.mem_cons.mp hmem with hhead | htail
              · subst candidate
                exact Nat.le_refl _
              · exact Nat.le_trans hscore (tailLeast candidate htail candidateFits))
          else
            .found tailBound (List.mem_cons_of_mem _ tailMember) (by
              intro candidate hmem candidateFits
              rcases List.mem_cons.mp hmem with hhead | htail
              · subst candidate
                exact Nat.le_of_lt (Nat.lt_of_not_ge hscore)
              · exact tailLeast candidate htail candidateFits)
    else
      match selectLeast policy limits rest with
      | .found bound member least => .found bound (List.mem_cons_of_mem _ member) (by
          intro candidate hmem candidateFits
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst candidate
            exact False.elim (hfit candidateFits)
          · exact least candidate htail candidateFits)
      | .refused exhaustive => .refused (by
          intro candidate hmem
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst candidate
            exact violates_of_not_fits hfit
          · exact exhaustive candidate htail)

/-! ## §4. Executed fixtures -/

def coalescingCatalog : List (Plan coalescingSession) := [coalescedPlan]

def twoRoundCatalog : List (Plan twoRoundSession) := [twoRoundPlan]

def allCurrenciesCatalog : List (Plan allCurrenciesSession) := [allCurrenciesPlan]

def emptyCatalog : List (Plan emptySession) := [emptyPlan]

def ambientCatalog : List (Plan ambientBarrierSession) := [ambientPlan]

/-- Two crossings coalesce into one meeting, and bounded search accepts the real
one-action plan under the full peer-only profile. -/
theorem coalescing_catalog_accepts :
    (searchCatalog peerOnlyLimits coalescingCatalog).isFound = true := by
  decide

/-- Tightening only the peer coordinate to zero exhaustively rejects that same
catalog. -/
theorem coalescing_catalog_refuses_zero :
    (searchCatalog zeroLimits coalescingCatalog).isFound = false := by
  decide

/-- One crossing with two incompatible round tags accepts at peer limit two. -/
theorem two_round_catalog_accepts_two :
    (searchCatalog twoPeerLimits twoRoundCatalog).isFound = true := by
  decide

/-- The same one-crossing catalog is exhaustively rejected at peer limit one. -/
theorem two_round_catalog_refuses_one :
    (searchCatalog peerOnlyLimits twoRoundCatalog).isFound = false := by
  decide

/-- The pointwise checker exercises all five coordinates: one allowance in each
accepts the five-action plan, while the peer-only allowance rejects it. -/
theorem all_currency_pointwise_accept_refuse :
    (searchCatalog oneEachLimits allCurrenciesCatalog).isFound = true
      ∧ (searchCatalog peerOnlyLimits allCurrenciesCatalog).isFound = false := by
  decide

/-- **Crossing count alone still cannot decide.** Both sessions have zero
crossings and singleton catalogs. The empty plan fits zero in every currency;
the ambient peer-barrier plan is exhaustively rejected. -/
theorem same_crossings_opposite_catalog_verdicts :
    emptySession.crossings = ambientBarrierSession.crossings
      ∧ (searchCatalog zeroLimits emptyCatalog).isFound = true
      ∧ (searchCatalog zeroLimits ambientCatalog).isFound = false := by
  decide

/-! ### Policy dependence, with the full profiles retained -/

/-- A deliberately redundant peer action is a valid plan for the empty session:
coverage is vacuous, but its price remains visible. -/
def extraPeerPlan : Plan emptySession where
  schedule := {
    actions := [sharedDemand]
    covers := by intro obligation h; cases h }

/-- The corresponding redundant network action. -/
def extraNetworkPlan : Plan emptySession where
  schedule := {
    actions := [networkDemand]
    covers := by intro obligation h; cases h }

def policyCatalog : List (Plan emptySession) := [extraPeerPlan, extraNetworkPlan]

/-- Minimize the peer coordinate; other coordinates remain in the result. -/
def fewerPeerPolicy : OrderPolicy where
  scalar profile := profile .peerBarrier

/-- Minimize the network coordinate instead. -/
def fewerNetworkPolicy : OrderPolicy where
  scalar profile := profile .networkRound

/-- Both policies search the same feasible catalog and limits, yet select
different full profiles. The peer policy chooses `(peer=0, network=1)`; the
network policy chooses `(peer=1, network=0)`. This is why policy is an explicit
input and why the selected scalar never replaces `ProfileUpperBound`. -/
theorem selection_is_policy_dependent :
    (selectLeast fewerPeerPolicy oneEachLimits policyCatalog).selectedCoordinate?
        .peerBarrier = some 0
      ∧ (selectLeast fewerPeerPolicy oneEachLimits policyCatalog).selectedCoordinate?
        .networkRound = some 1
      ∧ (selectLeast fewerNetworkPolicy oneEachLimits policyCatalog).selectedCoordinate?
        .peerBarrier = some 1
      ∧ (selectLeast fewerNetworkPolicy oneEachLimits policyCatalog).selectedCoordinate?
        .networkRound = some 0 := by
  decide

end Uwueave.ScheduleSynthesis
