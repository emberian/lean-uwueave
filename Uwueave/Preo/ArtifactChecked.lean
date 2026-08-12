/-
# Uwueave.Preo.ArtifactChecked — proof-indexed artifact origins

This module owns the one-way bridge from checked declarations, verdicts,
futures, sessions, plans, and witnessed five-currency budgets to the neutral
data in ArtifactData. No decoded first-order value is promoted back to proof
authority.
-/
import Uwueave.Preo.ArtifactData
import Uwueave.Preo.Classification
import Uwueave.Evidence
import Uwueave.Scheduling

namespace Uwueave.Preo.Artifact

open Uwueave

set_option autoImplicit false

universe u

/-! ## §2. Checked sources

The constructors are private.  Public creation functions require the actual
Lean carrier/relation/verdict/session/plan term; there is no checked constructor
whose input is a first-order verdict tag or plan summary.
-/

/-- A codec used only to expose concrete witnesses.  The left inverse makes a
wire witness unambiguous; it does not make arbitrary decoded artifacts proofs. -/
structure FirstOrderCodec (α : Type u) where
  encode : α → List Nat
  decode : List Nat → Option α
  decode_encode : ∀ value, decode (encode value) = some value

/-- A checked declaration is indexed by the state type Lean elaborated. -/
structure CheckedDeclaration (State : Type u) where private mk ::
  id : DeclarationId
  stateTypeId : Nat
  schemaVersion : Nat

def CheckedDeclaration.ofState {State : Type u} (id : DeclarationId)
    (stateTypeId schemaVersion : Nat) : CheckedDeclaration State :=
  ⟨id, stateTypeId, schemaVersion⟩

/-- A checked field is indexed by its real carrier.  `keyTypeId = none` is an
ordinary field; `some k` records the stable type ID of a `per` key. -/
structure CheckedField (Carrier : Type u) where private mk ::
  id : FieldId
  declaration : DeclarationId
  kindId : Nat
  carrierTypeId : Nat
  keyTypeId : Option Nat

def CheckedField.ofCarrier {State Carrier : Type u}
    (declaration : CheckedDeclaration State) (id : FieldId)
    (kindId carrierTypeId : Nat) (keyTypeId : Option Nat := none) :
    CheckedField Carrier :=
  ⟨id, declaration.id, kindId, carrierTypeId, keyTypeId⟩

/-- The checked invariant source.  Its verdict and witness codec are retained
until projection; no report string and no separately supplied answer exists. -/
structure CheckedInvariant {S : Type u} [MergeState S] (I : Invariant S)
    where private mk ::
  id : InvariantId
  declaration : DeclarationId
  carrierTypeId : Nat
  verdict : Spec.Verdict I
  codec : FirstOrderCodec S

def CheckedInvariant.ofVerdict {State S : Type u} [MergeState S]
    {I : Invariant S} (declaration : CheckedDeclaration State)
    (id : InvariantId) (carrierTypeId : Nat) (verdict : Spec.Verdict I)
    (codec : FirstOrderCodec S) : CheckedInvariant I :=
  ⟨id, declaration.id, carrierTypeId, verdict, codec⟩

/-- A checked future is indexed by the world type and future relation.  The
relation itself never crosses the first-order boundary; `relationId` is the
stable manifest identity downstream code binds to it. -/
structure CheckedFuture {W : Type} (F : Evidence.Future W) where private mk ::
  id : FutureId
  declaration : DeclarationId
  worldTypeId : Nat
  relationId : Nat

def CheckedFuture.ofRelation {State : Type u} {W : Type} {F : Evidence.Future W}
    (declaration : CheckedDeclaration State) (id : FutureId)
    (worldTypeId relationId : Nat) : CheckedFuture F :=
  ⟨id, declaration.id, worldTypeId, relationId⟩

/-- A checked scheduling session is indexed by the actual dependent `Session`
value, including its crossing-bounded origins. -/
structure CheckedSession (session : Scheduling.Session) where private mk ::
  id : SessionId
  declaration : DeclarationId

def CheckedSession.ofSession {State : Type u} {session : Scheduling.Session}
    (declaration : CheckedDeclaration State) (id : SessionId) :
    CheckedSession session :=
  ⟨id, declaration.id⟩

/-- A checked plan is indexed by an exhibited `Scheduling.Plan`; the latter's
schedule carries the proof that every session obligation is covered. -/
structure CheckedPlan {session : Scheduling.Session}
    (checkedSession : CheckedSession session) (plan : Scheduling.Plan session)
    where private mk ::
  id : PlanId

def CheckedPlan.ofPlan {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    (id : PlanId) : CheckedPlan checkedSession plan :=
  ⟨id⟩

/-- A checked five-currency budget is tied to both the checked session and the
exact checked plan whose realized profile it bounds. The only public
constructor consumes an actual `Scheduling.ProfileUpperBound`; neither
crossings nor a peer-meeting floor can substitute for that witness. -/
structure CheckedBudget {session : Scheduling.Session}
    (checkedSession : CheckedSession session) (plan : Scheduling.Plan session)
    (limits : Scheduling.Currency → Nat) where private mk ::
  id : BudgetId
  planId : PlanId
  bound : Scheduling.ProfileUpperBound session limits
  samePlan : bound.plan = plan

def CheckedBudget.ofProfileUpperBound {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    (checkedPlan : CheckedPlan checkedSession plan)
    {limits : Scheduling.Currency → Nat}
    (bound : Scheduling.ProfileUpperBound session limits)
    (samePlan : bound.plan = plan) (id : BudgetId) :
    CheckedBudget checkedSession plan limits :=
  ⟨id, checkedPlan.id, bound, samePlan⟩

/-- The semantic acceptance retained by a checked budget is pointwise over the
exact plan named by its checked plan, not merely over some schedule. -/
theorem CheckedBudget.realized_fits {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    {limits : Scheduling.Currency → Nat}
    (checked : CheckedBudget checkedSession plan limits)
    (currency : Scheduling.Currency) : plan.profile currency ≤ limits currency := by
  rw [← checked.samePlan]
  exact checked.bound.fits currency

/-- Every checked budget exposes the actual profile-bound witness from which
it was built. Because `CheckedBudget.mk` is private, a crossing count or
`LeastMeetings`/floor fact has no constructor path into this source type. -/
theorem CheckedBudget.has_exact_profile_witness {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    {limits : Scheduling.Currency → Nat}
    (checked : CheckedBudget checkedSession plan limits) :
    ∃ bound : Scheduling.ProfileUpperBound session limits, bound.plan = plan :=
  ⟨checked.bound, checked.samePlan⟩

/-! ## Checked-to-data projections -/

def Currency.ofScheduling : Scheduling.Currency → Currency
  | .peerBarrier => .peerBarrier
  | .arbiterCut => .arbiterCut
  | .networkRound => .networkRound
  | .userPrompt => .userPrompt
  | .rollback => .rollback

def EvidenceKey.ofScheduling : Scheduling.EvidenceKey → EvidenceKey
  | .none => .none
  | .named key => .named key

def DemandArtifact.ofDemand (demand : Scheduling.Demand) : DemandArtifact where
  currency := Currency.ofScheduling demand.currency
  participants := demand.participants
  scope := demand.scope
  epoch := demand.epoch
  evidence := EvidenceKey.ofScheduling demand.evidence
  round := demand.round
  barrier := demand.barrier

def OriginArtifact.ofOrigin {crossings : Nat} :
    Scheduling.Origin crossings → OriginArtifact
  | .crossing index => .crossing index.val
  | .ambient => .ambient

def ObligationArtifact.ofObligation {crossings : Nat}
    (obligation : Scheduling.Obligation crossings) : ObligationArtifact where
  origin := OriginArtifact.ofOrigin obligation.origin
  demand := DemandArtifact.ofDemand obligation.demand

def CheckedDeclaration.toArtifact {State : Type u}
    (checked : CheckedDeclaration State) : DeclarationArtifact :=
  ⟨checked.id, checked.stateTypeId, checked.schemaVersion⟩

def CheckedField.toArtifact {Carrier : Type u}
    (checked : CheckedField Carrier) : FieldArtifact :=
  ⟨checked.id, checked.declaration, checked.kindId, checked.carrierTypeId,
    checked.keyTypeId⟩

def CheckedInvariant.toArtifact {S : Type u} [MergeState S] {I : Invariant S}
    (checked : CheckedInvariant I) : InvariantArtifact :=
  let evidence := match checked.verdict with
    | .free _ => VerdictEvidence.free
    | .clash left right _ _ _ =>
        VerdictEvidence.clash (checked.codec.encode left) (checked.codec.encode right)
  ⟨checked.id, checked.declaration, checked.carrierTypeId, evidence⟩

def CheckedFuture.toArtifact {W : Type} {F : Evidence.Future W}
    (checked : CheckedFuture F) : FutureArtifact :=
  ⟨checked.id, checked.declaration, checked.worldTypeId, checked.relationId⟩

def CheckedSession.toArtifact {session : Scheduling.Session}
    (checked : CheckedSession session) : SessionArtifact :=
  ⟨checked.id, checked.declaration, session.crossings,
    session.obligations.map ObligationArtifact.ofObligation⟩

private def planProfile {session : Scheduling.Session}
    (plan : Scheduling.Plan session) : List (Currency × Nat) :=
  [(.peerBarrier, plan.profile .peerBarrier),
   (.arbiterCut, plan.profile .arbiterCut),
   (.networkRound, plan.profile .networkRound),
   (.userPrompt, plan.profile .userPrompt),
   (.rollback, plan.profile .rollback)]

private def limitsProfile (limits : Scheduling.Currency → Nat) :
    List (Currency × Nat) :=
  [(.peerBarrier, limits .peerBarrier),
   (.arbiterCut, limits .arbiterCut),
   (.networkRound, limits .networkRound),
   (.userPrompt, limits .userPrompt),
   (.rollback, limits .rollback)]

def CheckedPlan.toArtifact {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    (checked : CheckedPlan checkedSession plan) : PlanArtifact :=
  ⟨checked.id, checkedSession.id,
    plan.schedule.actions.map DemandArtifact.ofDemand, planProfile plan⟩

def CheckedBudget.toArtifact {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    {limits : Scheduling.Currency → Nat}
    (checked : CheckedBudget checkedSession plan limits) : BudgetArtifact :=
  ⟨checked.id, checkedSession.id, checked.planId,
    limitsProfile limits, planProfile plan⟩

/-! ## §4. Bundling is append-only

The transport structure is public data, not proof evidence.  Its builders are
the intended path from checked sources.  In particular, no theorem consumes an
`InvariantArtifact.verdict` as a `Spec.Verdict`.
-/


def Artifact.ofDeclaration {State : Type u}
    (declaration : CheckedDeclaration State) : Artifact :=
  ⟨declaration.toArtifact, [], [], [], [], [], []⟩

def Artifact.addField {Carrier : Type u} (artifact : Artifact)
    (field : CheckedField Carrier) : Artifact :=
  { artifact with fields := artifact.fields ++ [field.toArtifact] }

def Artifact.addInvariant {S : Type u} [MergeState S] {I : Invariant S}
    (artifact : Artifact) (invariant : CheckedInvariant I) : Artifact :=
  { artifact with invariants := artifact.invariants ++ [invariant.toArtifact] }

def Artifact.addFuture {W : Type} {F : Evidence.Future W}
    (artifact : Artifact) (future : CheckedFuture F) : Artifact :=
  { artifact with futures := artifact.futures ++ [future.toArtifact] }

def Artifact.addSession {session : Scheduling.Session} (artifact : Artifact)
    (checked : CheckedSession session) : Artifact :=
  { artifact with sessions := artifact.sessions ++ [checked.toArtifact] }

def Artifact.addPlan {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    (artifact : Artifact) (checked : CheckedPlan checkedSession plan) : Artifact :=
  { artifact with plans := artifact.plans ++ [checked.toArtifact] }

def Artifact.addBudget {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    {limits : Scheduling.Currency → Nat} (artifact : Artifact)
    (checked : CheckedBudget checkedSession plan limits) : Artifact :=
  { artifact with budgets := artifact.budgets ++ [checked.toArtifact] }

end Uwueave.Preo.Artifact
