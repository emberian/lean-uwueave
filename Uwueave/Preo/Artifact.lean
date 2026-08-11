/-
# Uwueave.Preo.Artifact — a neutral, first-order export boundary

This module separates two things which must not be confused:

* the **checked source**, indexed by the Lean term that gives it meaning; and
* the **artifact**, a closed first-order projection suitable for an FFI,
  generated file, content-addressed manifest, or downstream adapter.

In particular, an invariant artifact is produced by eliminating a
`Spec.Verdict`.  No function in this module accepts a Boolean or wire verdict
and turns it back into a proof.  A clash exports the codec images of the two
states carried by the verdict; a free verdict exports only the constructor
tag, because its proof is authority rather than wire data.  Likewise a plan
artifact is projected from `Scheduling.Plan`, so its actions come from a
schedule whose coverage obligation Lean already checked.

The decoder below is deliberately only a decoder for the first-order artifact.
It is not a verifier and has no map into `Spec.Verdict`, `FreeTermination`, or
`Scheduling.Plan`.  Downstream code may transport or authenticate the decoded
data, but only the checked constructors in this file can originate semantic
entries.

The shape is intentionally independent of minidregg (and especially of its
unrelated `Loom` proof-system model).  A future minidregg adapter should import
this module, bind these stable IDs into its own manifest, and leave semantic
acceptance on the Lean side of the boundary.
-/
import Uwueave.Preo.Classification
import Uwueave.Evidence
import Uwueave.Scheduling

namespace Uwueave.Preo.Artifact

open Uwueave

set_option autoImplicit false

universe u

/-! ## §1. Stable, non-interchangeable identifiers -/

structure DeclarationId where
  value : Nat
  deriving DecidableEq, Repr

structure FieldId where
  value : Nat
  deriving DecidableEq, Repr

structure InvariantId where
  value : Nat
  deriving DecidableEq, Repr

structure FutureId where
  value : Nat
  deriving DecidableEq, Repr

structure SessionId where
  value : Nat
  deriving DecidableEq, Repr

structure PlanId where
  value : Nat
  deriving DecidableEq, Repr

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

/-! ## §3. First-order semantic artifacts -/

/-- The only two projections of a checked global verdict.  The clash branch
retains its runnable repro; there is intentionally no `Bool` field. -/
inductive VerdictEvidence where
  | free
  | clash (left right : List Nat)
  deriving DecidableEq, Repr

inductive Currency where
  | peerBarrier
  | arbiterCut
  | networkRound
  | userPrompt
  | rollback
  deriving DecidableEq, Repr

def Currency.ofScheduling : Scheduling.Currency → Currency
  | .peerBarrier => .peerBarrier
  | .arbiterCut => .arbiterCut
  | .networkRound => .networkRound
  | .userPrompt => .userPrompt
  | .rollback => .rollback

inductive EvidenceKey where
  | none
  | named (key : Nat)
  deriving DecidableEq, Repr

def EvidenceKey.ofScheduling : Scheduling.EvidenceKey → EvidenceKey
  | .none => .none
  | .named key => .named key

structure DemandArtifact where
  currency : Currency
  participants : List Nat
  scope : Nat
  epoch : Nat
  evidence : EvidenceKey
  round : Nat
  barrier : Nat
  deriving DecidableEq, Repr

def DemandArtifact.ofDemand (demand : Scheduling.Demand) : DemandArtifact where
  currency := Currency.ofScheduling demand.currency
  participants := demand.participants
  scope := demand.scope
  epoch := demand.epoch
  evidence := EvidenceKey.ofScheduling demand.evidence
  round := demand.round
  barrier := demand.barrier

inductive OriginArtifact where
  | crossing (index : Nat)
  | ambient
  deriving DecidableEq, Repr

def OriginArtifact.ofOrigin {crossings : Nat} :
    Scheduling.Origin crossings → OriginArtifact
  | .crossing index => .crossing index.val
  | .ambient => .ambient

structure ObligationArtifact where
  origin : OriginArtifact
  demand : DemandArtifact
  deriving DecidableEq, Repr

def ObligationArtifact.ofObligation {crossings : Nat}
    (obligation : Scheduling.Obligation crossings) : ObligationArtifact where
  origin := OriginArtifact.ofOrigin obligation.origin
  demand := DemandArtifact.ofDemand obligation.demand

structure DeclarationArtifact where
  id : DeclarationId
  stateTypeId : Nat
  schemaVersion : Nat
  deriving DecidableEq, Repr

structure FieldArtifact where
  id : FieldId
  declaration : DeclarationId
  kindId : Nat
  carrierTypeId : Nat
  keyTypeId : Option Nat
  deriving DecidableEq, Repr

structure InvariantArtifact where
  id : InvariantId
  declaration : DeclarationId
  carrierTypeId : Nat
  verdict : VerdictEvidence
  deriving DecidableEq, Repr

structure FutureArtifact where
  id : FutureId
  declaration : DeclarationId
  worldTypeId : Nat
  relationId : Nat
  deriving DecidableEq, Repr

structure SessionArtifact where
  id : SessionId
  declaration : DeclarationId
  crossings : Nat
  obligations : List ObligationArtifact
  deriving DecidableEq, Repr

structure PlanArtifact where
  id : PlanId
  session : SessionId
  actions : List DemandArtifact
  profile : List (Currency × Nat)
  deriving DecidableEq, Repr

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

def CheckedPlan.toArtifact {session : Scheduling.Session}
    {checkedSession : CheckedSession session} {plan : Scheduling.Plan session}
    (checked : CheckedPlan checkedSession plan) : PlanArtifact :=
  ⟨checked.id, checkedSession.id,
    plan.schedule.actions.map DemandArtifact.ofDemand, planProfile plan⟩

/-! ## §4. Bundling is append-only

The transport structure is public data, not proof evidence.  Its builders are
the intended path from checked sources.  In particular, no theorem consumes an
`InvariantArtifact.verdict` as a `Spec.Verdict`.
-/

structure Artifact where
  declaration : DeclarationArtifact
  fields : List FieldArtifact
  invariants : List InvariantArtifact
  futures : List FutureArtifact
  sessions : List SessionArtifact
  plans : List PlanArtifact
  deriving DecidableEq, Repr

def Artifact.ofDeclaration {State : Type u}
    (declaration : CheckedDeclaration State) : Artifact :=
  ⟨declaration.toArtifact, [], [], [], [], []⟩

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

/-! ## §5. Canonical first-order encoding and its left inverse -/

structure DeclarationArtifactEncoding where
  id : Nat
  stateTypeId : Nat
  schemaVersion : Nat
  deriving DecidableEq, Repr

def DeclarationArtifact.canonicalEncoding
    (artifact : DeclarationArtifact) : DeclarationArtifactEncoding :=
  ⟨artifact.id.value, artifact.stateTypeId, artifact.schemaVersion⟩

def DeclarationArtifactEncoding.decode
    (wire : DeclarationArtifactEncoding) : DeclarationArtifact :=
  ⟨⟨wire.id⟩, wire.stateTypeId, wire.schemaVersion⟩

@[simp] theorem DeclarationArtifactEncoding.decode_canonicalEncoding
    (artifact : DeclarationArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure FieldArtifactEncoding where
  id : Nat
  declarationId : Nat
  kindId : Nat
  carrierTypeId : Nat
  keyTypeId : Option Nat
  deriving DecidableEq, Repr

def FieldArtifact.canonicalEncoding (artifact : FieldArtifact) : FieldArtifactEncoding :=
  ⟨artifact.id.value, artifact.declaration.value, artifact.kindId,
    artifact.carrierTypeId, artifact.keyTypeId⟩

def FieldArtifactEncoding.decode (wire : FieldArtifactEncoding) : FieldArtifact :=
  ⟨⟨wire.id⟩, ⟨wire.declarationId⟩, wire.kindId, wire.carrierTypeId, wire.keyTypeId⟩

@[simp] theorem FieldArtifactEncoding.decode_canonicalEncoding
    (artifact : FieldArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure InvariantArtifactEncoding where
  id : Nat
  declarationId : Nat
  carrierTypeId : Nat
  verdict : VerdictEvidence
  deriving DecidableEq, Repr

def InvariantArtifact.canonicalEncoding
    (artifact : InvariantArtifact) : InvariantArtifactEncoding :=
  ⟨artifact.id.value, artifact.declaration.value, artifact.carrierTypeId,
    artifact.verdict⟩

def InvariantArtifactEncoding.decode
    (wire : InvariantArtifactEncoding) : InvariantArtifact :=
  ⟨⟨wire.id⟩, ⟨wire.declarationId⟩, wire.carrierTypeId, wire.verdict⟩

@[simp] theorem InvariantArtifactEncoding.decode_canonicalEncoding
    (artifact : InvariantArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure FutureArtifactEncoding where
  id : Nat
  declarationId : Nat
  worldTypeId : Nat
  relationId : Nat
  deriving DecidableEq, Repr

def FutureArtifact.canonicalEncoding (artifact : FutureArtifact) : FutureArtifactEncoding :=
  ⟨artifact.id.value, artifact.declaration.value, artifact.worldTypeId,
    artifact.relationId⟩

def FutureArtifactEncoding.decode (wire : FutureArtifactEncoding) : FutureArtifact :=
  ⟨⟨wire.id⟩, ⟨wire.declarationId⟩, wire.worldTypeId, wire.relationId⟩

@[simp] theorem FutureArtifactEncoding.decode_canonicalEncoding
    (artifact : FutureArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure SessionArtifactEncoding where
  id : Nat
  declarationId : Nat
  crossings : Nat
  obligations : List ObligationArtifact
  deriving DecidableEq, Repr

def SessionArtifact.canonicalEncoding (artifact : SessionArtifact) : SessionArtifactEncoding :=
  ⟨artifact.id.value, artifact.declaration.value, artifact.crossings,
    artifact.obligations⟩

def SessionArtifactEncoding.decode (wire : SessionArtifactEncoding) : SessionArtifact :=
  ⟨⟨wire.id⟩, ⟨wire.declarationId⟩, wire.crossings, wire.obligations⟩

@[simp] theorem SessionArtifactEncoding.decode_canonicalEncoding
    (artifact : SessionArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure PlanArtifactEncoding where
  id : Nat
  sessionId : Nat
  actions : List DemandArtifact
  profile : List (Currency × Nat)
  deriving DecidableEq, Repr

def PlanArtifact.canonicalEncoding (artifact : PlanArtifact) : PlanArtifactEncoding :=
  ⟨artifact.id.value, artifact.session.value, artifact.actions, artifact.profile⟩

def PlanArtifactEncoding.decode (wire : PlanArtifactEncoding) : PlanArtifact :=
  ⟨⟨wire.id⟩, ⟨wire.sessionId⟩, wire.actions, wire.profile⟩

@[simp] theorem PlanArtifactEncoding.decode_canonicalEncoding
    (artifact : PlanArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure ArtifactEncoding where
  declaration : DeclarationArtifactEncoding
  fields : List FieldArtifactEncoding
  invariants : List InvariantArtifactEncoding
  futures : List FutureArtifactEncoding
  sessions : List SessionArtifactEncoding
  plans : List PlanArtifactEncoding
  deriving DecidableEq, Repr

def Artifact.canonicalEncoding (artifact : Artifact) : ArtifactEncoding where
  declaration := artifact.declaration.canonicalEncoding
  fields := artifact.fields.map FieldArtifact.canonicalEncoding
  invariants := artifact.invariants.map InvariantArtifact.canonicalEncoding
  futures := artifact.futures.map FutureArtifact.canonicalEncoding
  sessions := artifact.sessions.map SessionArtifact.canonicalEncoding
  plans := artifact.plans.map PlanArtifact.canonicalEncoding

def ArtifactEncoding.decode (wire : ArtifactEncoding) : Artifact where
  declaration := wire.declaration.decode
  fields := wire.fields.map FieldArtifactEncoding.decode
  invariants := wire.invariants.map InvariantArtifactEncoding.decode
  futures := wire.futures.map FutureArtifactEncoding.decode
  sessions := wire.sessions.map SessionArtifactEncoding.decode
  plans := wire.plans.map PlanArtifactEncoding.decode

/-- The canonical first-order encoder has a structural left inverse.  This is
transport faithfulness, not semantic acceptance of arbitrary wire data. -/
@[simp] theorem ArtifactEncoding.decode_canonicalEncoding (artifact : Artifact) :
    artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  simp [Artifact.canonicalEncoding, ArtifactEncoding.decode, Function.comp_def]

/-! ## §6. Non-vacuous closed examples -/

namespace Examples

def natCodec : FirstOrderCodec Nat where
  encode value := [value]
  decode
    | [value] => some value
    | _ => none
  decode_encode := by intro value; rfl

def declaration : CheckedDeclaration Nat :=
  CheckedDeclaration.ofState ⟨100⟩ 200 1

def field : CheckedField Nat :=
  CheckedField.ofCarrier declaration ⟨101⟩ 10 200

def always : Invariant Nat := fun _ => True

def alwaysVerdict : Spec.Verdict always :=
  .free (fun _ _ _ _ => trivial)

def invariant : CheckedInvariant always :=
  CheckedInvariant.ofVerdict declaration ⟨102⟩ 200 alwaysVerdict natCodec

def encodeBoolSet (state : Catalog.GSet Bool) : List Nat :=
  [if state false then 1 else 0, if state true then 1 else 0]

def decodeBoolSet : List Nat → Option (Catalog.GSet Bool)
  | [left, right] => some (fun key => if key then right != 0 else left != 0)
  | _ => none

theorem decodeBoolSet_encodeBoolSet (state : Catalog.GSet Bool) :
    decodeBoolSet (encodeBoolSet state) = some state := by
  apply congrArg some
  funext key
  cases key
  · cases h : state false <;> simp_all
  · cases h : state true <;> simp_all

def boolSetCodec : FirstOrderCodec (Catalog.GSet Bool) :=
  ⟨encodeBoolSet, decodeBoolSet, decodeBoolSet_encodeBoolSet⟩

def atMostOneBool : Invariant (Catalog.GSet Bool) :=
  fun state => state false = true → state true = true → False

def leftBool : Catalog.GSet Bool := fun key => key == false

def rightBool : Catalog.GSet Bool := fun key => key == true

def atMostOneBoolVerdict : Spec.Verdict atMostOneBool :=
  .clash leftBool rightBool (by simp [atMostOneBool, leftBool])
    (by simp [atMostOneBool, rightBool]) (by
    intro merged
    exact merged rfl rfl)

def clashingInvariant : CheckedInvariant atMostOneBool :=
  CheckedInvariant.ofVerdict declaration ⟨106⟩ 201 atMostOneBoolVerdict boolSetCodec

def forward : Evidence.Future Nat := fun before after => before ≤ after

def future : CheckedFuture forward :=
  CheckedFuture.ofRelation declaration ⟨103⟩ 200 300

def session : CheckedSession Scheduling.oneCrossingPeerSession :=
  CheckedSession.ofSession declaration ⟨104⟩

def plan : CheckedPlan session Scheduling.oneCrossingPeerPlan :=
  CheckedPlan.ofPlan ⟨105⟩

def bundle : Artifact :=
  ((((((Artifact.ofDeclaration declaration).addField field).addInvariant invariant).addInvariant
    clashingInvariant).addFuture future).addSession session).addPlan plan

/-- All six declaration surfaces are present; this is not an empty-list
roundtrip dressed up as an acceptance test. -/
example : bundle.fields.length = 1
    ∧ bundle.invariants.length = 2
    ∧ bundle.futures.length = 1
    ∧ bundle.sessions.length = 1
    ∧ bundle.plans.length = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Both verdict constructors were eliminated from checked terms, not supplied
to the artifact constructor; the clash retains its two runnable witnesses. -/
example : bundle.invariants.map InvariantArtifact.verdict =
    [.free, .clash [1, 0] [0, 1]] := rfl

/-- The plan export retains the real action and its multi-currency profile. -/
example : bundle.plans.map (fun p => (p.actions.length, p.profile)) =
    [(1, [(.peerBarrier, 1), (.arbiterCut, 0), (.networkRound, 0),
      (.userPrompt, 0), (.rollback, 0)])] := rfl

/-- Whole-bundle canonical roundtrip, with every list nonempty. -/
example : bundle.canonicalEncoding.decode = bundle :=
  ArtifactEncoding.decode_canonicalEncoding bundle

end Examples

end Uwueave.Preo.Artifact
