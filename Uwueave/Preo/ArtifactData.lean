/-
# Uwueave.Preo.ArtifactData — minimal neutral first-order artifact data

This leaf contains only stable identifiers, first-order artifact rows, and the
canonical structural projection. It imports no checked semantic judgement,
scheduler, elaborator, diagnostic renderer, or example. Durable byte validation
imports this module so runtime admission cannot accidentally acquire those
layers.
-/
import Init

namespace Uwueave.Preo.Artifact

open Uwueave

set_option autoImplicit false

universe u

/-! ## §1. Stable, non-interchangeable identifiers -/

structure DeclarationId where
  value : Nat
  deriving DecidableEq

structure FieldId where
  value : Nat
  deriving DecidableEq

structure InvariantId where
  value : Nat
  deriving DecidableEq

structure FutureId where
  value : Nat
  deriving DecidableEq

structure SessionId where
  value : Nat
  deriving DecidableEq

structure PlanId where
  value : Nat
  deriving DecidableEq

structure BudgetId where
  value : Nat
  deriving DecidableEq


/-! ## First-order semantic artifacts -/

/-- The only two projections of a checked global verdict.  The clash branch
retains its runnable repro; there is intentionally no `Bool` field. -/
inductive VerdictEvidence where
  | free
  | clash (left right : List Nat)
  deriving DecidableEq

inductive Currency where
  | peerBarrier
  | arbiterCut
  | networkRound
  | userPrompt
  | rollback
  deriving DecidableEq

inductive EvidenceKey where
  | none
  | named (key : Nat)
  deriving DecidableEq

structure DemandArtifact where
  currency : Currency
  participants : List Nat
  scope : Nat
  epoch : Nat
  evidence : EvidenceKey
  round : Nat
  barrier : Nat
  deriving DecidableEq

inductive OriginArtifact where
  | crossing (index : Nat)
  | ambient
  deriving DecidableEq

structure ObligationArtifact where
  origin : OriginArtifact
  demand : DemandArtifact
  deriving DecidableEq

structure DeclarationArtifact where
  id : DeclarationId
  stateTypeId : Nat
  schemaVersion : Nat
  deriving DecidableEq

structure FieldArtifact where
  id : FieldId
  declaration : DeclarationId
  kindId : Nat
  carrierTypeId : Nat
  keyTypeId : Option Nat
  deriving DecidableEq

structure InvariantArtifact where
  id : InvariantId
  declaration : DeclarationId
  carrierTypeId : Nat
  verdict : VerdictEvidence
  deriving DecidableEq

structure FutureArtifact where
  id : FutureId
  declaration : DeclarationId
  worldTypeId : Nat
  relationId : Nat
  deriving DecidableEq

structure SessionArtifact where
  id : SessionId
  declaration : DeclarationId
  crossings : Nat
  obligations : List ObligationArtifact
  deriving DecidableEq

structure PlanArtifact where
  id : PlanId
  session : SessionId
  actions : List DemandArtifact
  profile : List (Currency × Nat)
  deriving DecidableEq

/-- First-order budget data. `limits` are the five promised maxima and
`realizedProfile` is the exact profile of the same checked plan identified by
`plan`. Arbitrary decoded values remain data until V2 validation. -/
structure BudgetArtifact where
  id : BudgetId
  session : SessionId
  plan : PlanId
  limits : List (Currency × Nat)
  realizedProfile : List (Currency × Nat)
  deriving DecidableEq

/-! ## Append-only artifact data -/

structure Artifact where
  declaration : DeclarationArtifact
  fields : List FieldArtifact
  invariants : List InvariantArtifact
  futures : List FutureArtifact
  sessions : List SessionArtifact
  plans : List PlanArtifact
  budgets : List BudgetArtifact
  deriving DecidableEq

/-! ## §5. Canonical first-order encoding and its left inverse -/

structure DeclarationArtifactEncoding where
  id : Nat
  stateTypeId : Nat
  schemaVersion : Nat
  deriving DecidableEq

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
  deriving DecidableEq

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
  deriving DecidableEq

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
  deriving DecidableEq

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
  deriving DecidableEq

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
  deriving DecidableEq

def PlanArtifact.canonicalEncoding (artifact : PlanArtifact) : PlanArtifactEncoding :=
  ⟨artifact.id.value, artifact.session.value, artifact.actions, artifact.profile⟩

def PlanArtifactEncoding.decode (wire : PlanArtifactEncoding) : PlanArtifact :=
  ⟨⟨wire.id⟩, ⟨wire.sessionId⟩, wire.actions, wire.profile⟩

@[simp] theorem PlanArtifactEncoding.decode_canonicalEncoding
    (artifact : PlanArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure BudgetArtifactEncoding where
  id : Nat
  sessionId : Nat
  planId : Nat
  limits : List (Currency × Nat)
  realizedProfile : List (Currency × Nat)
  deriving DecidableEq

def BudgetArtifact.canonicalEncoding
    (artifact : BudgetArtifact) : BudgetArtifactEncoding :=
  ⟨artifact.id.value, artifact.session.value, artifact.plan.value,
    artifact.limits, artifact.realizedProfile⟩

def BudgetArtifactEncoding.decode (wire : BudgetArtifactEncoding) : BudgetArtifact :=
  ⟨⟨wire.id⟩, ⟨wire.sessionId⟩, ⟨wire.planId⟩,
    wire.limits, wire.realizedProfile⟩

@[simp] theorem BudgetArtifactEncoding.decode_canonicalEncoding
    (artifact : BudgetArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  rfl

structure ArtifactEncoding where
  declaration : DeclarationArtifactEncoding
  fields : List FieldArtifactEncoding
  invariants : List InvariantArtifactEncoding
  futures : List FutureArtifactEncoding
  sessions : List SessionArtifactEncoding
  plans : List PlanArtifactEncoding
  budgets : List BudgetArtifactEncoding
  deriving DecidableEq

def Artifact.canonicalEncoding (artifact : Artifact) : ArtifactEncoding where
  declaration := artifact.declaration.canonicalEncoding
  fields := artifact.fields.map FieldArtifact.canonicalEncoding
  invariants := artifact.invariants.map InvariantArtifact.canonicalEncoding
  futures := artifact.futures.map FutureArtifact.canonicalEncoding
  sessions := artifact.sessions.map SessionArtifact.canonicalEncoding
  plans := artifact.plans.map PlanArtifact.canonicalEncoding
  budgets := artifact.budgets.map BudgetArtifact.canonicalEncoding

def ArtifactEncoding.decode (wire : ArtifactEncoding) : Artifact where
  declaration := wire.declaration.decode
  fields := wire.fields.map FieldArtifactEncoding.decode
  invariants := wire.invariants.map InvariantArtifactEncoding.decode
  futures := wire.futures.map FutureArtifactEncoding.decode
  sessions := wire.sessions.map SessionArtifactEncoding.decode
  plans := wire.plans.map PlanArtifactEncoding.decode
  budgets := wire.budgets.map BudgetArtifactEncoding.decode

/-- The canonical first-order encoder has a structural left inverse.  This is
transport faithfulness, not semantic acceptance of arbitrary wire data. -/
@[simp] theorem ArtifactEncoding.decode_canonicalEncoding (artifact : Artifact) :
    artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  simp [Artifact.canonicalEncoding, ArtifactEncoding.decode, Function.comp_def]

end Uwueave.Preo.Artifact
