/-
# Uwueave.AuthenticatedWorldContext — signed typed positions and spent authority

This leaf connects three boundaries without erasing any of them:

* `AuthenticatedAdmission` supplies accepted signed records and the separate
  `WasIssued` fact derived from a caller's `AuthenticIssuer` premise;
* `Preo.DerivedProgram` supplies exact typed value/source/position membership
  under the caller's `SourceAuthenticity`; and
* `WorldContext` supplies a real active grant, causal cut and version base.

Capability use is recorded by a grow-only tombstone set.  A step adds a
step-level set of freshly used grants, so one delivery may account for several
candidates without contradictory per-candidate frame equations.  Consuming a
grant does not claim that no other grant covers the same source.

This module proves no cryptographic hardness statement.  `Accepted` is never
treated as issuance, an ERA event id is never treated as a content hash, and
the deployment-supplied position decoder remains an explicit premise.  Signed
frontier progress is a distinct domain and will be conjoined by a later
constructor from `AuthenticatedFrontier`; a signed position event is not
silently reused as a progress attestation.
-/

import Uwueave.AuthenticatedAdmission
import Uwueave.AuthenticatedFrontier
import Uwueave.WorldContext
import Uwueave.Preo.DerivedProgram

namespace Uwueave.AuthenticatedWorldContext

open Uwueave Uwueave.Catalog

/-! ## 1. Signed and genuinely issued typed-position events -/

/-- Dedicated inner ERA kind for typed-position attribution.  The outer
`Authenticity.Payload.event` domain separates events from grants and moves;
this inner tag separates position attribution from ERA's operational kinds.
Authenticated progress uses a different inner kind. -/
def positionKind : Nat := 5

theorem positionKind_gt_operational : 3 < positionKind := by decide

theorem positionKind_ne_progressKind :
    positionKind ≠ AuthenticatedFrontier.progressKind := by decide

/-- An accepted signed position event that also occurred in the caller's
received trace and exact issuance transcript.  Acceptance and issuance are
intentionally separate fields. -/
structure IssuedPositionEvent
    (scheme : Authenticity.SignatureScheme)
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop) : Type where
  accepted : AuthenticatedAdmission.AcceptedEvent scheme keys keyRevocations
  received_record : received accepted.record
  position_domain : accepted.event.kind = positionKind
  wasIssued : Authenticity.WasIssued issued accepted.record

namespace IssuedPositionEvent

/-- The only generic constructor: `WasIssued` comes from issuer authenticity,
not from successful signature verification. -/
def ofAuthenticIssuer
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    (authentic : Authenticity.AuthenticIssuer scheme keys keyRevocations
      issued received)
    (accepted : AuthenticatedAdmission.AcceptedEvent scheme keys keyRevocations)
    (received_record : received accepted.record)
    (position_domain : accepted.event.kind = positionKind) :
    IssuedPositionEvent scheme keys keyRevocations issued received :=
  ⟨accepted, received_record, position_domain,
    authentic accepted.record received_record accepted.accepted⟩

theorem source_is_signed_issuer
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    (event : IssuedPositionEvent scheme keys keyRevocations issued received) :
    event.accepted.record.issuer = event.accepted.record.issuer := rfl

end IssuedPositionEvent

/-- A deployment decoder for the complete signed event payload.  These are
authored projections, not facts reconstructed from ids or hashes; the claim
below retains their exact equalities to the typed materialization witness. -/
structure PositionCodec (α CausalOp Version : Type) where
  worldOf : Era.Event → Holes.World
  valueOf : Era.Event → α
  positionOf : Era.Event → Preo.Expr.Hole
  originOf : Era.Event → CausalOp
  versionOf : Era.Event → Version

/-- One exact signed typed-position claim.  It retains the candidate world
used by the typed evaluator, the caller-wide source-authenticity witness, and
the equalities binding every decoded field to that same candidate. -/
structure AuthenticatedPositionClaim
    {Γ : Preo.Expr.Schema}
    (program : Preo.DerivedProgram.Program Γ)
    (decoder : Preo.DerivedProgram.WorldDecoder Γ)
    (source : Holes.World → Evidence.Source)
    (Authentic : Holes.World → Evidence.Source → Prop)
    (worlds : GSet Holes.World)
    {CausalOp Version : Type}
    (codec : PositionCodec program.type.denote CausalOp Version)
    {scheme : Authenticity.SignatureScheme}
    (keys : Authenticity.Keyring scheme)
    (keyRevocations : Authenticity.Revocations)
    (issued : Authenticity.Issued)
    (received : Authenticity.SignedRecord scheme → Prop) : Type where
  signed : IssuedPositionEvent scheme keys keyRevocations issued received
  candidate : Evidence.PositionCandidate program.type.denote Preo.Expr.Hole
  world : Holes.World
  sourceAuthenticity : Preo.DerivedProgram.SourceAuthenticity
    worlds source Authentic
  world_present : worlds world = true
  value_exact : program.evalWorld decoder world = candidate.value
  source_exact : source world = candidate.source
  position_exact : candidate.position ∈ program.holes
  decoded_world : codec.worldOf signed.accepted.event = world
  decoded_value : codec.valueOf signed.accepted.event = candidate.value
  decoded_position : codec.positionOf signed.accepted.event = candidate.position
  source_signed : candidate.source = signed.accepted.record.issuer

namespace AuthenticatedPositionClaim

/-- The signed claim enters the existing proof-gated attributed document at
exactly its value/source/position.  The final authenticity conjunct is derived
from the caller's `SourceAuthenticity`, not from the numeric issuer equality. -/
theorem materialized
    {Γ : Preo.Expr.Schema}
    {program : Preo.DerivedProgram.Program Γ}
    {decoder : Preo.DerivedProgram.WorldDecoder Γ}
    {source : Holes.World → Evidence.Source}
    {Authentic : Holes.World → Evidence.Source → Prop}
    {worlds : GSet Holes.World}
    {CausalOp Version : Type}
    {codec : PositionCodec program.type.denote CausalOp Version}
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    (claim : AuthenticatedPositionClaim program decoder source Authentic worlds
      codec keys keyRevocations issued received)
    (obligations certificates : GSet Evidence.Source) :
    program.verifiedAttributedDocument decoder source Authentic obligations
        certificates worlds claim.sourceAuthenticity
        (.position claim.candidate) = true := by
  apply (program.verified_position_iff decoder source Authentic obligations
    certificates worlds claim.sourceAuthenticity claim.candidate).2
  refine ⟨claim.world, claim.world_present, claim.value_exact,
    claim.source_exact, claim.position_exact, ?_⟩
  rw [← claim.source_exact]
  exact claim.sourceAuthenticity.authentic claim.world claim.world_present

end AuthenticatedPositionClaim

/-! ## 2. Grow-only capability-consumption receipts -/

/-- A world context plus the grow-only set of capability tokens already used.
The underlying `Context.outstanding` remains grow-only and is never deleted. -/
structure ConsumedContext (α CausalOp Version HistoryOp : Type)
    (H : CausalReach.FinHistory CausalOp)
    (VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp) where
  base : WorldContext.Context α CausalOp Version HistoryOp H VH
  consumed : Authority.GrantSet

/-- Every tombstone names an actually outstanding grant. -/
def ConsumedWf {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (context : ConsumedContext α CausalOp Version HistoryOp H VH) : Prop :=
  context.consumed ⊑ context.base.outstanding

/-- An outstanding, unconsumed, active grant covers this source. -/
def Available {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (context : ConsumedContext α CausalOp Version HistoryOp H VH)
    (source : Evidence.Source) (grant : Authority.Grant) : Prop :=
  context.base.outstanding grant = true
    ∧ context.consumed grant = false
    ∧ Authority.Active (Gated.grants context.base.authority)
        (Gated.revoked context.base.authority) grant
    ∧ Gated.covers grant.2.2 (WorldContext.sourceProbe source grant.1)

/-- One atomic receipt may consume several grants.  `used` is fresh, lies in
the pre-state's outstanding set, and is unioned into the tombstones exactly.
The underlying world/context axes remain frozen while evidence is delivered. -/
structure ConsumptionReceipt
    {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (before after : ConsumedContext α CausalOp Version HistoryOp H VH) : Type where
  used : Authority.GrantSet
  base_frozen : WorldContext.Frozen before.base after.base
  used_fresh : ∀ grant, used grant = true → before.consumed grant = false
  used_outstanding : used ⊑ before.base.outstanding
  consumed_exact : after.consumed = before.consumed ⊔ used

namespace ConsumptionReceipt

theorem consumed_mono
    {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {before after : ConsumedContext α CausalOp Version HistoryOp H VH}
    (receipt : ConsumptionReceipt before after) :
    before.consumed ⊑ after.consumed := by
  rw [receipt.consumed_exact]
  exact le_merge_left _ _

theorem used_after
    {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {before after : ConsumedContext α CausalOp Version HistoryOp H VH}
    (receipt : ConsumptionReceipt before after) {grant : Authority.Grant}
    (hused : receipt.used grant = true) : after.consumed grant = true := by
  rw [receipt.consumed_exact]
  exact (Holes.gset_mem_or _ _ _).2 (Or.inr hused)

theorem unused_unchanged
    {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {before after : ConsumedContext α CausalOp Version HistoryOp H VH}
    (receipt : ConsumptionReceipt before after) {grant : Authority.Grant}
    (hunused : receipt.used grant = false) :
    after.consumed grant = before.consumed grant := by
  rw [receipt.consumed_exact]
  show (before.consumed grant || receipt.used grant) = before.consumed grant
  simp [hunused]

theorem preserves_wf
    {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {before after : ConsumedContext α CausalOp Version HistoryOp H VH}
    (receipt : ConsumptionReceipt before after) (hwf : ConsumedWf before) :
    ConsumedWf after := by
  apply (Holes.gset_leq_iff_subset _ _).2
  intro grant hafter
  have hparts := (Holes.gset_mem_or _ _ grant).1
    (receipt.consumed_exact ▸ hafter)
  rw [receipt.base_frozen.outstanding]
  rcases hparts with hbefore | hused
  · exact (Holes.gset_leq_iff_subset _ _).1 hwf grant hbefore
  · exact (Holes.gset_leq_iff_subset _ _).1 receipt.used_outstanding grant hused

end ConsumptionReceipt

/-! ## 3. Context checks for the exact signed claim -/

/-- Context admission for one signed typed position.  Roster membership,
holder binding, causal origin and version are distinct checks.  `used_grant`
only records this token's consumption; another covering grant may remain. -/
structure ContextualPositionClaim
    {Γ : Preo.Expr.Schema}
    {program : Preo.DerivedProgram.Program Γ}
    {decoder : Preo.DerivedProgram.WorldDecoder Γ}
    {source : Holes.World → Evidence.Source}
    {Authentic : Holes.World → Evidence.Source → Prop}
    {worlds : GSet Holes.World}
    {CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version
      (Evidence.ResultEvidence program.type.denote) HistoryOp}
    {codec : PositionCodec program.type.denote CausalOp Version}
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    (claim : AuthenticatedPositionClaim program decoder source Authentic worlds
      codec keys keyRevocations issued received)
    (context : ConsumedContext program.type.denote CausalOp Version HistoryOp H VH)
    (used : Authority.GrantSet)
    (holder : AuthenticatedAdmission.GrantHolder) : Type where
  roster_member : context.base.world.roster claim.candidate.source = true
  grant : Authority.Grant
  used_grant : used grant = true
  available : Available context claim.candidate.source grant
  holder_bound : holder claim.signed.accepted.record.issuer grant.1
  causal_known : context.base.known.mem
    (codec.originOf claim.signed.accepted.event) = true
  base_allows : Histories.Reaches VH.dag context.base.base
    (codec.versionOf claim.signed.accepted.event)

/-! ## 4. Authenticated consuming delivery -/

/-- Erase the timestamp while retaining the exact value/source pair consumed
by `WorldFuture`. -/
def eraseTimestamp {α T : Type}
    (event : AuthenticatedFrontier.CandidateEvent α T) :
    α × Evidence.Source :=
  (event.1.value, event.2)

/-- Image of a timestamped candidate set under `eraseTimestamp`. -/
noncomputable def eraseTimestampSet {α T : Type}
    (events : GSet (AuthenticatedFrontier.CandidateEvent α T)) :
    GSet (α × Evidence.Source) :=
  Holes.bindSet events (fun event erased =>
    Holes.truth (eraseTimestamp event = erased))

/-- One exact typed-position/context witness for a newly delivered candidate.
The existential data remains proof-carrying: the signed claim and all decoded
equalities are retained, not merely its source id. -/
structure ExactPositionWitness
    {Γ : Preo.Expr.Schema}
    {program : Preo.DerivedProgram.Program Γ}
    {decoder : Preo.DerivedProgram.WorldDecoder Γ}
    {source : Holes.World → Evidence.Source}
    {Authentic : Holes.World → Evidence.Source → Prop}
    {worlds : GSet Holes.World}
    {CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version
      (Evidence.ResultEvidence program.type.denote) HistoryOp}
    {codec : PositionCodec program.type.denote CausalOp Version}
    {scheme : Authenticity.SignatureScheme}
    {keys : Authenticity.Keyring scheme}
    {keyRevocations : Authenticity.Revocations}
    {issued : Authenticity.Issued}
    {received : Authenticity.SignedRecord scheme → Prop}
    (context : ConsumedContext program.type.denote CausalOp Version HistoryOp H VH)
    (used : Authority.GrantSet)
    (holder : AuthenticatedAdmission.GrantHolder)
    (event : program.type.denote × Evidence.Source) : Type where
  claim : AuthenticatedPositionClaim program decoder source Authentic worlds
    codec keys keyRevocations issued received
  value_eq : claim.candidate.value = event.1
  source_eq : claim.candidate.source = event.2
  contextual : ContextualPositionClaim claim context used holder

/-- A distinct authenticated consuming transition.  It deliberately projects
only to `WorldFuture.DeliveryFuture`: ordinary `WorldContext.DeliveryFuture`
freezes `outstanding`, while this wrapper additionally grows consumption
tombstones.  The signed progress record binds its own exact issued/delivered
sets and lawful frontier advance; each new erased candidate separately carries
an exact signed typed-position witness and one freshly used grant. -/
structure AuthenticatedConsumingDelivery
    {Γ : Preo.Expr.Schema}
    {program : Preo.DerivedProgram.Program Γ}
    {decoder : Preo.DerivedProgram.WorldDecoder Γ}
    {source : Holes.World → Evidence.Source}
    {Authentic : Holes.World → Evidence.Source → Prop}
    {worlds : GSet Holes.World}
    {CausalOp Version HistoryOp T : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version
      (Evidence.ResultEvidence program.type.denote) HistoryOp}
    [Frontier.PartialOrder T]
    {positionCodec : PositionCodec program.type.denote CausalOp Version}
    {positionScheme : Authenticity.SignatureScheme}
    {positionKeys : Authenticity.Keyring positionScheme}
    {positionRevocations : Authenticity.Revocations}
    {positionIssued : Authenticity.Issued}
    {positionReceived : Authenticity.SignedRecord positionScheme → Prop}
    {progressScheme : Authenticity.SignatureScheme}
    {progressKeys : Authenticity.Keyring progressScheme}
    {progressRevocations : Authenticity.Revocations}
    {progressIssued : Authenticity.Issued}
    {progressReceived : Authenticity.SignedRecord progressScheme → Prop}
    {progressRoster : List Evidence.Source}
    {progressCodec : AuthenticatedFrontier.ProgressCodec program.type.denote T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress progressScheme
      progressKeys progressRevocations progressIssued progressReceived progressRoster}
    (advance : AuthenticatedFrontier.AuthenticatedAdvance progressCodec progress)
    (before after : ConsumedContext program.type.denote CausalOp Version HistoryOp H VH)
    (receipt : ConsumptionReceipt before after)
    (holder : AuthenticatedAdmission.GrantHolder) : Type where
  before_wf : ConsumedWf before
  after_wf : ConsumedWf after
  progress_source_member : before.base.world.roster progress.source = true
  world_delivery : WorldFuture.DeliveryFuture
    (WorldContext.project before.base) (WorldContext.project after.base)
  issued_before_exact : before.base.world.issued = eraseTimestampSet advance.issued
  issued_after_exact : after.base.world.issued = eraseTimestampSet advance.issued
  delivered_before_exact : WorldFuture.delivered before.base.world =
    eraseTimestampSet advance.deliveredBefore
  delivered_after_exact : WorldFuture.delivered after.base.world =
    eraseTimestampSet advance.deliveredAfter
  new_position : ∀ event,
    WorldFuture.delivered before.base.world event = false →
    WorldFuture.delivered after.base.world event = true →
    Nonempty (ExactPositionWitness
      (program := program) (decoder := decoder) (source := source)
      (Authentic := Authentic) (worlds := worlds) (codec := positionCodec)
      (keys := positionKeys) (keyRevocations := positionRevocations)
      (issued := positionIssued) (received := positionReceived)
      before receipt.used holder event)
  used_justified : ∀ grant, receipt.used grant = true →
    ∃ event,
      WorldFuture.delivered before.base.world event = false
        ∧ WorldFuture.delivered after.base.world event = true
        ∧ ∃ witness : ExactPositionWitness
          (program := program) (decoder := decoder) (source := source)
          (Authentic := Authentic) (worlds := worlds) (codec := positionCodec)
          (keys := positionKeys) (keyRevocations := positionRevocations)
          (issued := positionIssued) (received := positionReceived)
          before receipt.used holder event,
          witness.contextual.grant = grant
  grant_unique : ∀ {event₁ event₂}
    (first : ExactPositionWitness
      (program := program) (decoder := decoder) (source := source)
      (Authentic := Authentic) (worlds := worlds) (codec := positionCodec)
      (keys := positionKeys) (keyRevocations := positionRevocations)
      (issued := positionIssued) (received := positionReceived)
      before receipt.used holder event₁)
    (second : ExactPositionWitness
      (program := program) (decoder := decoder) (source := source)
      (Authentic := Authentic) (worlds := worlds) (codec := positionCodec)
      (keys := positionKeys) (keyRevocations := positionRevocations)
      (issued := positionIssued) (received := positionReceived)
      before receipt.used holder event₂),
    first.contextual.grant = second.contextual.grant → event₁ = event₂

namespace AuthenticatedConsumingDelivery

theorem projects_world_delivery
    {Γ : Preo.Expr.Schema}
    {program : Preo.DerivedProgram.Program Γ}
    {decoder : Preo.DerivedProgram.WorldDecoder Γ}
    {source : Holes.World → Evidence.Source}
    {Authentic : Holes.World → Evidence.Source → Prop}
    {worlds : GSet Holes.World}
    {CausalOp Version HistoryOp T : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version
      (Evidence.ResultEvidence program.type.denote) HistoryOp}
    [Frontier.PartialOrder T]
    {positionCodec : PositionCodec program.type.denote CausalOp Version}
    {positionScheme : Authenticity.SignatureScheme}
    {positionKeys : Authenticity.Keyring positionScheme}
    {positionRevocations : Authenticity.Revocations}
    {positionIssued : Authenticity.Issued}
    {positionReceived : Authenticity.SignedRecord positionScheme → Prop}
    {progressScheme : Authenticity.SignatureScheme}
    {progressKeys : Authenticity.Keyring progressScheme}
    {progressRevocations : Authenticity.Revocations}
    {progressIssued : Authenticity.Issued}
    {progressReceived : Authenticity.SignedRecord progressScheme → Prop}
    {progressRoster : List Evidence.Source}
    {progressCodec : AuthenticatedFrontier.ProgressCodec program.type.denote T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress progressScheme
      progressKeys progressRevocations progressIssued progressReceived progressRoster}
    {advance : AuthenticatedFrontier.AuthenticatedAdvance progressCodec progress}
    {before after : ConsumedContext program.type.denote CausalOp Version HistoryOp H VH}
    {receipt : ConsumptionReceipt before after}
    {holder : AuthenticatedAdmission.GrantHolder}
    (delivery : AuthenticatedConsumingDelivery
      (decoder := decoder) (source := source) (Authentic := Authentic)
      (worlds := worlds) (positionCodec := positionCodec)
      (positionKeys := positionKeys)
      (positionRevocations := positionRevocations)
      (positionIssued := positionIssued)
      (positionReceived := positionReceived)
      advance before after receipt holder) :
    WorldFuture.DeliveryFuture (WorldContext.project before.base)
      (WorldContext.project after.base) :=
  delivery.world_delivery

theorem progress_is_lawful
    {Γ : Preo.Expr.Schema}
    {program : Preo.DerivedProgram.Program Γ}
    {decoder : Preo.DerivedProgram.WorldDecoder Γ}
    {source : Holes.World → Evidence.Source}
    {Authentic : Holes.World → Evidence.Source → Prop}
    {worlds : GSet Holes.World}
    {CausalOp Version HistoryOp T : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version
      (Evidence.ResultEvidence program.type.denote) HistoryOp}
    [Frontier.PartialOrder T]
    {positionCodec : PositionCodec program.type.denote CausalOp Version}
    {positionScheme : Authenticity.SignatureScheme}
    {positionKeys : Authenticity.Keyring positionScheme}
    {positionRevocations : Authenticity.Revocations}
    {positionIssued : Authenticity.Issued}
    {positionReceived : Authenticity.SignedRecord positionScheme → Prop}
    {progressScheme : Authenticity.SignatureScheme}
    {progressKeys : Authenticity.Keyring progressScheme}
    {progressRevocations : Authenticity.Revocations}
    {progressIssued : Authenticity.Issued}
    {progressReceived : Authenticity.SignedRecord progressScheme → Prop}
    {progressRoster : List Evidence.Source}
    {progressCodec : AuthenticatedFrontier.ProgressCodec program.type.denote T}
    {progress : AuthenticatedFrontier.AuthenticatedProgress progressScheme
      progressKeys progressRevocations progressIssued progressReceived progressRoster}
    {advance : AuthenticatedFrontier.AuthenticatedAdvance progressCodec progress}
    {before after : ConsumedContext program.type.denote CausalOp Version HistoryOp H VH}
    {receipt : ConsumptionReceipt before after}
    {holder : AuthenticatedAdmission.GrantHolder}
    (_delivery : AuthenticatedConsumingDelivery
      (decoder := decoder) (source := source) (Authentic := Authentic)
      (worlds := worlds) (positionCodec := positionCodec)
      (positionKeys := positionKeys)
      (positionRevocations := positionRevocations)
      (positionIssued := positionIssued)
      (positionReceived := positionReceived)
      advance before after receipt holder) :
    Frontier.DeliveryAdvance AuthenticatedFrontier.candidateStamp advance.issued
      (progressCodec.beforeOf progress.acceptedEvent.event)
      (progressCodec.afterOf progress.acceptedEvent.event)
      advance.deliveredBefore advance.deliveredAfter :=
  advance.toDeliveryAdvance

end AuthenticatedConsumingDelivery

/-! ## 5. Concrete positive and refusal fixtures -/

def positionEvent : Era.Event := ⟨501, positionKind, 1, 1, 0⟩

def positionRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 1 1 (.event positionEvent)

def positionIssued : Authenticity.Issued :=
  fun issuer epoch payload => issuer = 1 ∧ epoch = 1 ∧ payload = .event positionEvent

def positionReceived : Authenticity.SignedRecord Authenticity.toyScheme → Prop :=
  fun record => record = positionRecord

theorem positionRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme AuthenticatedAdmission.moveKeys
      Authenticity.noRevocations positionRecord := by
  apply Authenticity.signRecord_accepted
  · simp [AuthenticatedAdmission.moveKeys, Era.alice, Era.bob]
  · rfl

def acceptedPosition : AuthenticatedAdmission.AcceptedEvent
    Authenticity.toyScheme AuthenticatedAdmission.moveKeys
    Authenticity.noRevocations :=
  ⟨positionRecord, positionEvent, rfl, positionRecord_accepted⟩

theorem positionIssuer_authentic :
    Authenticity.AuthenticIssuer Authenticity.toyScheme
      AuthenticatedAdmission.moveKeys Authenticity.noRevocations positionIssued
      positionReceived := by
  intro record hreceived _
  subst record
  exact ⟨rfl, rfl, rfl⟩

def issuedPosition : IssuedPositionEvent Authenticity.toyScheme
    AuthenticatedAdmission.moveKeys Authenticity.noRevocations positionIssued
    positionReceived :=
  IssuedPositionEvent.ofAuthenticIssuer positionIssuer_authentic acceptedPosition
    rfl rfl

def positionWorlds : GSet Holes.World := Delta.addDelta [1, 49]

def positionCodec : PositionCodec Nat Bool WorldContext.Version where
  worldOf := fun _ => [1, 49]
  valueOf := fun _ => 49
  positionOf := fun _ => Preo.DerivedProgram.maxRightPosition
  originOf := fun _ => false
  versionOf := fun _ => .event

def positionCandidate : Evidence.PositionCandidate Nat Preo.Expr.Hole :=
  ⟨49, 1, Preo.DerivedProgram.maxRightPosition⟩

def exactPositionClaim : AuthenticatedPositionClaim
    Preo.DerivedProgram.maxFields (Preo.DerivedProgram.natWorldDecoder 2)
    (fun world => Holes.read world 0) Preo.DerivedProgram.RegisterZeroAuthentic
    positionWorlds positionCodec AuthenticatedAdmission.moveKeys
    Authenticity.noRevocations positionIssued positionReceived where
  signed := issuedPosition
  candidate := positionCandidate
  world := [1, 49]
  sourceAuthenticity := Preo.DerivedProgram.registerZeroAuthenticity positionWorlds
  world_present := by simp [positionWorlds, Delta.addDelta]
  value_exact := by change Nat.max 1 49 = 49; decide
  source_exact := rfl
  position_exact := by
    simp [positionCandidate, Preo.DerivedProgram.maxFields_holes,
      Preo.DerivedProgram.maxRightPosition]
  decoded_world := rfl
  decoded_value := rfl
  decoded_position := rfl
  source_signed := rfl

theorem exactPosition_materialized :
    Preo.DerivedProgram.maxFields.verifiedAttributedDocument
        (Preo.DerivedProgram.natWorldDecoder 2)
        (fun world => Holes.read world 0)
        Preo.DerivedProgram.RegisterZeroAuthentic
        Preo.DerivedProgram.noSources Preo.DerivedProgram.noSources positionWorlds
        exactPositionClaim.sourceAuthenticity
        (.position positionCandidate) = true :=
  exactPositionClaim.materialized _ _

abbrev DemoConsumedContext := ConsumedContext Holes.Val Bool
  WorldContext.Version Unit WorldContext.causalHistory WorldContext.versionHistory

def noConsumed : Authority.GrantSet := fun _ => false
def usedDelegate : Authority.GrantSet := WorldContext.delegateCapability

def beforeConsumption : DemoConsumedContext :=
  ⟨WorldContext.capRich, noConsumed⟩

def afterConsumption : DemoConsumedContext :=
  ⟨WorldContext.capRichDelivered, usedDelegate⟩

def delegateReceipt : ConsumptionReceipt beforeConsumption afterConsumption where
  used := usedDelegate
  base_frozen := WorldContext.frozen_capRich
  used_fresh := by intro _ _; rfl
  used_outstanding := by
    change WorldContext.delegateCapability ⊑ WorldContext.delegateCapability
    exact leq_refl _
  consumed_exact := by
    funext grant
    change WorldContext.delegateCapability grant =
      (false || WorldContext.delegateCapability grant)
    simp

def positionHolder : AuthenticatedAdmission.GrantHolder :=
  fun issuer cite => issuer = 1 ∧ cite = 2

def contextualPosition : ContextualPositionClaim exactPositionClaim
    beforeConsumption usedDelegate positionHolder where
  roster_member := by decide
  grant := (2, 1, 4)
  used_grant := by decide
  available := by
    refine ⟨by decide, rfl, Authority.demo_delegate_active, by decide⟩
  holder_bound := ⟨rfl, rfl⟩
  causal_known := rfl
  base_allows := WorldContext.root_reaches_event

def timestampedIssued : GSet (AuthenticatedFrontier.CandidateEvent Nat Nat) :=
  fun event => decide
    ((event.1.value = 47 ∧ event.1.timestamp = 0 ∧ event.2 = Evidence.alice)
      ∨ (event.1.value = 49 ∧ event.1.timestamp = 0 ∧ event.2 = Evidence.bob))

def timestampedBefore : GSet (AuthenticatedFrontier.CandidateEvent Nat Nat) :=
  fun event => decide
    (event.1.value = 47 ∧ event.1.timestamp = 0 ∧ event.2 = Evidence.alice)

def timestampedAfter : GSet (AuthenticatedFrontier.CandidateEvent Nat Nat) :=
  timestampedIssued

def progressEvent : Era.Event :=
  ⟨601, AuthenticatedFrontier.progressKind, 1, 1, 0⟩

def progressRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 1 1 (.event progressEvent)

def progressIssued : Authenticity.Issued :=
  fun issuer epoch payload => issuer = 1 ∧ epoch = 1 ∧ payload = .event progressEvent

def progressReceived : Authenticity.SignedRecord Authenticity.toyScheme → Prop :=
  fun record => record = progressRecord

theorem progressRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme AuthenticatedAdmission.moveKeys
      Authenticity.noRevocations progressRecord := by
  apply Authenticity.signRecord_accepted
  · simp [AuthenticatedAdmission.moveKeys, Era.alice, Era.bob]
  · rfl

def acceptedProgress : AuthenticatedAdmission.AcceptedEvent
    Authenticity.toyScheme AuthenticatedAdmission.moveKeys
    Authenticity.noRevocations :=
  ⟨progressRecord, progressEvent, rfl, progressRecord_accepted⟩

theorem progressIssuer_authentic :
    Authenticity.AuthenticIssuer Authenticity.toyScheme
      AuthenticatedAdmission.moveKeys Authenticity.noRevocations progressIssued
      progressReceived := by
  intro record hreceived _
  subst record
  exact ⟨rfl, rfl, rfl⟩

def authenticatedProgress : AuthenticatedFrontier.AuthenticatedProgress
    Authenticity.toyScheme AuthenticatedAdmission.moveKeys
    Authenticity.noRevocations progressIssued progressReceived [0, 1] :=
  AuthenticatedFrontier.AuthenticatedProgress.ofAuthenticIssuer acceptedProgress
    rfl progressIssuer_authentic rfl rfl (by
      simp [acceptedProgress, progressRecord, Authenticity.signRecord])

def progressCodec : AuthenticatedFrontier.ProgressCodec Nat Nat where
  timeOf := fun _ => 0
  beforeOf := fun _ => Frontier.singleton ⟨Evidence.bob, 0⟩
  afterOf := fun _ => Frontier.empty (Frontier.Point Nat)
  issuedOf := fun _ => timestampedIssued
  deliveredBeforeOf := fun _ => timestampedBefore
  deliveredAfterOf := fun _ => timestampedAfter

def authenticatedAdvance : AuthenticatedFrontier.AuthenticatedAdvance
    progressCodec authenticatedProgress where
  source_settled := Frontier.complete_empty _
  lawful := by
    constructor
    · change timestampedBefore ⊑ timestampedAfter
      apply (Holes.gset_leq_iff_subset _ _).2
      intro event hbefore
      apply decide_eq_true
      exact Or.inl (of_decide_eq_true hbefore)
    · intro point hcovered
      exact False.elim (Frontier.not_covers_empty point hcovered)
    · intro event hissued _
      exact hissued

theorem erase_timestampedIssued :
    eraseTimestampSet timestampedIssued = Evidence.cand4749 := by
  apply Holes.gset_ext
  intro event
  unfold eraseTimestampSet
  rw [Holes.mem_bindSet]
  constructor
  · rintro ⟨timestamped, htimestamped, herased⟩
    have heq := Holes.truth_eq_true.mp herased
    simp [timestampedIssued] at htimestamped
    rcases htimestamped with h47 | h49
    · rcases h47 with ⟨hvalue, htime, hsource⟩
      have htimestamped : eraseTimestamp timestamped =
          (47, Evidence.alice) := by
        apply Prod.ext <;> simp [eraseTimestamp, hvalue, hsource]
      rw [← heq, htimestamped]
      decide
    · rcases h49 with ⟨hvalue, htime, hsource⟩
      have htimestamped : eraseTimestamp timestamped =
          (49, Evidence.bob) := by
        apply Prod.ext <;> simp [eraseTimestamp, hvalue, hsource]
      rw [← heq, htimestamped]
      decide
  · intro hevent
    simp [Evidence.cand4749] at hevent
    rcases hevent with rfl | rfl
    · exact ⟨(⟨47, 0⟩, Evidence.alice), by
        simp [timestampedIssued], Holes.truth_eq_true.2 rfl⟩
    · exact ⟨(⟨49, 0⟩, Evidence.bob), by
        simp [timestampedIssued], Holes.truth_eq_true.2 rfl⟩

theorem erase_timestampedBefore :
    eraseTimestampSet timestampedBefore = Evidence.cand47 := by
  apply Holes.gset_ext
  intro event
  unfold eraseTimestampSet
  rw [Holes.mem_bindSet]
  constructor
  · rintro ⟨timestamped, htimestamped, herased⟩
    have heq := Holes.truth_eq_true.mp herased
    simp [timestampedBefore] at htimestamped
    rcases htimestamped with ⟨hvalue, htime, hsource⟩
    have htimestamped : eraseTimestamp timestamped =
        (47, Evidence.alice) := by
      apply Prod.ext <;> simp [eraseTimestamp, hvalue, hsource]
    rw [← heq, htimestamped]
    decide
  · intro hevent
    have heq : event = (47, Evidence.alice) := of_decide_eq_true hevent
    subst event
    exact ⟨(⟨47, 0⟩, Evidence.alice), by
      simp [timestampedBefore], Holes.truth_eq_true.2 rfl⟩

def exactPositionWitness : ExactPositionWitness
    (program := Preo.DerivedProgram.maxFields)
    (decoder := Preo.DerivedProgram.natWorldDecoder 2)
    (source := fun world => Holes.read world 0)
    (Authentic := Preo.DerivedProgram.RegisterZeroAuthentic)
    (worlds := positionWorlds) (codec := positionCodec)
    (keys := AuthenticatedAdmission.moveKeys)
    (keyRevocations := Authenticity.noRevocations)
    (issued := positionIssued) (received := positionReceived)
    beforeConsumption usedDelegate positionHolder
      ((49 : Nat), Evidence.bob) where
  claim := exactPositionClaim
  value_eq := rfl
  source_eq := rfl
  contextual := contextualPosition

def authenticatedConsumingDelivery : AuthenticatedConsumingDelivery
    (program := Preo.DerivedProgram.maxFields)
    (decoder := Preo.DerivedProgram.natWorldDecoder 2)
    (source := fun world => Holes.read world 0)
    (Authentic := Preo.DerivedProgram.RegisterZeroAuthentic)
    (worlds := positionWorlds) (positionCodec := positionCodec)
    (positionKeys := AuthenticatedAdmission.moveKeys)
    (positionRevocations := Authenticity.noRevocations)
    (positionIssued := positionIssued) (positionReceived := positionReceived)
    authenticatedAdvance beforeConsumption afterConsumption delegateReceipt
    positionHolder where
  before_wf := by
    apply (Holes.gset_leq_iff_subset _ _).2
    intro grant h
    exact Bool.noConfusion h
  after_wf := leq_refl _
  progress_source_member := by decide
  world_delivery := WorldFuture.delivery_wPending_wDelivered
  issued_before_exact := erase_timestampedIssued.symm
  issued_after_exact := erase_timestampedIssued.symm
  delivered_before_exact := erase_timestampedBefore.symm
  delivered_after_exact := erase_timestampedIssued.symm
  new_position := by
    intro event hbefore hafter
    have hevent := WorldContext.added_candidate_is_bob hbefore hafter
    subst event
    exact ⟨exactPositionWitness⟩
  used_justified := by
    intro grant hused
    have hgrant : grant = (2, 1, 4) := of_decide_eq_true hused
    subst grant
    refine ⟨((49 : Nat), Evidence.bob), by decide, by decide,
      exactPositionWitness, rfl⟩
  grant_unique := by
    intro event₁ event₂ first second _
    apply Prod.ext
    · have hfirst := first.claim.decoded_value
      have hsecond := second.claim.decoded_value
      simp [positionCodec] at hfirst hsecond
      exact first.value_eq.symm.trans (hfirst.symm.trans
        (hsecond.trans second.value_eq))
    · have hfirstRecord := first.claim.signed.received_record
      have hsecondRecord := second.claim.signed.received_record
      change first.claim.signed.accepted.record = positionRecord at hfirstRecord
      change second.claim.signed.accepted.record = positionRecord at hsecondRecord
      calc
        event₁.2 = first.claim.candidate.source := first.source_eq.symm
        _ = first.claim.signed.accepted.record.issuer :=
          first.claim.source_signed
        _ = second.claim.signed.accepted.record.issuer := by
          rw [hfirstRecord, hsecondRecord]
        _ = second.claim.candidate.source := second.claim.source_signed.symm
        _ = event₂.2 := second.source_eq

theorem authenticated_delivery_projects :
    WorldFuture.DeliveryFuture WorldFuture.wPending WorldFuture.wDelivered :=
  authenticatedConsumingDelivery.projects_world_delivery

theorem delegate_consumed_once :
    beforeConsumption.consumed (2, 1, 4) = false
      ∧ afterConsumption.consumed (2, 1, 4) = true :=
  ⟨rfl, delegateReceipt.used_after (by decide)⟩

/-- The toy scheme makes verification forgeable.  This record is accepted but
is absent from the exact issuance transcript, so no issued-position envelope
can promote it. -/
def forgedPositionEvent : Era.Event := ⟨999, positionKind, 1, 1, 0⟩

def forgedPositionRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 1 1 (.event forgedPositionEvent)

theorem forgedPositionRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme AuthenticatedAdmission.moveKeys
      Authenticity.noRevocations forgedPositionRecord := by
  apply Authenticity.signRecord_accepted
  · simp [AuthenticatedAdmission.moveKeys, Era.alice, Era.bob]
  · rfl

theorem forgedPositionRecord_not_issued :
    ¬ Authenticity.WasIssued positionIssued forgedPositionRecord := by
  simp [Authenticity.WasIssued, positionIssued, forgedPositionRecord,
    forgedPositionEvent, positionEvent, Authenticity.signRecord]

theorem accepted_forgery_not_promoted :
    ¬ ∃ admitted : IssuedPositionEvent Authenticity.toyScheme
        AuthenticatedAdmission.moveKeys Authenticity.noRevocations positionIssued
        (fun record => record = forgedPositionRecord),
      admitted.accepted.record = forgedPositionRecord := by
  rintro ⟨admitted, hrecord⟩
  exact forgedPositionRecord_not_issued (hrecord ▸ admitted.wasIssued)

/-- A stale base reaches the head but not the signed claim's event version. -/
def alternateConsumption : DemoConsumedContext :=
  ⟨WorldContext.alternateBase, noConsumed⟩

theorem stale_base_refuses_position :
    ¬ Nonempty (ContextualPositionClaim exactPositionClaim alternateConsumption
      usedDelegate positionHolder) := by
  rintro ⟨admitted⟩
  exact WorldContext.not_alternate_reaches_event admitted.base_allows

/-- This cut knows only causal origin `true`; the signed position decodes to
origin `false`, so equal roster, authority and version data cannot promote it. -/
def trueOnlyCut : CausalReach.Cut WorldContext.causalHistory where
  mem := fun origin => decide (origin = true)
  down := CausalReach.eqHistory_down Bool (fun origin => decide (origin = true))

def wrongOriginBase : WorldContext.DemoContext where
  world := WorldFuture.wPending
  authority := WorldContext.authorityContext
  outstanding := WorldContext.delegateCapability
  known := trueOnlyCut
  base := .root
  head := .head
  base_reaches_head := WorldContext.root_reaches_head

def wrongOriginConsumption : DemoConsumedContext :=
  ⟨wrongOriginBase, noConsumed⟩

theorem wrong_origin_refuses_position :
    ¬ Nonempty (ContextualPositionClaim exactPositionClaim wrongOriginConsumption
      usedDelegate positionHolder) := by
  rintro ⟨admitted⟩
  exact Bool.noConfusion admitted.causal_known

/-- Tombstoning this token makes the same exact signed claim unavailable.
This does not assert that no alternate covering token exists. -/
theorem consumed_token_not_reusable :
    ¬ Available afterConsumption positionCandidate.source (2, 1, 4) := by
  intro available
  exact Bool.noConfusion available.2.1

end Uwueave.AuthenticatedWorldContext
