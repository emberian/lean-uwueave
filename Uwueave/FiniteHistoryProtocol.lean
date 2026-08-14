/-
# Uwueave.FiniteHistoryProtocol -- settled finite delivery to semantic convergence

This downstream leaf closes the finite, duplicate-tolerant protocol argument.
Two successful settled deliveries may use different orders, capacities, and any
number of exact retries.  If their journals cover the same finite target
extensionally, their materialized event sets agree.

That runtime fact is deliberately not yet semantic convergence.  A
`RecordImage` states the missing representation invariant: equal materialized
event sets represent `SameRecord` histories.  `SemanticReplica` packages one
settled delivery with a history represented by such an image, and the final
theorems compose the image invariant with `HistoryConvergent` or
`RecordDetermined`.

Stable event identifiers remain equality keys.  Authentication may establish
the provenance of a journal or manifest, but is orthogonal to both event-set
convergence and the `SameRecord` premise proved here.
-/
import Uwueave.FiniteHistoryDelivery

namespace Uwueave.FiniteHistoryProtocol

open Uwueave.Histories Uwueave.HistoryPolicy
open Uwueave.HistoryRuntime Uwueave.PersistentRuntime
open Uwueave.PersistentHistoryRuntime

set_option autoImplicit false

universe uPayload uV uS uOp

/-! ## 1. Duplicate-tolerant finite coverage -/

/-- Two finite lists cover the same extensional set.  Order and multiplicity
are intentionally erased, so exact retries are admitted. -/
def Covers {α : Type uPayload} [DecidableEq α]
    (arrivals target : List α) : Prop :=
  ∀ item, item ∈ arrivals ↔ item ∈ target

theorem Covers.refl {α : Type uPayload} [DecidableEq α] (target : List α) :
    Covers target target :=
  fun _ => Iff.rfl

theorem Covers.symm {α : Type uPayload} [DecidableEq α]
    {left right : List α} (covers : Covers left right) : Covers right left :=
  fun item => (covers item).symm

theorem Covers.trans {α : Type uPayload} [DecidableEq α]
    {first second third : List α}
    (left : Covers first second) (right : Covers second third) :
    Covers first third :=
  fun item => (left item).trans (right item)

/-- Repeating an already presented head is extensionally invisible. -/
theorem Covers.duplicate_head {α : Type uPayload} [DecidableEq α]
    (item : α) (rest : List α) :
    Covers (item :: item :: rest) (item :: rest) := by
  intro candidate
  simp

/-- One successful application changes authoritative membership by exactly the
presented record (or leaves it unchanged for a retry). -/
theorem applyRecord_success_accepted_iff
    {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (schema : RecordSchema State Record Nonce)
    {before after : Cursor State Record} {record : Record}
    (success : applyRecord schema before record = some after)
    (item : Record) :
    item ∈ after.accepted ↔ item ∈ before.accepted ∨ item = record := by
  by_cases known : record ∈ before.accepted
  · simp [applyRecord, known] at success
    cases success
    constructor
    · exact fun member => Or.inl member
    · rintro (member | rfl)
      · exact member
      · exact known
  · by_cases collision : ∃ prior ∈ before.accepted,
        schema.nonce prior = schema.nonce record
    · simp [applyRecord, known, collision] at success
    · cases admitted : schema.step before.state record with
      | none => simp [applyRecord, known, collision, admitted] at success
      | some next =>
          simp [applyRecord, known, collision, admitted] at success
          cases success
          simp

/-- A successful replay contains exactly the old authoritative records and the
records that occurred in its journal, extensionally. -/
theorem replay_success_accepted_iff
    {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (schema : RecordSchema State Record Nonce)
    {before after : Cursor State Record} {records : List Record}
    (success : replay schema before records = some after)
    (item : Record) :
    item ∈ after.accepted ↔ item ∈ before.accepted ∨ item ∈ records := by
  induction records generalizing before after with
  | nil =>
      simp only [replay] at success
      cases success
      simp
  | cons record rest ih =>
      cases applied : applyRecord schema before record with
      | none => simp [replay, applied] at success
      | some middle =>
          have tailSuccess : replay schema middle rest = some after := by
            simpa [replay, applied] using success
          rw [ih tailSuccess, applyRecord_success_accepted_iff schema applied]
          simp only [List.mem_cons]
          constructor
          · rintro ((old | current) | tail)
            · exact Or.inl old
            · exact Or.inr (Or.inl current)
            · exact Or.inr (Or.inr tail)
          · rintro (old | current | tail)
            · exact Or.inl (Or.inl old)
            · exact Or.inl (Or.inr current)
            · exact Or.inr tail

/-- A successful replay from an empty cursor contains exactly the records that
occurred in its journal.  Multiplicity is absent from both sides. -/
theorem replay_from_empty_accepted_iff
    {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (schema : RecordSchema State Record Nonce) (initial : State)
    {records : List Record} {after : Cursor State Record}
    (success : replay schema (emptyCursor initial) records = some after)
    (item : Record) :
    item ∈ after.accepted ↔ item ∈ records := by
  rw [replay_success_accepted_iff schema success]
  simp [emptyCursor]

/-- One duplicate-tolerant successful replay of a finite target.  `settled`
rules out unresolved pending arrivals, while `coherent` connects the
authoritative accepted records to the two runtime stores. -/
structure SettledReplay {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (target : List (Event Id Payload)) (capacity : Nat) where
  arrivals : List (Event Id Payload)
  covers : Covers arrivals target
  cursor : DeliveryCursor Id Payload
  replay_exact : replay (deliverySchema Id Payload)
    (emptyDeliveryCursor Id Payload capacity) arrivals = some cursor
  coherent : DeliveryCursorCoherent cursor
  settled : cursor.state.pending = []

namespace SettledReplay

variable {Id Payload : Type}
  [DecidableEq Id] [DecidableEq Payload]
  {target : List (Event Id Payload)} {capacity : Nat}

theorem accepted_iff (delivery : SettledReplay target capacity)
    (event : Event Id Payload) :
    event ∈ delivery.cursor.accepted ↔ event ∈ target := by
  exact (replay_from_empty_accepted_iff
    (deliverySchema Id Payload) (DeliveryState.empty Id Payload capacity)
    delivery.replay_exact event).trans (delivery.covers event)

theorem materialized_iff (delivery : SettledReplay target capacity)
    (event : Event Id Payload) :
    event ∈ delivery.cursor.state.materialized.accepted ↔ event ∈ target := by
  have cursorIff := delivery.coherent.2 event
  rw [delivery.settled] at cursorIff
  simp only [List.not_mem_nil, or_false] at cursorIff
  exact cursorIff.symm.trans (delivery.accepted_iff event)

theorem sameEventSet {leftCapacity rightCapacity : Nat}
    (left : SettledReplay target leftCapacity)
    (right : SettledReplay target rightCapacity) :
    SameEventSet left.cursor.state.materialized
      right.cursor.state.materialized := by
  intro event
  exact (left.materialized_iff event).trans
    (right.materialized_iff event).symm

theorem settledSameEventSet {leftCapacity rightCapacity : Nat}
    (left : SettledReplay target leftCapacity)
    (right : SettledReplay target rightCapacity) :
    SettledSameEventSet left.cursor.state right.cursor.state :=
  ⟨left.settled, right.settled, left.sameEventSet right⟩

theorem eventSetView_eq {leftCapacity rightCapacity : Nat}
    (left : SettledReplay target leftCapacity)
    (right : SettledReplay target rightCapacity) :
    eventSetView left.cursor.state.materialized =
      eventSetView right.cursor.state.materialized :=
  (left.settledSameEventSet right).view_eq

end SettledReplay

/-! ## 2. The explicit semantic boundary -/

/-- A representation relation from a materialized event set to a semantic
history, together with the exact faithfulness property convergence needs.
Nothing in this interface infers semantic history content from `Event Id V`.
-/
structure RecordImage (Id Payload : Type)
    (V : Type uV) (S : Type uS) (Op : Type uOp)
    [DecidableEq Id] [DecidableEq Payload] where
  Represents : EventState Id Payload → History V S Op → Prop
  faithful : ∀ {left right : EventState Id Payload}
    {leftHistory rightHistory : History V S Op},
    SameEventSet left right →
    Represents left leftHistory → Represents right rightHistory →
    SameRecord leftHistory rightHistory

/-- A settled finite delivery paired with the semantic history its record image
represents. -/
structure SemanticReplica {Id Payload : Type}
    {V : Type uV} {S : Type uS} {Op : Type uOp}
    [DecidableEq Id] [DecidableEq Payload]
    (image : RecordImage Id Payload V S Op)
    (target : List (Event Id Payload)) (capacity : Nat) where
  delivery : SettledReplay target capacity
  history : History V S Op
  represented : image.Represents delivery.cursor.state.materialized history

namespace SemanticReplica

variable {Id Payload : Type}
  {V : Type uV} {S : Type uS} {Op : Type uOp}
  [DecidableEq Id] [DecidableEq Payload]
  {image : RecordImage Id Payload V S Op}
  {target : List (Event Id Payload)}

theorem sameRecord {leftCapacity rightCapacity : Nat}
    (left : SemanticReplica image target leftCapacity)
    (right : SemanticReplica image target rightCapacity) :
    SameRecord left.history right.history :=
  image.faithful (left.delivery.sameEventSet right.delivery)
    left.represented right.represented

/-- Protocol convergence from an already proved history-convergence law. -/
theorem view_eq_of_convergent {leftCapacity rightCapacity : Nat}
    {P : HistoryMerge V S Op}
    (left : SemanticReplica image target leftCapacity)
    (right : SemanticReplica image target rightCapacity)
    (convergent : HistoryConvergent P) (version : V) :
    viewOf P left.history version = viewOf P right.history version :=
  convergent left.history right.history (left.sameRecord right) version

/-- The common operational route: record-determined selection yields history
convergence, which the faithful record image lifts to settled replicas. -/
theorem view_eq_of_recordDetermined {leftCapacity rightCapacity : Nat}
    {P : HistoryMerge V S Op}
    (left : SemanticReplica image target leftCapacity)
    (right : SemanticReplica image target rightCapacity)
    (determined : RecordDetermined P) (version : V) :
    viewOf P left.history version = viewOf P right.history version :=
  left.view_eq_of_convergent right
    (HistoryPolicy.recordDetermined_converges determined) version

end SemanticReplica

/-! ## 3. Why `Event Id V` alone is insufficient -/

namespace PayloadCounterexample

def sharedEvent : Event Nat Unit := ⟨0, [], ()⟩

def sharedMaterialization : EventState Nat Unit := ⟨[sharedEvent]⟩

def singletonDag : VersionDag Unit where
  parent := fun _ _ => false
  rank := fun _ => 0
  rank_lt := by simp

def leftHistory : History Unit Bool Unit where
  dag := singletonDag
  state := fun _ => false
  origin := fun _ => .root
  root := ()

def rightHistory : History Unit Bool Unit where
  dag := singletonDag
  state := fun _ => true
  origin := fun _ => .root
  root := ()

/-- The deliberately weak interpretation available from the current payload:
the materialized event is fixed, while the semantic history is unconstrained.
Both counterexample histories satisfy it. -/
def PayloadOnlyRepresents (state : EventState Nat Unit)
    (_history : History Unit Bool Unit) : Prop :=
  state = sharedMaterialization

theorem shared_event_admits_both_histories :
    PayloadOnlyRepresents sharedMaterialization leftHistory ∧
      PayloadOnlyRepresents sharedMaterialization rightHistory :=
  ⟨rfl, rfl⟩

/-- The exact same `Event Nat Unit` set can accompany histories with different
root state.  Hence an event-set theorem cannot manufacture `SameRecord`; a
faithful `RecordImage` (or an equivalent refinement relation) is necessary. -/
theorem same_events_do_not_imply_sameRecord :
    PayloadOnlyRepresents sharedMaterialization leftHistory ∧
      PayloadOnlyRepresents sharedMaterialization rightHistory ∧
      SameEventSet sharedMaterialization sharedMaterialization ∧
      ¬ SameRecord leftHistory rightHistory := by
  refine ⟨rfl, rfl, sameEventSet_refl sharedMaterialization, ?_⟩
  intro same
  have genesis := same.genesis
  simp [leftHistory, rightHistory] at genesis

/-- Consequently the payload-only interpretation cannot inhabit
`RecordImage`: it fails precisely the interface's `faithful` field. -/
theorem payloadOnlyRepresents_not_faithful :
    ¬ (∀ {left right : EventState Nat Unit}
      {leftHistory rightHistory : History Unit Bool Unit},
      SameEventSet left right →
      PayloadOnlyRepresents left leftHistory →
      PayloadOnlyRepresents right rightHistory →
      SameRecord leftHistory rightHistory) := by
  intro faithful
  exact same_events_do_not_imply_sameRecord.2.2.2
    (faithful same_events_do_not_imply_sameRecord.2.2.1
      same_events_do_not_imply_sameRecord.1
      same_events_do_not_imply_sameRecord.2.1)

end PayloadCounterexample

/-! ## 4. Honest remaining boundary

`RecordImage` is intentionally an interface, not a claimed codec refinement.
This leaf supplies no canonical history encoder and proves no relation from
host bytes, signatures, or authenticated transport to `RecordImage.Represents`.
Consequently it closes **zero** host-byte refinement obligations.  A future
encoder must commit the root and genesis, the complete direct-parent and rank
rows, base-erased origin shape, and every root/run state; it must then prove
that equality of the encoded event set entails `SameRecord`.
-/

end Uwueave.FiniteHistoryProtocol
