/-
# Uwueave.PersistentHistoryRuntime -- causal history on checked replay

This module instantiates `PersistentRuntime.RecordSchema` twice: immediate
causal admission and bounded out-of-order delivery. In the latter, the
authoritative cursor's list records accepted arrivals, while its state separates
causally materialized events from bounded pending arrivals. Exact retries are
no-ops and identifier reuse with different content is a nonce collision.

Checkpoints are the generic checked prefix cursors from `PersistentRuntime`.
They are accelerators, not authority; the suffix theorem below is the existing
full-replay equality specialized to causal history events.

No theorem here claims a filesystem, authenticated network endpoint, or
infinite-history enumeration. Rust now has two separate host rungs: the older
`BufferedHistoryJournal` loses pending events on reopen, while
`HistoryArrivalJournal` durably replays its canonical accepted-arrival records.
The explicit callback contract below specifies the typed transition a host must
match. It does not prove that the Rust bytes, checksums, or filesystem implement
that contract, and no cross-language refinement theorem identifies them.
-/
import Uwueave.HistoryRuntime
import Uwueave.PersistentRuntime

namespace Uwueave.PersistentHistoryRuntime

open Uwueave.HistoryRuntime Uwueave.PersistentRuntime

set_option autoImplicit false

/-- Causal event admission as a deterministic persistent replay schema. -/
def historySchema (Id Payload : Type) [DecidableEq Id] [DecidableEq Payload] :
    RecordSchema (EventState Id Payload) (Event Id Payload) Id where
  nonce := Event.id
  step state event :=
    match HistoryRuntime.append state event with
    | .appended next => some next
    | .retry _ => none
    | .collision _ => none
    | .missingParent _ => none
    | .selfParent => none
    | .duplicateParent => none

abbrev HistoryCursor (Id Payload : Type) :=
  Cursor (EventState Id Payload) (Event Id Payload)

abbrev HistoryCheckpoint (Id Payload : Type) :=
  CheckpointData (EventState Id Payload) (Event Id Payload)

def emptyHistoryCursor (Id Payload : Type) : HistoryCursor Id Payload :=
  emptyCursor EventState.empty

/-- Schema admission is exactly a fresh successful causal decision.  Exact
retry is handled one layer up by `PersistentRuntime.applyRecord`; seeing it
inside `step` would expose an incoherent cursor whose materialized event state
contains a record absent from its authoritative record list. -/
theorem historySchema_step_eq_some_iff {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (state next : EventState Id Payload) (event : Event Id Payload) :
    (historySchema Id Payload).step state event = some next ↔
      HistoryRuntime.append state event = .appended next := by
  cases decision : HistoryRuntime.append state event <;>
    simp [historySchema, decision]

/-- Exact complete-event retry is idempotent at the persistent cursor layer. -/
theorem applyEvent_retry {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (cursor : HistoryCursor Id Payload) (event : Event Id Payload)
    (known : event ∈ cursor.accepted) :
    applyRecord (historySchema Id Payload) cursor event = some cursor :=
  applyRecord_retry _ _ _ known

/-- Reusing an accepted event id for different complete content is refused. -/
theorem applyEvent_collision {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (cursor : HistoryCursor Id Payload) (event prior : Event Id Payload)
    (coherent : NonceCoherent (historySchema Id Payload) cursor)
    (different : event ≠ prior) (known : prior ∈ cursor.accepted)
    (sameId : prior.id = event.id) :
    applyRecord (historySchema Id Payload) cursor event = none :=
  applyRecord_nonce_conflict _ cursor event prior coherent different known sameId

/-- A validated causal checkpoint resumes to exactly full replay. -/
theorem checkpoint_suffix_replay {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (journal : List (Event Id Payload))
    (checkpoint : HistoryCheckpoint Id Payload)
    (valid : CheckpointValid (historySchema Id Payload)
      (emptyHistoryCursor Id Payload) journal checkpoint) :
    replay (historySchema Id Payload) checkpoint.cursor
        (journal.drop checkpoint.consumed) =
      replay (historySchema Id Payload) (emptyHistoryCursor Id Payload) journal :=
  checkpoint_suffix_replay_equiv _ _ _ _ valid

/-! ## Executable causal/checkpoint witnesses -/

def rootEvent : Event Nat Nat := ⟨1, [], 10⟩
def leftEvent : Event Nat Nat := ⟨2, [1], 20⟩
def rightEvent : Event Nat Nat := ⟨3, [1], 30⟩
def orphanEvent : Event Nat Nat := ⟨4, [99], 40⟩
def forgedRoot : Event Nat Nat := ⟨1, [], 11⟩

def afterRootState : EventState Nat Nat := ⟨[rootEvent]⟩
def afterRootCursor : HistoryCursor Nat Nat := ⟨afterRootState, [rootEvent]⟩

theorem root_appends :
    applyRecord (historySchema Nat Nat) (emptyHistoryCursor Nat Nat) rootEvent =
      some afterRootCursor := by decide

theorem root_retry_is_idempotent :
    applyRecord (historySchema Nat Nat) afterRootCursor rootEvent =
      some afterRootCursor := by decide

theorem reused_id_collision_refused :
    applyRecord (historySchema Nat Nat) afterRootCursor forgedRoot = none := by decide

theorem missing_parent_refused :
    applyRecord (historySchema Nat Nat) (emptyHistoryCursor Nat Nat) orphanEvent =
      none := by decide

def forkJournal : List (Event Nat Nat) := [rootEvent, leftEvent, rightEvent]

def rootCheckpoint : HistoryCheckpoint Nat Nat where
  consumed := 1
  cursor := afterRootCursor

theorem rootCheckpoint_valid :
    CheckpointValid (historySchema Nat Nat) (emptyHistoryCursor Nat Nat)
      forkJournal rootCheckpoint := by
  constructor <;> decide

theorem rootCheckpoint_executes :
    validateCheckpoint (historySchema Nat Nat) (emptyHistoryCursor Nat Nat)
      forkJournal rootCheckpoint = true := by decide

theorem fork_checkpoint_suffix_exact :
    replay (historySchema Nat Nat) rootCheckpoint.cursor
        (forkJournal.drop rootCheckpoint.consumed) =
      replay (historySchema Nat Nat) (emptyHistoryCursor Nat Nat) forkJournal :=
  checkpoint_suffix_replay forkJournal rootCheckpoint rootCheckpoint_valid

def leftFirstState : EventState Nat Nat := ⟨[rootEvent, leftEvent, rightEvent]⟩
def rightFirstState : EventState Nat Nat := ⟨[rootEvent, rightEvent, leftEvent]⟩

/-- Two legal arrival orders materialize different chronological lists but the
same full event set. -/
theorem fork_arrival_orders_converge :
    replay (historySchema Nat Nat) (emptyHistoryCursor Nat Nat)
        [rootEvent, leftEvent, rightEvent] =
        some ⟨leftFirstState, [rootEvent, leftEvent, rightEvent]⟩ ∧
      replay (historySchema Nat Nat) (emptyHistoryCursor Nat Nat)
        [rootEvent, rightEvent, leftEvent] =
        some ⟨rightFirstState, [rootEvent, rightEvent, leftEvent]⟩ ∧
      SameEventSet leftFirstState rightFirstState := by
  constructor
  · decide
  constructor
  · decide
  · intro event
    simp only [leftFirstState, rightFirstState, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · intro member
      rcases member with root | left | right
      · exact Or.inl root
      · exact Or.inr (Or.inr left)
      · exact Or.inr (Or.inl right)
    · intro member
      rcases member with root | right | left
      · exact Or.inl root
      · exact Or.inr (Or.inr right)
      · exact Or.inr (Or.inl left)

/-! ## Stable-id buffered delivery replay -/

/-- The authoritative record list keeps arrival order, while `DeliveryState`
retains the causally materialized set and its explicitly bounded pending set.
Exact retries and nonce collisions remain handled by `applyRecord`. -/
def deliverySchema (Id Payload : Type) [DecidableEq Id] [DecidableEq Payload] :
    RecordSchema (DeliveryState Id Payload) (Event Id Payload) Id where
  nonce := Event.id
  step state event :=
    match receive state event with
    | .delivered next | .buffered next => some next
    | .retry _ => none
    | .collision _ => none
    | .bufferFull _ => none
    | .selfParent => none
    | .duplicateParent => none

abbrev DeliveryCursor (Id Payload : Type) :=
  Cursor (DeliveryState Id Payload) (Event Id Payload)

abbrev DeliveryCheckpoint (Id Payload : Type) :=
  CheckpointData (DeliveryState Id Payload) (Event Id Payload)

/-- A resumable cursor must agree extensionally about all accepted arrival
records: each is either causally materialized or explicitly pending, and there
are no unjournaled events in either runtime store. `deliverySchema` itself is
total on arbitrary structures, but public resume claims require this predicate
or generic `CheckpointValid`. -/
def DeliveryCursorCoherent {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (cursor : DeliveryCursor Id Payload) : Prop :=
  DeliveryValid cursor.state ∧
    ∀ event, event ∈ cursor.accepted ↔
      event ∈ cursor.state.materialized.accepted ∨
      event ∈ cursor.state.pending

def emptyDeliveryCursor (Id Payload : Type) (capacity : Nat) :
    DeliveryCursor Id Payload :=
  emptyCursor (DeliveryState.empty Id Payload capacity)

/-- Typed callback boundary for a durable-arrival host adapter.

The proof fields require a callback to agree with authoritative single-record
admission and full arrival replay. They deliberately say nothing about codecs,
checksums, I/O, or crash durability. A Rust/FFI implementation must establish
that separate representation relation before this contract can be used as a
refinement theorem. -/
structure DurableArrivalCallbacks (Id Payload : Type)
    [DecidableEq Id] [DecidableEq Payload] where
  receive : DeliveryCursor Id Payload → Event Id Payload →
    Option (DeliveryCursor Id Payload)
  reopen : Nat → List (Event Id Payload) →
    Option (DeliveryCursor Id Payload)
  receive_eq : ∀ cursor event,
    receive cursor event = applyRecord (deliverySchema Id Payload) cursor event
  reopen_eq : ∀ capacity arrivals,
    reopen capacity arrivals = replay (deliverySchema Id Payload)
      (emptyDeliveryCursor Id Payload capacity) arrivals

/-- The Lean schema itself supplies the reference implementation of the host
callback contract. -/
def schemaArrivalCallbacks (Id Payload : Type)
    [DecidableEq Id] [DecidableEq Payload] :
    DurableArrivalCallbacks Id Payload where
  receive := applyRecord (deliverySchema Id Payload)
  reopen := fun capacity => replay (deliverySchema Id Payload)
    (emptyDeliveryCursor Id Payload capacity)
  receive_eq := fun _ _ => rfl
  reopen_eq := fun _ _ => rfl

theorem emptyDeliveryCursor_coherent (Id Payload : Type)
    [DecidableEq Id] [DecidableEq Payload] (capacity : Nat) :
    DeliveryCursorCoherent (emptyDeliveryCursor Id Payload capacity) := by
  simp [DeliveryCursorCoherent, DeliveryValid, emptyDeliveryCursor, emptyCursor,
    DeliveryState.empty, EventState.empty]

theorem deliverySchema_step_eq_some_iff {Id Payload : Type}
    [DecidableEq Id] [DecidableEq Payload]
    (state next : DeliveryState Id Payload) (event : Event Id Payload) :
    (deliverySchema Id Payload).step state event = some next ↔
      receive state event = .delivered next ∨
      receive state event = .buffered next := by
  cases decision : receive state event <;>
    simp [deliverySchema, decision]

def stableCausalCursor : DeliveryCursor Nat String :=
  ⟨runtimeCausalState, runtimeCausalOrder⟩

def stableReverseCursor : DeliveryCursor Nat String :=
  ⟨runtimeReverseSettledState, runtimeReverseOrder⟩

theorem stable_causal_replay_exact :
    replay (deliverySchema Nat String) (emptyDeliveryCursor Nat String 5)
      runtimeCausalOrder = some stableCausalCursor := rfl

theorem stable_reverse_replay_exact :
    replay (deliverySchema Nat String) (emptyDeliveryCursor Nat String 5)
      runtimeReverseOrder = some stableReverseCursor := rfl

/-- Every host callback implementation of the typed contract must recover the
same reverse-order fixture cursor. This is a callback-level obligation, not a
claim that the current Rust wire has been related to Lean values. -/
theorem durableCallbacks_reverse_reopen_exact
    (callbacks : DurableArrivalCallbacks Nat String) :
    callbacks.reopen 5 runtimeReverseOrder =
      some stableReverseCursor := by
  rw [callbacks.reopen_eq]
  exact stable_reverse_replay_exact

theorem stableCausalCursor_coherent :
    DeliveryCursorCoherent stableCausalCursor := by
  constructor
  · change [].length ≤ 5
    decide
  · intro event
    simp [stableCausalCursor, runtimeCausalState]

theorem stableReverseCursor_coherent :
    DeliveryCursorCoherent stableReverseCursor := by
  constructor
  · exact runtime_reverse_order_respects_capacity
  · intro event
    simp [stableReverseCursor, runtimeReverseSettledState, runtimeReverseOrder,
      or_comm, or_left_comm]

theorem stable_replays_converge :
    SettledSameEventSet stableCausalCursor.state stableReverseCursor.state :=
  runtime_orders_converge

/-- A checkpoint may retain unresolved buffered events. Validation still uses
the authoritative arrival prefix; resumption later drains them when their
parents arrive. -/
def stableReversePrefixState : DeliveryState Nat String :=
  ⟨EventState.empty, [runtimeTip, runtimeMergeRight, runtimeMergeLeft], 5⟩

def stableReversePrefixCursor : DeliveryCursor Nat String :=
  ⟨stableReversePrefixState,
    [runtimeTip, runtimeMergeRight, runtimeMergeLeft]⟩

def stableReverseCheckpoint : DeliveryCheckpoint Nat String where
  consumed := 3
  cursor := stableReversePrefixCursor

theorem stableReversePrefixCursor_coherent :
    DeliveryCursorCoherent stableReversePrefixCursor := by
  constructor
  · change 3 ≤ 5
    decide
  · intro event
    simp [stableReversePrefixCursor, stableReversePrefixState, EventState.empty]

theorem stableReverseCheckpoint_valid :
    CheckpointValid (deliverySchema Nat String)
      (emptyDeliveryCursor Nat String 5) runtimeReverseOrder
      stableReverseCheckpoint := by
  exact ⟨by decide, rfl⟩

theorem stable_reverse_checkpoint_suffix_exact :
    replay (deliverySchema Nat String) stableReverseCheckpoint.cursor
        (runtimeReverseOrder.drop stableReverseCheckpoint.consumed) =
      replay (deliverySchema Nat String) (emptyDeliveryCursor Nat String 5)
        runtimeReverseOrder :=
  checkpoint_suffix_replay_equiv _ _ _ _ stableReverseCheckpoint_valid

end Uwueave.PersistentHistoryRuntime
