/-
# Uwueave.PersistentHistoryRuntime -- causal history on checked replay

This module instantiates `PersistentRuntime.RecordSchema` with the causal event
admission function from `HistoryRuntime`.  The authoritative cursor therefore
retains both the materialized event state and the complete chronological record
list: exact retries are no-ops, identifier reuse with different content is a
nonce collision, and a fresh child is admitted only after every parent.

Checkpoints are the generic checked prefix cursors from `PersistentRuntime`.
They are accelerators, not authority; the suffix theorem below is the existing
full-replay equality specialized to causal history events.

No theorem here claims a filesystem, network endpoint, out-of-order buffer,
authentication, or infinite-history enumeration.  The pure-Rust
`HistoryJournal` supplies one concrete checksummed host rung separately.
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

end Uwueave.PersistentHistoryRuntime
