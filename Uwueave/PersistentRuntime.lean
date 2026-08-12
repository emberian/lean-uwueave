/-
# Uwueave.PersistentRuntime — authoritative logs and atomic batch recovery

This module states the durability contract needed by a document runtime without
pretending to prove a filesystem implementation.  The authority is an
append-only list of operations/events.  A deterministic replay machine checks
each new record, remembers the complete record attached to every accepted
nonce, makes an exact retry a no-op, and refuses nonce reuse with different
content.

Atomicity is an observation contract on the authoritative log:

* a successful commit reopens as `old ++ batch`;
* an unsuccessful or crash-ambiguous commit reopens as either `old` or
  `old ++ batch`;
* consequently no partial, reordered, or invented suffix is admitted.

Checkpoints are non-authoritative accelerators.  A checkpoint candidate carries
an offset and replay cursor; it is accepted only when replaying exactly the
corresponding log prefix reconstructs that cursor.  The central checkpoint
theorem then proves replay from the checked cursor over the remaining suffix is
equal to replaying the whole authoritative log.  Derived caches are even
weaker: they are deliberately absent from `reopenImage`.

Everything here is a pure logical/executable model over `List`.  No result in
this file claims anything about file descriptors, flush calls, rename, locking,
checksums, BLAKE3, redb, sectors, or power-loss behavior.  A host implementation
must establish the atomic observation premise and refine its parser/serializer
to the chosen record type.
-/
import Std

namespace Uwueave.PersistentRuntime

set_option autoImplicit false

/-! ## §1. Deterministic checked replay with idempotent nonces -/

/-- A runtime record schema.  `step` is the complete semantic admission and
transition function: `none` refuses a record, while `some next` accepts it.
Because it is a function, replay is deterministic by construction. -/
structure RecordSchema (State : Type) (Record : Type) (Nonce : Type) where
  nonce : Record → Nonce
  step : State → Record → Option State

/-- The authoritative replay cursor.  `accepted` is retained in chronological
order so nonce reuse can be checked without trusting a derived index. -/
structure Cursor (State : Type) (Record : Type) where
  state : State
  accepted : List Record
  deriving DecidableEq, Repr

/-- Start replay with no authoritative records. -/
def emptyCursor {State Record : Type} (initial : State) : Cursor State Record :=
  ⟨initial, []⟩

/-- One checked append.

An exact record retry is idempotent.  A fresh record is admitted by `step` and
appended to the authoritative history.  A distinct record reusing an accepted
nonce is refused; nonce identity alone never licenses different content. -/
def applyRecord {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) (record : Record) :
    Option (Cursor State Record) :=
  if record ∈ cursor.accepted then
    some cursor
  else if ∃ prior ∈ cursor.accepted, M.nonce prior = M.nonce record then
    none
  else
    match M.step cursor.state record with
    | none => none
    | some next => some ⟨next, cursor.accepted ++ [record]⟩

/-- Deterministic replay in journal order.  The first refused record refuses the
whole supplied suffix; replay never skips an invalid middle record. -/
def replay {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce) :
    Cursor State Record → List Record → Option (Cursor State Record)
  | cursor, [] => some cursor
  | cursor, record :: rest => do
      let next ← applyRecord M cursor record
      replay M next rest

/-- Authoritative nonce coherence: two accepted records carrying one nonce are
the same complete record.  This is the invariant that separates idempotent
retry from conflicting nonce reuse. -/
def NonceCoherent {State Record Nonce : Type}
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) : Prop :=
  ∀ left, left ∈ cursor.accepted →
    ∀ right, right ∈ cursor.accepted →
      M.nonce left = M.nonce right → left = right

theorem emptyCursor_nonceCoherent {State Record Nonce : Type}
    (M : RecordSchema State Record Nonce) (initial : State) :
    NonceCoherent M (emptyCursor initial : Cursor State Record) := by
  intro left impossible
  simp [emptyCursor] at impossible

/-- Exact retries are no-ops, including after reopen. -/
theorem applyRecord_retry {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) (record : Record)
    (known : record ∈ cursor.accepted) :
    applyRecord M cursor record = some cursor := by
  simp [applyRecord, known]

/-- Exact conflict rule with its necessary premise: the different record is
not itself already authoritative.  Cursors produced from `emptyCursor` by
successful replay satisfy this condition for a newly presented conflict.  Thus
a reused nonce with different content is refused rather than treated as an
idempotent retry. -/
theorem applyRecord_nonce_conflict_of_not_mem {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) (record prior : Record)
    (notKnown : record ∉ cursor.accepted)
    (known : prior ∈ cursor.accepted)
    (sameNonce : M.nonce prior = M.nonce record) :
    applyRecord M cursor record = none := by
  have collision : ∃ prior' ∈ cursor.accepted,
      M.nonce prior' = M.nonce record :=
    ⟨prior, known, sameNonce⟩
  simp [applyRecord, notKnown, collision]

/-- On a coherent cursor, different content with a reused nonce is
unconditionally a conflict: coherence derives the required non-membership. -/
theorem applyRecord_nonce_conflict {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) (record prior : Record)
    (coherent : NonceCoherent M cursor)
    (different : record ≠ prior) (known : prior ∈ cursor.accepted)
    (sameNonce : M.nonce prior = M.nonce record) :
    applyRecord M cursor record = none := by
  apply applyRecord_nonce_conflict_of_not_mem M cursor record prior
  · intro recordKnown
    exact different (coherent record recordKnown prior known sameNonce.symm)
  · exact known
  · exact sameNonce

/-- A fresh admitted record extends the authoritative history by exactly one
record and uses exactly the schema transition. -/
theorem applyRecord_fresh {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) (record : Record)
    (notKnown : record ∉ cursor.accepted)
    (freshNonce : ¬ ∃ prior ∈ cursor.accepted,
      M.nonce prior = M.nonce record)
    {next : State} (admitted : M.step cursor.state record = some next) :
    applyRecord M cursor record =
      some ⟨next, cursor.accepted ++ [record]⟩ := by
  simp [applyRecord, notKnown, freshNonce, admitted]

/-- Replay is compositional across list concatenation. -/
theorem replay_append {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) (left right : List Record) :
    replay M cursor (left ++ right) =
      (replay M cursor left).bind (fun afterLeft => replay M afterLeft right) := by
  induction left generalizing cursor with
  | nil => rfl
  | cons record rest ih =>
      simp only [List.cons_append, replay]
      cases h : applyRecord M cursor record with
      | none => rfl
      | some next => exact ih next

/-- Records already present in the authoritative cursor replay as pure retries. -/
def AllKnown {State Record : Type}
    (cursor : Cursor State Record) (records : List Record) : Prop :=
  ∀ record, record ∈ records → record ∈ cursor.accepted

theorem replay_allKnown {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (cursor : Cursor State Record) (records : List Record)
    (known : AllKnown cursor records) :
    replay M cursor records = some cursor := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp only [replay]
      rw [applyRecord_retry M cursor record (known record (by simp))]
      exact ih (fun item hmem => known item (by simp [hmem]))

/-- One successful application preserves every prior authoritative record and
makes the applied record authoritative. -/
theorem applyRecord_success_extends {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {before after : Cursor State Record} {record : Record}
    (success : applyRecord M before record = some after) :
    (∀ item, item ∈ before.accepted → item ∈ after.accepted) ∧
      record ∈ after.accepted := by
  by_cases known : record ∈ before.accepted
  · simp [applyRecord, known] at success
    subst after
    exact ⟨fun _ h => h, known⟩
  · by_cases collision : ∃ prior ∈ before.accepted,
      M.nonce prior = M.nonce record
    · simp [applyRecord, known, collision] at success
    · cases admitted : M.step before.state record with
      | none => simp [applyRecord, known, collision, admitted] at success
      | some next =>
          simp [applyRecord, known, collision, admitted] at success
          subst after
          exact ⟨
            fun item h => List.mem_append_left [record] h,
            List.mem_append_right before.accepted (by simp)⟩

/-- Successful checked application preserves nonce coherence. -/
theorem applyRecord_success_nonceCoherent {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {before after : Cursor State Record} {record : Record}
    (coherent : NonceCoherent M before)
    (success : applyRecord M before record = some after) :
    NonceCoherent M after := by
  by_cases known : record ∈ before.accepted
  · simp [applyRecord, known] at success
    subst after
    exact coherent
  · by_cases collision : ∃ prior ∈ before.accepted,
      M.nonce prior = M.nonce record
    · simp [applyRecord, known, collision] at success
    · cases admitted : M.step before.state record with
      | none => simp [applyRecord, known, collision, admitted] at success
      | some next =>
          simp [applyRecord, known, collision, admitted] at success
          subst after
          intro left leftMem right rightMem sameNonce
          simp only [List.mem_append, List.mem_singleton] at leftMem rightMem
          rcases leftMem with leftOld | rfl <;>
            rcases rightMem with rightOld | rfl
          · exact coherent left leftOld right rightOld sameNonce
          · exact False.elim (collision ⟨left, leftOld, sameNonce⟩)
          · exact False.elim (collision ⟨right, rightOld, sameNonce.symm⟩)
          · rfl

/-- Successful replay preserves the prior authoritative history and makes every
record in the supplied suffix authoritative. -/
theorem replay_success_extends_and_knows {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {before after : Cursor State Record} {records : List Record}
    (success : replay M before records = some after) :
    (∀ item, item ∈ before.accepted → item ∈ after.accepted) ∧
      AllKnown after records := by
  induction records generalizing before after with
  | nil =>
      simp only [replay] at success
      cases success
      exact ⟨fun _ h => h, fun _ h => False.elim (by simp at h)⟩
  | cons record rest ih =>
      cases applied : applyRecord M before record with
      | none => simp [replay, applied] at success
      | some middle =>
          have tailSuccess : replay M middle rest = some after := by
            simpa [replay, applied] using success
          obtain ⟨firstExtends, recordKnown⟩ :=
            applyRecord_success_extends M applied
          obtain ⟨tailExtends, restKnown⟩ := ih tailSuccess
          constructor
          · intro item hmem
            exact tailExtends item (firstExtends item hmem)
          · intro item hmem
            rcases List.mem_cons.mp hmem with head | htail
            · subst item
              exact tailExtends _ recordKnown
            · exact restKnown item htail

/-- Successful deterministic replay preserves nonce coherence. -/
theorem replay_success_nonceCoherent {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {before after : Cursor State Record} {records : List Record}
    (coherent : NonceCoherent M before)
    (success : replay M before records = some after) :
    NonceCoherent M after := by
  induction records generalizing before after with
  | nil =>
      simp only [replay] at success
      cases success
      exact coherent
  | cons record rest ih =>
      cases applied : applyRecord M before record with
      | none => simp [replay, applied] at success
      | some middle =>
          have middleCoherent :=
            applyRecord_success_nonceCoherent M coherent applied
          have tailSuccess : replay M middle rest = some after := by
            simpa [replay, applied] using success
          exact ih middleCoherent tailSuccess

/-- Every cursor reconstructed successfully from the empty authoritative
history satisfies nonce coherence. -/
theorem replay_from_empty_nonceCoherent {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {initial : State} {after : Cursor State Record} {records : List Record}
    (success : replay M (emptyCursor initial) records = some after) :
    NonceCoherent M after :=
  replay_success_nonceCoherent M (emptyCursor_nonceCoherent M initial) success

/-- Named determinism hook: a fixed schema, cursor, and journal cannot replay
to two different cursors. -/
theorem replay_deterministic {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {before left right : Cursor State Record} {records : List Record}
    (toLeft : replay M before records = some left)
    (toRight : replay M before records = some right) :
    left = right := by
  rw [toLeft] at toRight
  exact Option.some.inj toRight

/-- Retrying an entire successfully replayed suffix is idempotent, not merely
retrying one record. -/
theorem replay_success_retry {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {before after : Cursor State Record} {records : List Record}
    (success : replay M before records = some after) :
    replay M after records = some after :=
  replay_allKnown M after records
    (replay_success_extends_and_knows M success).2

/-! ## §2. Checked batches and exact atomic observations -/

/-- Evidence that both the old authoritative log and the complete proposed
batch replay successfully.  This proves semantic admission; it does not prove a
host storage operation is atomic. -/
structure CheckedBatch {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (initial : Cursor State Record) (old batch : List Record) where
  before : Cursor State Record
  after : Cursor State Record
  old_checked : replay M initial old = some before
  batch_checked : replay M before batch = some after

/-- A checked batch gives the full-log replay equation used after a successful
atomic observation. -/
theorem CheckedBatch.full_checked {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    {M : RecordSchema State Record Nonce}
    {initial : Cursor State Record} {old batch : List Record}
    (checked : CheckedBatch M initial old batch) :
    replay M initial (old ++ batch) = some checked.after := by
  rw [replay_append, checked.old_checked]
  exact checked.batch_checked

/-- The only two authoritative images allowed after an unsuccessful or
crash-ambiguous atomic batch attempt. -/
inductive AtomicBatchObservation {Record : Type}
    (old batch : List Record) : List Record → Prop where
  | before : AtomicBatchObservation old batch old
  | after : AtomicBatchObservation old batch (old ++ batch)

/-- A reported successful commit has the single post-commit observation. -/
def SuccessfulBatchObservation {Record : Type}
    (old batch reopened : List Record) : Prop :=
  reopened = old ++ batch

/-- The inductive observation contract is exactly a two-element alternative. -/
theorem atomicBatchObservation_iff {Record : Type}
    (old batch reopened : List Record) :
    AtomicBatchObservation old batch reopened ↔
      reopened = old ∨ reopened = old ++ batch := by
  constructor
  · intro observed
    cases observed with
    | before => exact Or.inl rfl
    | after => exact Or.inr rfl
  · intro observed
    rcases observed with rfl | rfl
    · exact .before
    · exact .after

/-- Success reopens as the complete append, exactly. -/
theorem successful_reopen_exact {Record : Type}
    {old batch reopened : List Record}
    (success : SuccessfulBatchObservation old batch reopened) :
    reopened = old ++ batch := success

/-- Failure/crash ambiguity changes only whether the entire suffix is visible;
the suffix is never partial, reordered, or invented. -/
theorem atomic_suffix_exact {Record : Type}
    {old batch reopened : List Record}
    (observed : AtomicBatchObservation old batch reopened) :
    ∃ suffix, reopened = old ++ suffix ∧ (suffix = [] ∨ suffix = batch) := by
  cases observed with
  | before => exact ⟨[], by simp, Or.inl rfl⟩
  | after => exact ⟨batch, rfl, Or.inr rfl⟩

/-- If an atomic observation differs from the old image, it is the complete
post-commit image. -/
theorem atomic_after_of_changed {Record : Type}
    {old batch reopened : List Record}
    (observed : AtomicBatchObservation old batch reopened)
    (changed : reopened ≠ old) :
    reopened = old ++ batch := by
  rcases (atomicBatchObservation_iff old batch reopened).mp observed with
    before | after
  · exact False.elim (changed before)
  · exact after

/-- A checked batch plus an atomic observation replays to exactly the old state
or the complete new state—never the state of a strict batch prefix. -/
theorem checked_atomic_reopen {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    {initial : Cursor State Record} {old batch reopened : List Record}
    (checked : CheckedBatch M initial old batch)
    (observed : AtomicBatchObservation old batch reopened) :
    replay M initial reopened = some checked.before ∨
      replay M initial reopened = some checked.after := by
  cases observed with
  | before => exact Or.inl checked.old_checked
  | after =>
      right
      rw [replay_append, checked.old_checked]
      exact checked.batch_checked

/-! ## §3. Checked checkpoints and non-authoritative caches -/

/-- Host-shaped checkpoint data.  `consumed` is an authoritative-log offset;
`cursor` is only a candidate until `CheckpointValid` is checked. -/
structure CheckpointData (State : Type) (Record : Type) where
  consumed : Nat
  cursor : Cursor State Record
  deriving DecidableEq, Repr

/-- A checkpoint is valid exactly when its offset is in range and deterministic
replay of that authoritative prefix reconstructs its cursor. -/
def CheckpointValid {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (initial : Cursor State Record) (journal : List Record)
    (checkpoint : CheckpointData State Record) : Prop :=
  checkpoint.consumed ≤ journal.length ∧
    replay M initial (journal.take checkpoint.consumed) =
      some checkpoint.cursor

/-- Executable checkpoint validation hook for a pure-Rust implementation. -/
def validateCheckpoint {State Record Nonce : Type}
    [DecidableEq State] [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (initial : Cursor State Record) (journal : List Record)
    (checkpoint : CheckpointData State Record) : Bool :=
  decide (checkpoint.consumed ≤ journal.length) &&
    decide (replay M initial (journal.take checkpoint.consumed) =
      some checkpoint.cursor)

theorem validateCheckpoint_eq_true_iff {State Record Nonce : Type}
    [DecidableEq State] [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (initial : Cursor State Record) (journal : List Record)
    (checkpoint : CheckpointData State Record) :
    validateCheckpoint M initial journal checkpoint = true ↔
      CheckpointValid M initial journal checkpoint := by
  simp [validateCheckpoint, CheckpointValid]

/-- **Checkpoint + suffix replay equivalence.**  Once the candidate is checked,
resuming at its cursor is exactly full replay of the authoritative journal. -/
theorem checkpoint_suffix_replay_equiv {State Record Nonce : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (initial : Cursor State Record) (journal : List Record)
    (checkpoint : CheckpointData State Record)
    (valid : CheckpointValid M initial journal checkpoint) :
    replay M checkpoint.cursor (journal.drop checkpoint.consumed) =
      replay M initial journal := by
  calc
    replay M checkpoint.cursor (journal.drop checkpoint.consumed) =
        (replay M initial (journal.take checkpoint.consumed)).bind
          (fun afterPrefix =>
            replay M afterPrefix (journal.drop checkpoint.consumed)) := by
              rw [valid.2]
              rfl
    _ = replay M initial
          (journal.take checkpoint.consumed ++
            journal.drop checkpoint.consumed) := by
              rw [replay_append]
    _ = replay M initial journal := by
          rw [List.take_append_drop]

/-- A cache is a projection, never replay authority. -/
structure RuntimeImage (Record : Type) (View : Type) where
  journal : List Record
  cache : Option View

/-- Reopen consults only the authoritative journal. -/
def reopenImage {State Record Nonce View : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (initial : Cursor State Record) (image : RuntimeImage Record View) :
    Option (Cursor State Record) :=
  replay M initial image.journal

/-- Changing, dropping, or corrupting only a derived cache cannot change the
logical reopen result. -/
theorem reopenImage_cache_irrelevant {State Record Nonce View : Type}
    [DecidableEq Record] [DecidableEq Nonce]
    (M : RecordSchema State Record Nonce)
    (initial : Cursor State Record) (journal : List Record)
    (left right : Option View) :
    reopenImage M initial ⟨journal, left⟩ =
      reopenImage M initial ⟨journal, right⟩ := rfl

/-! ## §4. Executable negative witnesses -/

/-- Tiny records for the two recovery counterexamples. -/
structure CounterRecord where
  nonce : Nat
  amount : Nat
  deriving DecidableEq, Repr

/-- A deterministic counter schema; all fresh records are admitted. -/
def counterSchema : RecordSchema Nat CounterRecord Nat where
  nonce := CounterRecord.nonce
  step state record := some (state + record.amount)

def first : CounterRecord := ⟨7, 1⟩
def second : CounterRecord := ⟨8, 1⟩
def alternateFirst : CounterRecord := ⟨9, 1⟩

/-- The complete two-record batch preserves the even-state invariant. -/
theorem complete_pair_replays_to_two :
    replay counterSchema (emptyCursor 0) [first, second] =
      some ⟨2, [first, second]⟩ := by
  decide

/-- Its strict one-record prefix violates that invariant. -/
theorem partial_pair_replays_to_one :
    replay counterSchema (emptyCursor 0) [first] =
      some ⟨1, [first]⟩ := by
  decide

theorem complete_pair_even : 2 % 2 = 0 := by decide
theorem partial_pair_not_even : 1 % 2 ≠ 0 := by decide

/-- Concrete proof that exposing the strict prefix is outside the atomic batch
contract, not an allowed crash outcome. -/
theorem strict_prefix_not_atomic :
    ¬ AtomicBatchObservation [] [first, second] [first] := by
  intro observed
  rcases (atomicBatchObservation_iff [] [first, second] [first]).mp observed with
    before | after
  · simp [first] at before
  · simp [first, second] at after

/-- Two histories can have the same materialized state while retaining
different authoritative nonce knowledge. -/
theorem snapshot_collision :
    ∃ left right : Cursor Nat CounterRecord,
      replay counterSchema (emptyCursor 0) [first] = some left ∧
      replay counterSchema (emptyCursor 0) [alternateFirst] = some right ∧
      left.state = right.state ∧
      replay counterSchema left [first] ≠ replay counterSchema right [first] := by
  refine ⟨⟨1, [first]⟩, ⟨1, [alternateFirst]⟩, ?_, ?_, rfl, ?_⟩
  · decide
  · decide
  · decide

/-- Therefore the materialized snapshot alone is insufficient recovery
authority: retry behavior depends on the authoritative record identities. -/
theorem snapshot_only_recovery_unsafe :
    ∃ left right : Cursor Nat CounterRecord,
      left.state = right.state ∧
      replay counterSchema left [first] = some left ∧
      replay counterSchema right [first] =
        some ⟨2, [alternateFirst, first]⟩ := by
  exact ⟨⟨1, [first]⟩, ⟨1, [alternateFirst]⟩, rfl, by decide, by decide⟩

end Uwueave.PersistentRuntime
