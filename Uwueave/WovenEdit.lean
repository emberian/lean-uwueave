/-
# Uwueave.WovenEdit — checked local edits preserve woven well-formedness

`Wellformed.lean` proves that merge preserves the six structural invariants
of a woven document.  This module supplies the missing local half: a small,
typed edit calculus whose constructors expose exactly the facts needed by the
write path, a decidable checker for untrusted commands, and finite-script
semantics that cannot step through a malformed intermediate document.

The supported subset is intentionally small but operational:

* create a fresh node together with its first register write;
* add a per-user bookmark reference, only to an existing node;
* append an ordinary register write to an existing node; and
* append a tombstone marker to an existing node.

A tombstone is the distinguished register value `0`.  It is a logical,
monotone marker, not physical deletion or garbage collection.  Text insertion,
pin mutation, grant mutation, horizon advancement, and sequence-kernel
tombstones are not operations of this calculus.  In particular, nothing here
claims cross-tree hole safety.
-/
import Uwueave.Wellformed

namespace Uwueave.WovenEdit

open Uwueave Uwueave.Catalog Uwueave.Causality Uwueave.MVRegister Uwueave.Spec
open Uwueave.Wellformed

/-! ## State transformers -/

/-- Insert one element into a grow-only set. -/
def insertG [DecidableEq α] (s : GSet α) (a : α) : GSet α :=
  fun x => if x = a then true else s x

@[simp] theorem insertG_apply [DecidableEq α] (s : GSet α) (a x : α) :
    insertG s a x = true ↔ s x = true ∨ x = a := by
  by_cases h : x = a <;> simp [insertG, h]

/-- Add one write at one node, leaving all other registers unchanged. -/
def addWrite (cts : NodeId → MVReg) (node : NodeId) (w : Write) : NodeId → MVReg :=
  fun k => if k = node then insertG (cts k) w else cts k

/-- Add one bookmark for one user, leaving all other users unchanged. -/
def addBookmark (bms : User → GSet NodeId) (user : User) (node : NodeId) :
    User → GSet NodeId :=
  fun u => if u = user then insertG (bms u) node else bms u

/-- Rebuild only the three fields edited here.  Activation, authority, pins,
quota, text, and horizon are copied definitionally from the input document. -/
def rebuild (d : WovenDoc) (ns : GSet NodeId) (bms : User → GSet NodeId)
    (cts : NodeId → MVReg) : WovenDoc :=
  ((((ns, bms), (cts, d.1.1.2.2)), d.1.2), d.2)

/-- Creation grows the node set and appends its initial content write. -/
def createState (d : WovenDoc) (node value : Nat) (clock : Clock) : WovenDoc :=
  rebuild d (insertG (nodes d) node) (bookmarks d)
    (addWrite (contents d) node (value, clock))

/-- A reference edit grows one user's bookmark set. -/
def referenceState (d : WovenDoc) (user : User) (node : Nat) : WovenDoc :=
  rebuild d (nodes d) (addBookmark (bookmarks d) user node) (contents d)

/-- An update appends a write; old and concurrent values remain in the
multi-value register and its derived view decides what is visible. -/
def updateState (d : WovenDoc) (node value : Nat) (clock : Clock) : WovenDoc :=
  rebuild d (nodes d) (bookmarks d)
    (addWrite (contents d) node (value, clock))

/-- The reserved register payload for a logical tombstone. -/
def tombstoneValue : Nat := 0

/-- Tombstoning is a distinguished ordinary write, not physical erasure. -/
def tombstoneState (d : WovenDoc) (node : Nat) (clock : Clock) : WovenDoc :=
  updateState d node tombstoneValue clock

@[simp] theorem nodes_rebuild (d : WovenDoc) (ns : GSet NodeId)
    (bms : User → GSet NodeId) (cts : NodeId → MVReg) :
    nodes (rebuild d ns bms cts) = ns := rfl

@[simp] theorem bookmarks_rebuild (d : WovenDoc) (ns : GSet NodeId)
    (bms : User → GSet NodeId) (cts : NodeId → MVReg) :
    bookmarks (rebuild d ns bms cts) = bms := rfl

@[simp] theorem contents_rebuild (d : WovenDoc) (ns : GSet NodeId)
    (bms : User → GSet NodeId) (cts : NodeId → MVReg) :
    contents (rebuild d ns bms cts) = cts := rfl

@[simp] theorem pins_rebuild (d : WovenDoc) (ns : GSet NodeId)
    (bms : User → GSet NodeId) (cts : NodeId → MVReg) :
    pins (rebuild d ns bms cts) = pins d := rfl

@[simp] theorem text_rebuild (d : WovenDoc) (ns : GSet NodeId)
    (bms : User → GSet NodeId) (cts : NodeId → MVReg) :
    text (rebuild d ns bms cts) = text d := rfl

@[simp] theorem horizon_rebuild (d : WovenDoc) (ns : GSet NodeId)
    (bms : User → GSet NodeId) (cts : NodeId → MVReg) :
    horizon (rebuild d ns bms cts) = horizon d := rfl

@[simp] theorem grants_rebuild (d : WovenDoc) (ns : GSet NodeId)
    (bms : User → GSet NodeId) (cts : NodeId → MVReg) :
    grants (rebuild d ns bms cts) = grants d := rfl

/-! ## Typed edits and the untrusted command boundary -/

/-- A checked edit from the particular document `d`.  The constructor fields
are the write-path obligations: freshness for create, referential existence,
and a clock no later than the document horizon. -/
inductive Edit (n root : Nat) (d : WovenDoc) : Type where
  | create (node value : Nat) (clock : Clock)
      (fresh : nodes d node = false)
      (clockOk : Clock.le clock (horizon d)) : Edit n root d
  | reference (user : User) (node : Nat)
      (hExists : nodes d node = true) : Edit n root d
  | update (node value : Nat) (clock : Clock)
      (hExists : nodes d node = true)
      (notTombstone : value ≠ tombstoneValue)
      (clockOk : Clock.le clock (horizon d)) : Edit n root d
  | tombstone (node : Nat) (clock : Clock)
      (hExists : nodes d node = true)
      (clockOk : Clock.le clock (horizon d)) : Edit n root d

/-- Total interpretation of a typed edit. -/
def apply {n root : Nat} {d : WovenDoc} : Edit n root d → WovenDoc
  | .create node value clock _ _ => createState d node value clock
  | .reference user node _ => referenceState d user node
  | .update node value clock _ _ _ => updateState d node value clock
  | .tombstone node clock _ _ => tombstoneState d node clock

/-- Data accepted from an untrusted caller. -/
inductive Command where
  | create (node value : Nat) (clock : Clock)
  | reference (user : User) (node : Nat)
  | update (node value : Nat) (clock : Clock)
  | tombstone (node : Nat) (clock : Clock)
deriving Repr, DecidableEq

/-- Check a raw command against the current state, producing a typed edit only
when every constructor premise is available. -/
def check (n root : Nat) (d : WovenDoc) : Command → Option (Edit n root d)
  | .create node value clock =>
      if hfresh : nodes d node = false then
        if hc : Clock.le clock (horizon d) then
          some (.create node value clock hfresh hc)
        else none
      else none
  | .reference user node =>
      if hex : nodes d node = true then some (.reference user node hex) else none
  | .update node value clock =>
      if hex : nodes d node = true then
        if hv : value ≠ tombstoneValue then
          if hc : Clock.le clock (horizon d) then
            some (.update node value clock hex hv hc)
          else none
        else none
      else none
  | .tombstone node clock =>
      if hex : nodes d node = true then
        if hc : Clock.le clock (horizon d) then
          some (.tombstone node clock hex hc)
        else none
      else none

/-! ## Single-step preservation -/

private theorem old_mem_insertG [DecidableEq α] {s : GSet α} {a x : α}
    (h : s x = true) : insertG s a x = true :=
  (insertG_apply s a x).2 (Or.inl h)

theorem create_preserves {n root : Nat} {d : WovenDoc}
    (hd : WellFormed n root d) (node value : Nat) (clock : Clock)
    (hclock : Clock.le clock (horizon d)) :
    WellFormed n root (createState d node value clock) where
  bookmarksResolve u k hk :=
    old_mem_insertG (hd.bookmarksResolve u k (by simpa [createState] using hk))
  pinsResolve k hk :=
    old_mem_insertG (hd.pinsResolve k (by simpa [createState] using hk))
  contentPresent k hk := by
    rw [show nodes (createState d node value clock) k =
      insertG (nodes d) node k by rfl] at hk
    rcases (insertG_apply (nodes d) node k).1 hk with hold | rfl
    · obtain ⟨w, hw⟩ := hd.contentPresent k hold
      exact ⟨w, by
        simp only [createState, contents_rebuild, addWrite]
        split <;> simp_all [old_mem_insertG]⟩
    · exact ⟨(value, clock), by simp [createState, addWrite, insertG]⟩
  writesInHorizon k w hw := by
    simp only [createState, contents_rebuild, addWrite] at hw
    split at hw
    · rcases (insertG_apply _ _ _).1 hw with hold | hnew
      · exact hd.writesInHorizon k w hold
      · subst hnew
        exact hclock
    · exact hd.writesInHorizon k w hw
  textLinearizes k := hd.textLinearizes k
  grantsResolve := hd.grantsResolve

theorem reference_preserves {n root : Nat} {d : WovenDoc}
    (hd : WellFormed n root d) (user : User) (node : Nat)
    (hexists : nodes d node = true) :
    WellFormed n root (referenceState d user node) where
  bookmarksResolve u k hk := by
    simp only [referenceState, bookmarks_rebuild, addBookmark] at hk
    split at hk
    · rcases (insertG_apply _ _ _).1 hk with hold | rfl
      · exact hd.bookmarksResolve u k hold
      · exact hexists
    · exact hd.bookmarksResolve u k hk
  pinsResolve := hd.pinsResolve
  contentPresent := hd.contentPresent
  writesInHorizon := hd.writesInHorizon
  textLinearizes := hd.textLinearizes
  grantsResolve := hd.grantsResolve

theorem update_preserves {n root : Nat} {d : WovenDoc}
    (hd : WellFormed n root d) (node value : Nat) (clock : Clock)
    (hclock : Clock.le clock (horizon d)) :
    WellFormed n root (updateState d node value clock) where
  bookmarksResolve := hd.bookmarksResolve
  pinsResolve := hd.pinsResolve
  contentPresent k hk := by
    obtain ⟨w, hw⟩ := hd.contentPresent k hk
    exact ⟨w, by
      simp only [updateState, contents_rebuild, addWrite]
      split <;> simp_all [old_mem_insertG]⟩
  writesInHorizon k w hw := by
    simp only [updateState, contents_rebuild, addWrite] at hw
    split at hw
    · rcases (insertG_apply _ _ _).1 hw with hold | hnew
      · exact hd.writesInHorizon k w hold
      · subst hnew
        exact hclock
    · exact hd.writesInHorizon k w hw
  textLinearizes := hd.textLinearizes
  grantsResolve := hd.grantsResolve

theorem tombstone_preserves {n root : Nat} {d : WovenDoc}
    (hd : WellFormed n root d) (node : Nat) (clock : Clock)
    (hclock : Clock.le clock (horizon d)) :
    WellFormed n root (tombstoneState d node clock) :=
  update_preserves hd node tombstoneValue clock hclock

/-- Every typed edit preserves all six `WellFormed` conjuncts. -/
theorem apply_preserves {n root : Nat} {d : WovenDoc}
    (hd : WellFormed n root d) (e : Edit n root d) :
    WellFormed n root (apply e) := by
  cases e with
  | create node value clock _ hclock => exact create_preserves hd node value clock hclock
  | reference user node hexists => exact reference_preserves hd user node hexists
  | update node value clock _ _ hclock => exact update_preserves hd node value clock hclock
  | tombstone node clock _ hclock => exact tombstone_preserves hd node clock hclock

/-! ## Finite traces and command lists -/

/-- A finite dependent trace: every tail is indexed by the state produced by
its head, so malformed intermediate edits are not representable. -/
inductive Trace (n root : Nat) : WovenDoc → WovenDoc → Type where
  | nil (d : WovenDoc) : Trace n root d d
  | cons {d mid out : WovenDoc} (e : Edit n root d)
      (heq : apply e = mid) (tail : Trace n root mid out) : Trace n root d out

/-- Execute a checked trace.  The result is its destination index. -/
def Trace.run {n root : Nat} {d out : WovenDoc} (_ : Trace n root d out) : WovenDoc := out

/-- Preservation for every finite typed trace. -/
theorem Trace.preserves {n root : Nat} {d out : WovenDoc}
    (t : Trace n root d out) (hd : WellFormed n root d) :
    WellFormed n root out := by
  induction t with
  | nil => exact hd
  | cons e heq tail ih =>
      exact ih (heq ▸ apply_preserves hd e)

/-- Execute raw commands, rejecting at the first malformed command. -/
def runCommands (n root : Nat) : WovenDoc → List Command → Option WovenDoc
  | d, [] => some d
  | d, command :: commands =>
      match check n root d command with
      | none => none
      | some edit => runCommands n root (apply edit) commands

/-- Successful execution of any finite raw command list preserves
well-formedness at every accepted step, hence at the final state. -/
theorem runCommands_preserves {n root : Nat} {d out : WovenDoc}
    (commands : List Command) (hd : WellFormed n root d)
    (hrun : runCommands n root d commands = some out) :
    WellFormed n root out := by
  induction commands generalizing d with
  | nil =>
      change some d = some out at hrun
      cases Option.some.inj hrun
      exact hd
  | cons command commands ih =>
      simp only [runCommands] at hrun
      cases hcheck : check n root d command with
      | none => simp [hcheck] at hrun
      | some edit =>
          rw [hcheck] at hrun
          exact ih (apply_preserves hd edit) hrun

/-! ## Named rejection witnesses -/

/-- An update whose clock lies beyond replica X's horizon is rejected. -/
theorem outsideHorizonUpdate_rejected :
    check 5 9 docX (.update 0 7 (2, 0)) = none := by decide

/-- A tombstone whose second coordinate is beyond the horizon is rejected. -/
theorem outsideHorizonTombstone_rejected :
    check 5 9 docX (.tombstone 0 (1, 1)) = none := by decide

/-- A bookmark cannot point at node 12, which `docX` does not contain. -/
theorem danglingReference_rejected :
    check 5 9 docX (.reference true 12) = none := by decide

/-- The tombstone payload cannot be smuggled through the ordinary-update
constructor; callers must use the explicitly named tombstone operation. -/
theorem disguisedTombstoneUpdate_rejected :
    check 5 9 docX (.update 0 tombstoneValue (1, 0)) = none := by decide

/-- A legal four-operation script reaches a well-formed state. -/
def demoCommands : List Command :=
  [.create 3 11 (1, 0), .reference true 3,
   .update 3 12 (1, 0), .tombstone 3 (1, 0)]

theorem demoCommands_wellFormed : ∃ out, runCommands 5 9 docX demoCommands = some out ∧
    WellFormed 5 9 out := by
  refine ⟨_, rfl, ?_⟩
  exact runCommands_preserves demoCommands docX_wellFormed rfl

end Uwueave.WovenEdit
