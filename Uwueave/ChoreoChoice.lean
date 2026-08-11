/-
# Uwueave.ChoreoChoice — communicated Boolean choice for CRDT choreographies.

`Uwueave.Choreo` deliberately gives a silent `read` to every projected endpoint.
That model is useful, and `Choreo.reads_can_disagree` proves its `ReadsAgree`
premise cannot simply be deleted.  This module adds the complementary finite
fragment: one replica observes, projects to `select`, and every other replica
projects to `branch`.  The selected Boolean travels in the delivery trace.

The stateful pieces are read-free `Choreo` blocks.  Their global semantics,
endpoint projection, barrier delivery, and local execution are reused directly;
this module does not define a second merge or barrier semantics.  The only new
runtime datum is the communicated label.  Consequently `projection_sound` has
no `ReadsAgree` premise: a remote endpoint follows the received label instead of
re-evaluating the observer's predicate on its own, potentially stale state.

Scope is intentionally finite and safety-only.  `Bool` is the smallest
nontrivial label carrier.  A generated trace contains a label, but this is not a
general channel-duality theorem, an authenticity result, a fairness assumption,
an eventual-delivery theorem, or a recursive-protocol liveness result.  A missing
label blocks the local partial runner, as the negative fixture at the end shows.
-/
import Uwueave.Choreo

namespace Uwueave.ChoreoChoice

open Uwueave Uwueave.Catalog Uwueave.Delta

universe u v

variable {R : Type v} {S : Type u} [MergeState S] [DecidableEq R]

/-- The smallest finite carrier with two distinct branch labels. -/
abbrev Label := Bool

theorem label_nontrivial : (false : Label) ≠ true := by decide

/-! ## 1. Global programs built from the existing choreography semantics -/

/-- A stateful block accepted between communicated choices.  Requiring the
existing `Choreo.ReadFree` judgement is what lets the adapter discharge the old
silent-read premise rather than hiding it. -/
structure Block (R : Type v) (S : Type u) [MergeState S] where
  code : Choreo.Choreo R S
  readFree : Choreo.ReadFree code

namespace Block

/-- The empty existing-language block. -/
def done : Block R S := ⟨Choreo.Choreo.done, trivial⟩

end Block

/-- A finite communicated-choice program.  Each node first runs an ordinary
read-free `Choreo` block, then the named observer selects a Boolean label. -/
inductive Program (R : Type v) (S : Type u) [MergeState S] : Type (max u v) where
  | finish (block : Block R S) : Program R S
  | choice (block : Block R S) (observer : R) (observe : S → Label)
      (onTrue onFalse : Program R S) : Program R S

/-- Global denotation delegates every state transition and barrier to
`Choreo.denote`; this layer only chooses the continuation. -/
def denote (roster : List R) : Program R S → Choreo.Cfg R S → Choreo.Cfg R S
  | .finish block, initial => Choreo.denote roster block.code initial
  | .choice block observer observe onTrue onFalse, initial =>
      let after := Choreo.denote roster block.code initial
      if observe (after observer) then denote roster onTrue after
      else denote roster onFalse after

/-! ## 2. Endpoint projection and label-carrying delivery -/

/-- Projected local control.  The observer computes `select`; every other
endpoint waits at `branch` for the selected label.  The leading local block is
still exactly `Choreo.Local`. -/
inductive Local (S : Type u) [MergeState S] : Type u where
  | finish (block : Choreo.Local S) : Local S
  | select (block : Choreo.Local S) (observe : S → Label)
      (onTrue onFalse : Local S) : Local S
  | branch (block : Choreo.Local S) (onTrue onFalse : Local S) : Local S

/-- Endpoint projection exposes the observer-side `select` / remote `branch`
distinction while delegating each stateful block to `Choreo.project`. -/
def project : Program R S → R → Local S
  | .finish block, replica => .finish (Choreo.project block.code replica)
  | .choice block observer observe onTrue onFalse, replica =>
      if replica = observer then
        .select (Choreo.project block.code replica) observe
          (project onTrue replica) (project onFalse replica)
      else
        .branch (Choreo.project block.code replica)
          (project onTrue replica) (project onFalse replica)

/-- A structured delivery trace.  `states` is precisely the existing barrier
stream for the leading block; `label` is the one new communicated datum. -/
inductive Delivery (S : Type u) where
  | finish (states : List S) : Delivery S
  | choice (states : List S) (label : Label) (rest : Delivery S) : Delivery S

/-- Generated delivery delegates state delivery to `Choreo.deliveries` and
adds the observer's selected label before recursing down that branch. -/
def deliveries (roster : List R) :
    Program R S → Choreo.Cfg R S → R → Delivery S
  | .finish block, initial, replica =>
      .finish (Choreo.deliveries roster block.code initial replica)
  | .choice block observer observe onTrue onFalse, initial, replica =>
      let after := Choreo.denote roster block.code initial
      let label := observe (after observer)
      let rest := if label then deliveries roster onTrue after replica
                  else deliveries roster onFalse after replica
      .choice (Choreo.deliveries roster block.code initial replica) label rest

/-- Partial local execution.  A selector checks that the emitted trace label is
the label it computed; a remote branch consumes the label without observing its
own state.  A missing/malformed frame returns `none` rather than inventing a
choice. -/
def lrun : Local S → Delivery S → S → Option S
  | .finish block, .finish states, state =>
      some (Choreo.lrun block states state)
  | .select block observe onTrue onFalse, .choice states label rest, state =>
      let after := Choreo.lrun block states state
      if observe after = label then
        if label then lrun onTrue rest after else lrun onFalse rest after
      else none
  | .branch block onTrue onFalse, .choice states label rest, state =>
      let after := Choreo.lrun block states state
      if label then lrun onTrue rest after else lrun onFalse rest after
  | _, _, _ => none

/-! ## 3. Projection soundness without `ReadsAgree` -/

/-- An accepted block inherits pointwise projection soundness from `Choreo`.
Its stored read-freedom proof discharges `Choreo.ReadsAgree` explicitly. -/
theorem block_projection_sound (roster : List R) (block : Block R S)
    (initial : Choreo.Cfg R S) (replica : R) :
    Choreo.denote roster block.code initial replica =
      Choreo.lrun (Choreo.project block.code replica)
        (Choreo.deliveries roster block.code initial replica) (initial replica) := by
  exact Choreo.projection_sound roster block.code initial
    (Choreo.readFree_readsAgree roster block.code initial block.readFree) replica

/-- **Communicated-choice projection is sound with no `ReadsAgree` premise.**
The observer's local state computes the global label by block soundness; a remote
endpoint consumes that same generated label and therefore never evaluates the
predicate on a stale local copy. -/
theorem projection_sound (roster : List R) :
    ∀ (program : Program R S) (initial : Choreo.Cfg R S) (replica : R),
      lrun (project program replica) (deliveries roster program initial replica)
          (initial replica) = some (denote roster program initial replica) := by
  intro program
  induction program with
  | finish block =>
      intro initial replica
      simp only [project, deliveries, lrun, denote]
      rw [← block_projection_sound roster block initial replica]
  | choice block observer observe onTrue onFalse ihTrue ihFalse =>
      intro initial replica
      by_cases hreplica : replica = observer
      · subst observer
        simp only [project, deliveries, denote]
        rw [if_pos True.intro]
        simp only [lrun]
        rw [← block_projection_sound roster block initial replica]
        cases hlabel : observe (Choreo.denote roster block.code initial replica)
        · simpa [hlabel] using
            ihFalse (Choreo.denote roster block.code initial) replica
        · simpa [hlabel] using
            ihTrue (Choreo.denote roster block.code initial) replica
      · simp only [project, deliveries, lrun, denote, if_neg hreplica]
        rw [← block_projection_sound roster block initial replica]
        cases hlabel : observe (Choreo.denote roster block.code initial observer)
        · simpa [hlabel] using
            ihFalse (Choreo.denote roster block.code initial) replica
        · simpa [hlabel] using
            ihTrue (Choreo.denote roster block.code initial) replica

/-! ## 4. Two-party fixtures and the old silent-read boundary -/

abbrev Rep := Bool

def roster : List Rep := [false, true]

abbrev Bits := GSet Nat

/-- The observer has bit zero; the remote copy is deliberately stale. -/
def divergentStart : Choreo.Cfg Rep Bits := fun replica =>
  if replica = false then Delta.addDelta 0 else fun _ => false

/-- The same disagreement with the observer's answer flipped to false. -/
def divergentFalseStart : Choreo.Cfg Rep Bits := fun replica =>
  if replica = false then (fun _ => false) else Delta.addDelta 0

def seesZero : Bits → Label := fun bits => bits 0

theorem fixture_observations_disagree :
    seesZero (divergentStart false) ≠ seesZero (divergentStart true) := by decide

theorem false_fixture_observations_disagree :
    seesZero (divergentFalseStart false) ≠
      seesZero (divergentFalseStart true) := by decide

def addAtRemote (n : Nat) : Block Rep Bits :=
  ⟨Choreo.Choreo.write true (Delta.gsetAdd n) .done, trivial⟩

/-- Replica `false` selects from its copy; replica `true` branches on that
communicated result.  True adds `1` remotely and false would add `2`. -/
def twoParty : Program Rep Bits :=
  .choice .done false seesZero
    (.finish (addAtRemote 1))
    (.finish (addAtRemote 2))

theorem project_twoParty_observer :
    project twoParty false =
      .select .fin seesZero (.finish .fin) (.finish .fin) := rfl

theorem project_twoParty_remote :
    project twoParty true =
      .branch .fin
        (.finish (.act (Delta.gsetAdd 1) .fin))
        (.finish (.act (Delta.gsetAdd 2) .fin)) := rfl

/-- The selected true branch reaches the remote endpoint despite the endpoints'
opposite local observations. -/
theorem twoParty_remote_takes_true :
    denote roster twoParty divergentStart true 1 = true := by decide

theorem twoParty_remote_does_not_take_false :
    denote roster twoParty divergentStart true 2 = false := by decide

/-- Flipping only the observer's selected value exercises the false branch: the
remote adds `2` even though its own stale copy observes true. -/
theorem twoParty_remote_takes_false_branch :
    denote roster twoParty divergentFalseStart true 2 = true := by decide

theorem twoParty_remote_false_branch_skips_true :
    denote roster twoParty divergentFalseStart true 1 = false := by decide

/-- The general theorem applies directly; there is no branch-agreement argument
to supply even though `fixture_observations_disagree` proves one cannot exist. -/
theorem twoParty_remote_projection :
    lrun (project twoParty true) (deliveries roster twoParty divergentStart true)
        (divergentStart true) =
      some (denote roster twoParty divergentStart true) :=
  projection_sound roster twoParty divergentStart true

theorem twoParty_observer_projection :
    lrun (project twoParty false) (deliveries roster twoParty divergentStart false)
        (divergentStart false) =
      some (denote roster twoParty divergentStart false) :=
  projection_sound roster twoParty divergentStart false

/-- A remote `branch` with no label frame cannot step: missing communication is
reported as `none`, not guessed from the remote copy. -/
theorem twoParty_remote_missing_label :
    lrun (project twoParty true) (.finish []) (divergentStart true) = none := rfl

/-- The observer also rejects a trace whose label disagrees with the value it
actually selected. -/
theorem twoParty_observer_rejects_wrong_label :
    lrun (project twoParty false)
        (.choice [] false (.finish [])) (divergentStart false) = none := by decide

/-- The old silent-read model remains honestly refuted: this adapter solves the
problem by communicating a choice, not by pretending replicated reads agree. -/
theorem silent_reads_still_can_disagree :
    ∃ (initial : Choreo.Cfg Choreo.Rep Choreo.LoomDoc)
      (observe : Choreo.LoomDoc → Bool) (p r : Choreo.Rep),
      observe (initial p) ≠ observe (initial r) :=
  Choreo.reads_can_disagree

end Uwueave.ChoreoChoice
