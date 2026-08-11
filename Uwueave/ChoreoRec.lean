/-
# Uwueave.ChoreoRec — guarded recursion, finite approximants, and barrier progress.

`Choreo` is intentionally finite. This module adds an anonymous, nearest-binder
`mu`/`var` layer around it while keeping all executable meaning bounded: fuel
counts recursive unfoldings, and every approximant is an ordinary finite
`Choreo`. Consequently global denotation, endpoint projection, deliveries, and
projection soundness are inherited rather than reimplemented.

Progress here is deliberately local and finite. A runtime may take one local
write/read step, or release a barrier when every member of a nonempty roster is
at a barrier. `Deadlocked` means not complete and unable to take one such step.
Nothing states eventual delivery, fairness, temporal liveness, or that a remote
replica will eventually reach a barrier.
-/
import Uwueave.Choreo

namespace Uwueave.ChoreoRec

open Uwueave
open Uwueave.Catalog
open Uwueave.Delta
open Uwueave.Choreo

universe u v

variable {R : Type v} {S : Type u} [MergeState S]

/-! ## §1. Recursive syntax and its guardedness judgement -/

/-- Recursive choreography with an anonymous nearest `mu` binder. A `var`
inside a nested `mu` refers to that inner binder; outer recursion cannot cross
the nested binder. This small discipline avoids name capture entirely. -/
inductive RecChoreo (R : Type v) (S : Type u) [MergeState S] : Type (max u v) where
  | done : RecChoreo R S
  | write (r : R) (m : DeltaMutator S) (k : RecChoreo R S) : RecChoreo R S
  | read (r : R) (o : S → Bool) (kt kf : RecChoreo R S) : RecChoreo R S
  | sync (k : RecChoreo R S) : RecChoreo R S
  | var : RecChoreo R S
  | mu (body : RecChoreo R S) : RecChoreo R S

/-- Syntactic size, used only to justify recursion through finite prefixes. -/
def RecChoreo.size : RecChoreo R S → Nat
  | .done => 1
  | .write _ _ k => k.size + 1
  | .read _ _ kt kf => kt.size + kf.size + 1
  | .sync k => k.size + 1
  | .var => 1
  | .mu body => body.size + 1

/-- No unbound anonymous recursion variable occurs. -/
def RecChoreo.closedFrom (bound : Bool) : RecChoreo R S → Bool
  | .done => true
  | .write _ _ k => k.closedFrom bound
  | .read _ _ kt kf => kt.closedFrom bound && kf.closedFrom bound
  | .sync k => k.closedFrom bound
  | .var => bound
  | .mu body => body.closedFrom true

/-- Every recursion variable is protected by at least one finite choreography
action since its nearest binder. A nested `mu` resets the protection flag for
its own variable. -/
def RecChoreo.guardedFrom (isProtected : Bool) : RecChoreo R S → Bool
  | .done => true
  | .write _ _ k => k.guardedFrom true
  | .read _ _ kt kf => kt.guardedFrom true && kf.guardedFrom true
  | .sync k => k.guardedFrom true
  | .var => isProtected
  | .mu body => body.guardedFrom false

/-- Closed, guarded recursive choreography. This is the accepted recursive
fragment; the raw syntax remains available so rejected programs can be named. -/
def WellGuarded (term : RecChoreo R S) : Prop :=
  term.closedFrom false = true ∧ term.guardedFrom false = true

instance (term : RecChoreo R S) : Decidable (WellGuarded term) := by
  unfold WellGuarded
  infer_instance

/-! ## §2. Capture-free unfolding and finite approximants -/

/-- Replace occurrences of the nearest binder's variable. A nested `mu` owns
its own anonymous variable, so substitution intentionally stops there. -/
def unfoldBody (self : RecChoreo R S) : RecChoreo R S → RecChoreo R S
  | .done => .done
  | .write r m k => .write r m (unfoldBody self k)
  | .read r o kt kf => .read r o (unfoldBody self kt) (unfoldBody self kf)
  | .sync k => .sync (unfoldBody self k)
  | .var => self
  | .mu body => .mu body

@[simp] theorem unfoldBody_var (self : RecChoreo R S) :
    unfoldBody self .var = self := rfl

@[simp] theorem unfoldBody_nested_mu (self body : RecChoreo R S) :
    unfoldBody self (.mu body) = .mu body := rfl

/-- `fuel` bounds only recursive unfoldings. Finite action prefixes are retained
even at fuel zero; a variable or a binder with no remaining fuel truncates to
`Choreo.done`. Every result is therefore accepted by all existing finite
Choreo semantics and projection theorems. -/
def approximate : (fuel : Nat) → RecChoreo R S → Choreo R S
  | _, .done => .done
  | fuel, .write r m k => .write r m (approximate fuel k)
  | fuel, .read r o kt kf => .read r o (approximate fuel kt) (approximate fuel kf)
  | fuel, .sync k => .sync (approximate fuel k)
  | _, .var => .done
  | 0, .mu _ => .done
  | n + 1, .mu body => approximate n (unfoldBody (.mu body) body)
termination_by fuel term => (fuel, term.size)
decreasing_by
  · exact Prod.Lex.right fuel (by simp [RecChoreo.size])
  · exact Prod.Lex.right fuel (by simp only [RecChoreo.size]; omega)
  · exact Prod.Lex.right fuel (by simp only [RecChoreo.size]; omega)
  · exact Prod.Lex.right fuel (by simp [RecChoreo.size])
  · exact Prod.Lex.left _ _ (by omega)

/-- One unit of fuel unfolds a head binder once, then continues with the
remaining fuel. -/
@[simp] theorem approximate_mu_succ (n : Nat) (body : RecChoreo R S) :
    approximate (n + 1) (.mu body) =
      approximate n (unfoldBody (.mu body) body) := by
  rw [approximate]

@[simp] theorem approximate_mu_zero (body : RecChoreo R S) :
    approximate 0 (.mu body) = .done := by
  rw [approximate]

/-- Embed the original finite language. -/
def embed : Choreo R S → RecChoreo R S
  | .done => .done
  | .write r m k => .write r m (embed k)
  | .read r o kt kf => .read r o (embed kt) (embed kf)
  | .sync k => .sync (embed k)

/-- **Conservativity:** every fuel level elaborates a recursion-free term back
to exactly the original finite choreography. -/
theorem approximate_embed (fuel : Nat) : ∀ finite : Choreo R S,
    approximate fuel (embed finite) = finite
  | .done => by rw [embed, approximate]
  | .write r m k => by rw [embed, approximate, approximate_embed fuel k]
  | .read r o kt kf => by
      rw [embed, approximate, approximate_embed fuel kt, approximate_embed fuel kf]
  | .sync k => by rw [embed, approximate, approximate_embed fuel k]

/-- Recursion-free terms contain no variable, independently of binder state. -/
theorem embed_closedFrom (bound : Bool) (finite : Choreo R S) :
    (embed finite).closedFrom bound = true := by
  induction finite with
  | done => rfl
  | write _ _ k ih => exact ih
  | read _ _ kt kf iht ihf =>
      simp [embed, RecChoreo.closedFrom, iht, ihf]
  | sync k ih => exact ih

theorem embed_guardedFrom (isProtected : Bool) (finite : Choreo R S) :
    (embed finite).guardedFrom isProtected = true := by
  induction finite generalizing isProtected with
  | done => rfl
  | write _ _ k ih => simpa [embed, RecChoreo.guardedFrom] using ih true
  | read _ _ kt kf iht ihf =>
      simp [embed, RecChoreo.guardedFrom, iht true, ihf true]
  | sync k ih => simpa [embed, RecChoreo.guardedFrom] using ih true

/-- Recursion-free terms are closed and guarded. -/
theorem embed_wellGuarded (finite : Choreo R S) : WellGuarded (embed finite) :=
  ⟨embed_closedFrom false finite, embed_guardedFrom false finite⟩

/-! ## §3. Existing semantics and projection, lifted through approximants -/

variable [DecidableEq R]

def denoteApprox (fuel : Nat) (roster : List R) (term : RecChoreo R S)
    (initial : Cfg R S) : Cfg R S :=
  Choreo.denote roster (approximate fuel term) initial

def projectApprox (fuel : Nat) (term : RecChoreo R S) (replica : R) : Local S :=
  Choreo.project (approximate fuel term) replica

def deliveriesApprox (fuel : Nat) (roster : List R) (term : RecChoreo R S)
    (initial : Cfg R S) (replica : R) : List S :=
  Choreo.deliveries roster (approximate fuel term) initial replica

/-- Projection soundness needs exactly the same `ReadsAgree` hypothesis as the
finite language. Bounded unfolding supplies no branch agreement for free. -/
theorem projection_sound_approx (fuel : Nat) (roster : List R)
    (term : RecChoreo R S) (initial : Cfg R S)
    (hreads : ReadsAgree roster (approximate fuel term) initial) (replica : R) :
    denoteApprox fuel roster term initial replica =
      lrun (projectApprox fuel term replica)
        (deliveriesApprox fuel roster term initial replica) (initial replica) := by
  exact Choreo.projection_sound roster (approximate fuel term) initial hreads replica

theorem denoteApprox_embed (fuel : Nat) (roster : List R) (finite : Choreo R S)
    (initial : Cfg R S) :
    denoteApprox fuel roster (embed finite) initial =
      Choreo.denote roster finite initial := by
  rw [denoteApprox, approximate_embed]

theorem projectApprox_embed (fuel : Nat) (finite : Choreo R S) (replica : R) :
    projectApprox fuel (embed finite) replica = Choreo.project finite replica := by
  rw [projectApprox, approximate_embed]

/-! ## §4. A finite operational progress/deadlock judgement -/

/-- Local endpoint programs and their replica-owned states. -/
structure Runtime (R : Type v) (S : Type u) [MergeState S] where
  code : R → Local S
  state : Cfg R S

def pointUpdate {A : Type u} (f : R → A) (replica : R) (value : A) : R → A :=
  fun p => if p = replica then value else f p

/-- A nonempty roster is barrier-ready exactly when every roster endpoint is at
a barrier. The continuations may differ; projection soundness is a separate
semantic property, not baked into readiness. -/
def BarrierReady (roster : List R) (runtime : Runtime R S) : Prop :=
  roster ≠ [] ∧ ∀ p ∈ roster, ∃ k, runtime.code p = .barrier k

/-- Remove one ready barrier from every roster endpoint. -/
def releaseCode (roster : List R) (code : R → Local S) : R → Local S :=
  fun p =>
    if p ∈ roster then
      match code p with
      | .barrier k => k
      | other => other
    else code p

/-- The state update performed by one global barrier release. -/
def releaseState (roster : List R) (state : Cfg R S) : Cfg R S :=
  fun p => if p ∈ roster then joinAll (state p) (roster.map state) else state p

/-- One operational step. Writes and reads are local; a barrier step is global
and requires the full nonempty roster. No rule promises that a missing endpoint
will arrive later. -/
inductive Step (roster : List R) : Runtime R S → Runtime R S → Prop where
  | act (runtime : Runtime R S) (replica : R) (mutator : DeltaMutator S)
      (next : Local S) (hcode : runtime.code replica = .act mutator next) :
      Step roster runtime
        ⟨pointUpdate runtime.code replica next,
         pointUpdate runtime.state replica (mutator.op (runtime.state replica))⟩
  | obs (runtime : Runtime R S) (replica : R) (observe : S → Bool)
      (yes no : Local S) (hcode : runtime.code replica = .obs observe yes no) :
      Step roster runtime
        ⟨pointUpdate runtime.code replica
            (if observe (runtime.state replica) then yes else no),
         runtime.state⟩
  | barrier (runtime : Runtime R S) (hready : BarrierReady roster runtime) :
      Step roster runtime
        ⟨releaseCode roster runtime.code, releaseState roster runtime.state⟩

/-- Every roster endpoint has terminated. -/
def Complete (roster : List R) (runtime : Runtime R S) : Prop :=
  ∀ p ∈ roster, runtime.code p = .fin

def CanStep (roster : List R) (runtime : Runtime R S) : Prop :=
  ∃ next, Step roster runtime next

/-- Precise finite deadlock: unfinished, with neither a local action/read nor a
unanimously ready barrier step. -/
def Deadlocked (roster : List R) (runtime : Runtime R S) : Prop :=
  ¬ Complete roster runtime ∧ ¬ CanStep roster runtime

/-- Project one finite approximant into an initial runtime. -/
def initialRuntime (fuel : Nat) (term : RecChoreo R S)
    (initial : Cfg R S) : Runtime R S :=
  ⟨fun p => projectApprox fuel term p, initial⟩

/-! ## §5. Positive guarded progress and exact refutations -/

/-- One synchronization per recursive unfolding. -/
def guardedBarrierLoop : RecChoreo Bool Nat := .mu (.sync .var)

theorem guardedBarrierLoop_wellGuarded : WellGuarded guardedBarrierLoop := by
  decide

/-- Each additional unfolding of the guarded loop exposes exactly one more
finite barrier prefix. -/
theorem guardedBarrierLoop_unfold (n : Nat) :
    approximate (n + 1) guardedBarrierLoop =
      Choreo.sync (approximate n guardedBarrierLoop) := by
  simp [guardedBarrierLoop, approximate, unfoldBody]

/-- At fuel one the guarded loop exposes one finite barrier. -/
theorem guardedBarrierLoop_approx_one :
    approximate 1 guardedBarrierLoop = (Choreo.sync Choreo.done : Choreo Bool Nat) := by
  rw [guardedBarrierLoop_unfold]
  simp [guardedBarrierLoop]

def boolRoster : List Bool := [false, true]

def boolInitial : Cfg Bool Nat := fun p => if p then 2 else 1

/-- The guarded protocol's first bounded approximant can make a barrier step.
This is one-step finite progress, not eventual progress of the infinite loop. -/
theorem guardedBarrierLoop_progresses :
    CanStep boolRoster (initialRuntime 1 guardedBarrierLoop boolInitial) := by
  refine ⟨⟨releaseCode boolRoster
      (initialRuntime 1 guardedBarrierLoop boolInitial).code,
      releaseState boolRoster boolInitial⟩, Step.barrier _ ?_⟩
  constructor
  · simp [boolRoster]
  · intro p hp
    refine ⟨Local.fin, ?_⟩
    simp [initialRuntime, projectApprox, guardedBarrierLoop_approx_one,
      Choreo.project]

/-- Immediate self-reference: closed, but not guarded by any finite action. -/
def unguardedLoop : RecChoreo Bool Nat := .mu .var

theorem unguardedLoop_is_rejected : ¬ WellGuarded unguardedLoop := by
  decide

/-- A concrete partial barrier arrival: one endpoint waits while the other has
already terminated. -/
def mismatchedBarrierCode : Bool → Local Nat
  | false => .barrier .fin
  | true => .fin

def mismatchedBarrierRuntime : Runtime Bool Nat :=
  ⟨mismatchedBarrierCode, boolInitial⟩

theorem mismatchedBarrier_not_complete :
    ¬ Complete boolRoster mismatchedBarrierRuntime := by
  intro h
  have hf := h false (by simp [boolRoster])
  simp [mismatchedBarrierRuntime, mismatchedBarrierCode] at hf

theorem mismatchedBarrier_cannot_step :
    ¬ CanStep boolRoster mismatchedBarrierRuntime := by
  rintro ⟨next, hstep⟩
  cases hstep with
  | act replica mutator next hcode =>
      cases replica <;> simp [mismatchedBarrierRuntime, mismatchedBarrierCode] at hcode
  | obs replica observe yes no hcode =>
      cases replica <;> simp [mismatchedBarrierRuntime, mismatchedBarrierCode] at hcode
  | barrier hready =>
      obtain ⟨k, hk⟩ := hready.2 true (by simp [boolRoster])
      simp [mismatchedBarrierRuntime, mismatchedBarrierCode] at hk

/-- Exact barrier deadlock witness. -/
theorem mismatched_barrier_is_deadlocked :
    Deadlocked boolRoster mismatchedBarrierRuntime :=
  ⟨mismatchedBarrier_not_complete, mismatchedBarrier_cannot_step⟩

/-- Guardedness is a real restriction and roster agreement is a real progress
premise: an unguarded recursion is rejected, and a partial barrier arrival is
deadlocked by the operational judgement. -/
theorem unguarded_and_deadlocked_refutations :
    ¬ WellGuarded unguardedLoop ∧ Deadlocked boolRoster mismatchedBarrierRuntime :=
  ⟨unguardedLoop_is_rejected, mismatched_barrier_is_deadlocked⟩

end Uwueave.ChoreoRec
