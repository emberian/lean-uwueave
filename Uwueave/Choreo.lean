/-
# Uwueave.Choreo — choreographic programming over replica-owned CRDT state.

**choreography : computation :: CRDT : data.** A CRDT is one datum whose replicas
merge; a *choreography* is one program whose replicas are projected. This file is
the junction: a global program written from the god's-eye view, **projected** to
per-replica local programs, with the **coordination verdict read off the
choreography** by this library's judgement (`IConfluent` / `SegmentedIConfluent`).

## What is here

  * `Choreo` (§1) — a four-constructor global program: `done`, `write` (replica
    `r` mutates its own replica of the shared lattice, by a `Delta.DeltaMutator`),
    `read` (replica `r` observes *its own* copy and the choreography branches),
    `sync` (a barrier: every roster replica ends holding the join of all).
  * `denote` (§2) — the global semantics over a **configuration** `Cfg R S = R → S`
    (one lattice point per replica). `write` touches one component; `read` reads one
    component; `sync` joins the roster.
  * `project` / `lrun` / `deliveries` (§3) — endpoint projection to a `Local`
    program, its local run against an explicit **delivery stream**, and the stream
    the global run supplies. `projection_sound` is a *pointwise state equality*, on
    the whole fragment (all four constructors), not a head-duality.
  * `coordination_free_converges` (§4) — **the verdict theorem, positive half**: a
    sync-free choreography's projected replicas, gossiping their results in **any
    order, with any duplication, in any batching**, land on **one and the same
    state**; and (`coordination_free_safe`) that state is legal when `I` is
    I-confluent.
  * `coordination_free_iff_iconfluent` (§5) — **the verdict theorem, iff-shaped**:
    for the locally-checked saturating family `satFamily`, *"the sync-free
    choreography meets the spec"* **⟺** *`I` is I-confluent*. Both directions carry
    content. `sync_cannot_be_dropped` is the contrapositive with a witness.
  * `seam_coordination_free` (§6) — **the seam refinement**: a choreography whose
    every write is fiber-local for a seam `σ` and which contains no `sync` runs
    coordination-free *inside a fiber* — invariant preserved **and** fiber preserved
    — on `SegmentedIConfluent σ I` alone, with **no `IConfluent` anywhere**. `sync`
    is required exactly at σ-changes: `realloc_desynced_breaks` is the write that
    moves `σ` and dies without its barrier, against `spendChoreo`, which does not.
  * `Verdict` (§7) — the choreography-level verdict carrier (`free` / `seam` /
    `coupled`), demoting to `Spec.Verdict` by `toSpecVerdict`, in the shape this
    library already carries verdicts.
  * §8 — the worked two-replica loom: edits free, pin = sync. All three verdicts
    inhabited on concrete programs (`editVerdict` free, `spendVerdict` seam,
    `loomVerdict` coupled); the disciplined `sync (read …)` shape with its
    projection computed at both endpoints; the concrete run where deleting the
    barrier breaks the document (`loom_desynced_broken`); and the same for the
    seam (`realloc_desynced_breaks`).

## Literature

  * Fabrizio Montesi, *Introduction to Choreographies*, Cambridge UP 2023 — the
    global-program/endpoint-projection discipline this file instantiates.
  * Honda, Yoshida, Carbone — "Multiparty Asynchronous Session Types", POPL 2008;
    Carbone, Montesi — "Deadlock-freedom-by-design: multiparty asynchronous global
    programming", POPL 2013 (EPP correspondence).
  * Bailis et al., VLDB 2015 (I-confluence); Whittaker–Hellerstein, VLDB 2019
    (segmented invariant confluence) — via `Uwueave.Confluence` / `Uwueave.Segmented`.
  * Kuhn, Melgratti, Tuosto — "Behavioural Types for Local-First Software",
    ECOOP 2023 (LIPIcs 263:15). **The junction this file sits in is occupied,
    and this is the occupant** — see the retraction immediately below.

## ⚠ Retraction — "the choreography × CRDT junction is empty"

The design memo this file was built from (`FORCODEX.md` §4.7, retraction 2)
claimed a literature search "found **nothing** at the choreography × CRDT
junction". **That claim is withdrawn.** Kuhn–Melgratti–Tuosto (ECOOP 2023)
specify *swarm protocols* from a global viewpoint and **project** them to
per-peer machines that communicate by event notification over a replicated
log — local-first by construction, with peers making progress while
disconnected and, under the paper's well-formedness conditions, eventual
recovery of consistency and eventual agreement between each machine's locally
observable behaviour and the global specification. Choreographic projection
over eventually-consistent replicated state, with a progress guarantee under
unavailability, published three years before this file.

**The narrower claim this file does make, and which we have not found
elsewhere:** no system we could find combines *projected local-first
protocols* with a coordination verdict **derived from I-confluence**
(`coordination_free_iff_iconfluent`) **and** a **seam refinement** over that
verdict (`seam_coordination_free`). Kuhn et al. ask whether a projection
conforms and eventually converges; they do not ask whether an application
invariant survives the merge, and they carry no segmented notion — nothing of
the form "a barrier is required exactly at σ-changes and is free within a
fiber". Those two theorems are the delta. It is a small claim on purpose;
"the junction is empty" was not, and was false.

(A neighbouring cell is occupied too, and §4's framing elsewhere should stop
treating it as open ground: **Grove** — Adams, Griffis, Porter, Satish, Zhao,
Omar, POPL 2025 — is a bidirectionally typed collaborative structure-editor
calculus over a CmRDT edit log in which conflicts are **represented with
holes**. Typed holes × replicated collaborative editing is prior art. See
`Uwueave/Holes.lean`.)

## In-house prior art — credited precisely, and the delta

`breadstuffs/metatheory/Dregg2/` (read-only; **not** imported, and nothing here
depends on it):

  * `Dregg2/Coordination.lean` — a full MPST development: `GlobalType`
    (`comm`/`choice`/`mu`/`var`/`done`), `LocalType`, `project` with the branch-merge
    `mergeLocal`, `Projectable`, `projection_sound`, `deadlock_freedom` on a `NoRec`
    fragment, and an operational `GStep`/`GReach` LTS.
  * `Dregg2/Projection.lean` — the **blue/red split**: `BlueEligible I := IConfluent I`;
    blue projects to a coordination-free cell program, red to an atomic `JointTurn`.
  * `Dregg2/Spec/Choreography.lean` — `red_iff_coupled`: red ⟺ ¬ I-confluent ⟺ needs
    a joint hyperedge.

**The delta, stated plainly.**

  1. *Their judgement is over their kernel's turn model; ours is over the uwueave
     judgement.* Their `red_iff_coupled` classifies **one interaction** by its
     `StepEffect.inv`, and its first half is `Iff.rfl` (the colour *is defined as*
     `IConfluent`, so that direction carries no content beyond the `def`); the
     operational half rests on their conservation/atomic-wide-turn commitments
     (`Hyperedge`, CG-5 Σ=0) which uwueave's kernel does not have.
     `coordination_free_iff_iconfluent` below is over a **whole choreography**, both
     directions carry content, and neither side is a definitional unfold: the
     forward direction goes through a saturating *run*, the backward through
     write-safety plus the merge law.
  2. *Delivery is quantified.* Their blue payoff is `blue_merge_safe : I x → I y →
     I (x ⊔ y)` — a closure property. Ours (`coordination_free_converges`) quantifies
     over **delivery**: any two replicas, any two delivery lists with the same
     content, reach the *same state*, by `Delta.same_deltas_same_state`.
  3. *The seam refinement is new.* `SegmentedIConfluent` appears nowhere in their
     choreography layer (`Coordination.lean`, `Projection.lean`,
     `Spec/Choreography.lean` contain zero occurrences). §6 is choreography-altitude
     Whittaker: sync nodes are required exactly at σ-changes and are *free within
     fibers*, proved with no `IConfluent` hypothesis at all.

## Non-claims

  * ⟨TERMINAL⟩ **The asynchrony model is state-based (CvRDT) gossip with a
    synchronous roster barrier.** Delivery is modelled as *membership of a delivery
    list*: order, duplication and batching are immaterial by `Delta`'s three laws,
    and that is a theorem, not an assumption. It is **not** an operational network:
    there is no message-loss LTS and no channel. `sync` is a barrier over an explicit
    roster, evaluated in one step.
  * ⟨TERMINAL⟩ **There is no `send`/`recv` in this core.** This is a CRDT
    choreography: the channel is the lattice. So the MPST notion of general
    channel duality has no analogue here, and `projection_sound` is correspondingly
    *not* head-duality but a pointwise state equality — strictly more informative
    for this fragment, and inapplicable to theirs. `Uwueave.ChoreoChoice` adds one
    finite explicit label-delivery adapter; it does not turn this core into a
    channel calculus or prove general duality.
  * ⟨DONE in `Uwueave.ChoreoRec`⟩ **Finite guarded recursion approximants.**
    `Choreo` itself remains finite, while `ChoreoRec` adds guarded anonymous
    recursion through fuel-bounded approximants. `approximate_embed` and
    `projection_sound_approx` prove conservativity and projection soundness at
    every finite fuel.
  * ⟨DONE U-0013 in `Uwueave.ChoreoTemporal`⟩ **Recursive behavior now has an
    infinite-trace semantics.** Its coalgebra exposes one labeled control event
    and continuation forever, padding termination explicitly and exposing an
    unguarded head as `stuck`. `unfoldPrefix_eq_finitePrefix` proves that an
    independent bounded coalgebra iteration equals every finite trace prefix;
    `guardedBarrierLoop_finite_prefix_approximation`
    connects every prefix of the canonical infinite loop to `ChoreoRec`'s
    existing fuel approximant. `Bisimilar` is the extensional greatest
    observation relation, and `project_bisim_congr` proves endpoint projection
    is a congruence. Exact barrier-loop and unguarded-loop fixtures separate the
    positive and negative behaviors.
  * ⟨DONE U-0014 under explicit temporal premises in `Uwueave.ChoreoTemporal`⟩
    **Recursive barriers are temporally deadlock-free for accepted roster
    executions.** `BarrierWellFormed` deliberately requires both ordinary
    `WellGuarded` syntax and a successful finite-prefix barrier check for every
    read-branch stream: the exact action-guarded `guardedReadLoop` does not
    qualify. `temporal_deadlock_free` proves that every
    such behavior reaches a matching nonempty-roster barrier under named
    `PrefixFair` scheduling and that it is eventually released under the
    separate `EventualBarrierDelivery` premise. No deployed scheduler is
    declared fair. `ChoreoRec.mismatched_barrier_is_deadlocked` and the new
    `mismatchedEndpoints_not_matching` remain the exact partial-roster
    refutations.
  * ⟨DONE in `Uwueave.ChoreoChoice`⟩ **Communicated finite choices remove
    `ReadsAgree` from their projection theorem.** This core's silent `read` still
    sends no message: every replica evaluates the same predicate on its own copy,
    so `ReadsAgree` remains its honest hypothesis and `reads_can_disagree` remains
    the refutation of dropping it. The sibling adapter instead stages read-free
    `Choreo` blocks around an observer `select` and remote `branch`, carries the
    chosen Boolean in its delivery trace, and proves
    `ChoreoChoice.projection_sound` without `ReadsAgree`.
    `ChoreoChoice.twoParty_remote_takes_true` and
    `twoParty_remote_takes_false_branch` exercise both labels from disagreeing
    replica views; `twoParty_remote_missing_label` refuses to invent an absent
    label. This is finite safety over generated traces, not channel duality,
    recursion liveness, fairness, authenticity, or eventual delivery.
  * ⟨PREMISE U-0015⟩ **Liveness of delivery.** `coordination_free_converges` says *given*
    that a delivery list contains the run's results, every replica agrees. That every
    result is eventually delivered is the CRDT premise and is not proved here.
-/
import Uwueave.Spec
import Uwueave.Delta
import Uwueave.Necessity

namespace Uwueave.Choreo

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Delta

universe u v w

/-! ## §1. The syntax — four constructors, and why each is one.

Syntax is required *here and only here*: projection is a syntactic operation, so
the global program must be an object we can recurse over. Every constructor is a
proof obligation forever, so there are four:

  * `done` — the base case; without it nothing is finite.
  * `write` — the only way state changes. It names **which replica** acts (so the
    configuration semantics can touch one component) and carries a
    `Delta.DeltaMutator`, i.e. exactly a *monotone* operation presented with its
    patch (`Delta.ofInflationary` shows the interface is monotonicity, no more).
  * `read` — reads-into-computation. It names **which replica** observes, because
    in a replicated store a read is answered by *someone's* copy and copies differ;
    that `r` is load-bearing in `denote` and in `ReadsAgree`, and its absence from
    `project` is the honest statement that a projected read sends no message.
  * `sync` — the coordination node. Everything this file decides is "may this node
    be deleted", so it must be a constructor and not an annotation.
-/

/-- **A choreography over replica-owned CRDT state.** `R` is the replica alphabet,
`S` the merge lattice each replica holds a copy of. -/
inductive Choreo (R : Type v) (S : Type u) [MergeState S] : Type (max u v) where
  /-- The empty choreography. -/
  | done : Choreo R S
  /-- Replica `r` applies the (monotone) mutator `m` to its own copy. -/
  | write (r : R) (m : DeltaMutator S) (k : Choreo R S) : Choreo R S
  /-- Replica `r` observes its own copy with `o`; the choreography branches. -/
  | read (r : R) (o : S → Bool) (kt kf : Choreo R S) : Choreo R S
  /-- A barrier: every roster replica ends holding the join of the roster. -/
  | sync (k : Choreo R S) : Choreo R S

/-- **A configuration**: what each replica currently holds. This is where
"replica-owned" lives — there is no single global state to write to. -/
abbrev Cfg (R : Type v) (S : Type u) := R → S

variable {R : Type v} {S : Type u} [MergeState S] [DecidableEq R]

/-- Point-update of a configuration: only replica `r`'s copy changes. -/
def upd (κ : Cfg R S) (r : R) (s : S) : Cfg R S :=
  fun p => if p = r then s else κ p

omit [MergeState S] in
@[simp] theorem upd_self (κ : Cfg R S) (r : R) (s : S) : upd κ r s r = s := by
  simp [upd]

omit [MergeState S] in
@[simp] theorem upd_other {κ : Cfg R S} {r : R} {s : S} {p : R} (h : p ≠ r) :
    upd κ r s p = κ p := by
  simp [upd, h]

/-! ## §2. The global semantics.

`denote rs c κ` runs the whole choreography from configuration `κ` over the
roster `rs`, and returns the final configuration — *not* a single state. A `sync`
replaces every replica's copy by the roster join `joinAll (κ p) (rs.map κ)`; that
this is the *same* value at every roster replica is `sync_agrees`, and it is the
only place `rs` is used. -/

/-- The global (god's-eye) semantics of a choreography. -/
def denote (rs : List R) : Choreo R S → Cfg R S → Cfg R S
  | .done, κ => κ
  | .write r m k, κ => denote rs k (upd κ r (m.op (κ r)))
  | .read r o kt kf, κ => if o (κ r) then denote rs kt κ else denote rs kf κ
  | .sync k, κ => denote rs k (fun p => joinAll (κ p) (rs.map κ))

omit [DecidableEq R] in
/-- **A barrier makes every roster replica equal** — and to the *same* value, with
no dependence on which replica's copy seeded the fold. This is
`Delta.joinAll`'s least-upper-bound characterisation: both sides dominate exactly
the roster's states, so they are the same point of the lattice. It is why `sync`
"loses nothing and adds nothing" (`Confluence.merge_le_iff`) at the choreography
altitude. -/
theorem sync_agrees (rs : List R) (κ : Cfg R S) {p q : R} (hp : p ∈ rs) (hq : q ∈ rs) :
    joinAll (κ p) (rs.map κ) = joinAll (κ q) (rs.map κ) := by
  have hmp : κ p ∈ rs.map κ := List.mem_map.mpr ⟨p, hp, rfl⟩
  have hmq : κ q ∈ rs.map κ := List.mem_map.mpr ⟨q, hq, rfl⟩
  refine leq_antisymm ?_ ?_
  · exact joinAll_le (mem_le_joinAll hmp _) (fun d hd => mem_le_joinAll hd _)
  · exact joinAll_le (mem_le_joinAll hmq _) (fun d hd => mem_le_joinAll hd _)

/-! ## §3. Endpoint projection.

`Local` is the choreography with the replica annotations erased and the actions
that are not mine dropped — four constructors, mirroring `Choreo`'s.

The one asymmetry worth staring at: `project` **ignores** the `read`'s replica.
A projected read is "evaluate `o` on my own copy", at *every* replica; no message
is sent. That is faithful to a CRDT deployment (there is no channel), and it is
exactly why `ReadsAgree` below is a hypothesis carried into `projection_sound`
rather than a theorem. The communicated alternative is the explicitly distinct
`select`/`branch` adapter in `Uwueave.ChoreoChoice`; it does not change this
silent constructor's semantics. -/

/-- **A local (endpoint) program** — what one replica actually runs. -/
inductive Local (S : Type u) [MergeState S] : Type u where
  /-- Nothing further. -/
  | fin : Local S
  /-- Apply this mutator to my copy. -/
  | act (m : DeltaMutator S) (k : Local S) : Local S
  /-- Branch on my own copy. -/
  | obs (o : S → Bool) (kt kf : Local S) : Local S
  /-- Block until the barrier's join is delivered to me. -/
  | barrier (k : Local S) : Local S

/-- **Endpoint projection** `c ↾ p`. Writes by other replicas are erased (a
non-participant has no action); a read projects uniformly; a `sync` becomes a
`barrier`. -/
def project : Choreo R S → R → Local S
  | .done, _ => .fin
  | .write r m k, p => if p = r then .act m (project k p) else project k p
  | .read _ o kt kf, p => .obs o (project kt p) (project kf p)
  | .sync k, p => .barrier (project k p)

/-- **The local run**, against an explicit **delivery stream**: at the `n`-th
barrier the replica merges the `n`-th delivered state. A barrier with nothing
delivered is a no-op — the local semantics cannot invent a message, which is
what makes the stream the honest carrier of "what the network did". -/
def lrun : Local S → List S → S → S
  | .fin, _, s => s
  | .act m k, ds, s => lrun k ds (m.op s)
  | .obs o kt kf, ds, s => if o s then lrun kt ds s else lrun kf ds s
  | .barrier k, [], s => lrun k [] s
  | .barrier k, d :: ds, s => lrun k ds (s ⊔ d)

/-- The delivery stream the global run supplies to replica `p`: the roster join
at each barrier the run passes through. -/
def deliveries (rs : List R) : Choreo R S → Cfg R S → R → List S
  | .done, _, _ => []
  | .write r m k, κ, p => deliveries rs k (upd κ r (m.op (κ r))) p
  | .read r o kt kf, κ, p =>
      if o (κ r) then deliveries rs kt κ p else deliveries rs kf κ p
  | .sync k, κ, p =>
      joinAll (κ p) (rs.map κ) :: deliveries rs k (fun q => joinAll (κ q) (rs.map κ)) p

/-- **The read hypothesis**: every read the run performs is answered the same way
at every replica as at the replica the global semantics reads. Structurally
recursive along the same run `denote` takes, so it constrains exactly the reads
that actually fire. -/
def ReadsAgree (rs : List R) : Choreo R S → Cfg R S → Prop
  | .done, _ => True
  | .write r m k, κ => ReadsAgree rs k (upd κ r (m.op (κ r)))
  | .read r o kt kf, κ =>
      (∀ p, o (κ p) = o (κ r)) ∧
      (if o (κ r) then ReadsAgree rs kt κ else ReadsAgree rs kf κ)
  | .sync k, κ => ReadsAgree rs k (fun q => joinAll (κ q) (rs.map κ))

/-- **`projection_sound` — endpoint projection is faithful, pointwise.** For every
replica, the *projected local program*, run on that replica's own copy against
the deliveries the global run supplies, lands on **exactly** that replica's
component of the global denotation. All four constructors; the only hypothesis is
that the reads agreed.

This is the cleanest faithful statement for this fragment, and it is stronger
than the head-duality that `Dregg2.Coordination.projection_sound` reaches for
MPST: there is no bisimulation to build because there are no channels — the
composed local behaviour *is* the configuration, on the nose. -/
theorem projection_sound (rs : List R) :
    ∀ (c : Choreo R S) (κ : Cfg R S), ReadsAgree rs c κ → ∀ p : R,
      denote rs c κ p = lrun (project c p) (deliveries rs c κ p) (κ p) := by
  intro c
  induction c with
  | done => intro κ _ p; rfl
  | write r m k ih =>
    intro κ h p
    simp only [denote, deliveries, project, ReadsAgree] at *
    by_cases hpr : p = r
    · subst hpr
      have := ih (upd κ p (m.op (κ p))) h p
      simpa using this
    · simp only [if_neg hpr]
      have := ih (upd κ r (m.op (κ r))) h p
      simpa [upd_other hpr] using this
  | read r o kt kf iht ihf =>
    intro κ h p
    obtain ⟨hagree, hbranch⟩ := h
    simp only [denote, deliveries, project, lrun, hagree p]
    by_cases ho : o (κ r) = true
    · simp only [ho, if_pos] at hbranch ⊢
      exact iht κ hbranch p
    · simp only [ho, if_neg, Bool.not_eq_true] at hbranch ⊢
      exact ihf κ hbranch p
  | sync k ih =>
    intro κ h p
    simp only [denote, deliveries, project, lrun, ReadsAgree] at *
    have habs : κ p ⊔ joinAll (κ p) (rs.map κ) = joinAll (κ p) (rs.map κ) :=
      le_joinAll (κ p) (rs.map κ)
    rw [habs]
    exact ih (fun q => joinAll (κ q) (rs.map κ)) h p

/-! ### The sync-free reading: no barriers, so no deliveries. -/

/-- Sync-free: the choreography contains no barrier. -/
def SyncFree : Choreo R S → Prop
  | .done => True
  | .write _ _ k => SyncFree k
  | .read _ _ kt kf => SyncFree kt ∧ SyncFree kf
  | .sync _ => False

/-- Read-free: the choreography branches on nothing. -/
def ReadFree : Choreo R S → Prop
  | .done => True
  | .write _ _ k => ReadFree k
  | .read _ _ _ _ => False
  | .sync k => ReadFree k

/-- A read-free choreography discharges the read hypothesis outright — there are
no reads to disagree about. -/
theorem readFree_readsAgree (rs : List R) :
    ∀ (c : Choreo R S) (κ : Cfg R S), ReadFree c → ReadsAgree rs c κ := by
  intro c
  induction c with
  | done => intro _ _; trivial
  | write r m k ih => intro κ h; exact ih _ h
  | read r o kt kf _ _ => intro _ h; exact absurd h (by simp [ReadFree])
  | sync k ih => intro κ h; exact ih _ h

/-- **A barrier discharges the read hypothesis.** After a `sync` every roster
replica holds the same state (`sync_agrees`), so the read that follows agrees at
every replica. This is the formal content of "put the read after the sync". -/
theorem readsAgree_sync_read (rs : List R) (κ : Cfg R S) (r : R) (o : S → Bool)
    (kt kf : Choreo R S) (hall : ∀ z : R, z ∈ rs) (hr : r ∈ rs)
    (ht : ReadsAgree rs kt (fun q => joinAll (κ q) (rs.map κ)))
    (hf : ReadsAgree rs kf (fun q => joinAll (κ q) (rs.map κ))) :
    ReadsAgree rs (Choreo.sync (Choreo.read r o kt kf)) κ := by
  refine ⟨fun p => ?_, ?_⟩
  · exact congrArg o (sync_agrees rs κ (hall p) hr)
  · split <;> assumption

/-- A sync-free run delivers nothing — the whole coordination budget of a
choreography is its barriers. -/
theorem deliveries_of_syncFree (rs : List R) :
    ∀ (c : Choreo R S) (κ : Cfg R S), SyncFree c → ∀ p : R, deliveries rs c κ p = [] := by
  intro c
  induction c with
  | done => intro _ _ _; rfl
  | write r m k ih => intro κ h p; exact ih _ h p
  | read r o kt kf iht ihf =>
    intro κ h p
    simp only [deliveries]
    split
    · exact iht κ h.1 p
    · exact ihf κ h.2 p
  | sync k _ => intro _ h _; exact absurd h (by simp [SyncFree])

/-- `projection_sound` for the sync-free fragment: no deliveries at all, so the
projected local program alone reproduces the replica's global component. -/
theorem projection_sound_syncFree (rs : List R) (c : Choreo R S) (κ : Cfg R S)
    (hsf : SyncFree c) (h : ReadsAgree rs c κ) (p : R) :
    denote rs c κ p = lrun (project c p) [] (κ p) := by
  rw [projection_sound rs c κ h p, deliveries_of_syncFree rs c κ hsf p]

/-! ## §4. The verdict theorem, positive half — coordination-free convergence.

The statement quantifies over **delivery**, not over a fixed schedule: two
replicas, each running only its own projection, each merging an *arbitrary* list
of the run's results — any order, any duplication, any batching, as long as the
content is the run's results — reach **the same state**. `Delta`'s three laws are
what make "content" the only thing that matters. -/

/-- Every write in the choreography preserves `I` locally (Bailis's
abort-on-local-violation, folded into the mutator). -/
def WritesSafe (I : Invariant S) : Choreo R S → Prop
  | .done => True
  | .write _ m k => (∀ s, I s → I (m.op s)) ∧ WritesSafe I k
  | .read _ _ kt kf => WritesSafe I kt ∧ WritesSafe I kf
  | .sync k => WritesSafe I k

/-- An I-confluent invariant survives a whole fold of joins. -/
theorem joinAll_preserves {I : Invariant S} (hI : IConfluent I) :
    ∀ (l : List S) (base : S), I base → (∀ d ∈ l, I d) → I (joinAll base l)
  | [], _, hb, _ => hb
  | d :: l, base, hb, hd =>
      joinAll_preserves hI l (base ⊔ d) (hI _ _ hb (hd d (by simp)))
        (fun e he => hd e (by simp [he]))

/-- **The global run keeps the invariant** at every replica: writes are locally
safe by hypothesis and barriers are safe by I-confluence. -/
theorem denote_preserves {I : Invariant S} (hI : IConfluent I) (rs : List R) :
    ∀ (c : Choreo R S) (κ : Cfg R S), WritesSafe I c → (∀ z, I (κ z)) →
      ∀ p : R, I (denote rs c κ p) := by
  intro c
  induction c with
  | done => intro _ _ hκ p; exact hκ p
  | write r m k ih =>
    intro κ h hκ p
    refine ih _ h.2 (fun z => ?_) p
    by_cases hzr : z = r
    · subst hzr; rw [upd_self]; exact h.1 _ (hκ z)
    · rw [upd_other hzr]; exact hκ z
  | read r o kt kf iht ihf =>
    intro κ h hκ p
    simp only [denote]
    split
    · exact iht κ h.1 hκ p
    · exact ihf κ h.2 hκ p
  | sync k ih =>
    intro κ h hκ p
    refine ih _ h (fun z => ?_) p
    exact joinAll_preserves hI _ _ (hκ z)
      (fun d hd => by obtain ⟨w, _, rfl⟩ := List.mem_map.mp hd; exact hκ w)

/-- **The verdict theorem, positive half — convergence under arbitrary delivery.**

Let `c` be sync-free and let its reads agree. Then for any two roster replicas
`p`, `q` and **any** two delivery lists whose *content* is the run's per-replica
results, the states reached are equal:

    joinAll (c↾p run at p) ds  =  joinAll (c↾q run at q) ds'

The two lists need not be permutations of each other, need not be duplicate-free,
and need not be the same length — only their membership matters. That is
`Delta.joinAll`'s least-upper-bound characterisation doing the work
(`Delta.same_deltas_same_state` is the same argument at a fixed base). -/
theorem coordination_free_converges
    (rs : List R) (c : Choreo R S) (κ : Cfg R S)
    (hsf : SyncFree c) (h : ReadsAgree rs c κ)
    {p q : R} (hp : p ∈ rs) (hq : q ∈ rs) (ds ds' : List S)
    (hds : ∀ d, d ∈ ds ↔ ∃ x, x ∈ rs ∧ d = denote rs c κ x)
    (hds' : ∀ d, d ∈ ds' ↔ ∃ x, x ∈ rs ∧ d = denote rs c κ x) :
    joinAll (lrun (project c p) [] (κ p)) ds
      = joinAll (lrun (project c q) [] (κ q)) ds' := by
  rw [← projection_sound_syncFree rs c κ hsf h p,
      ← projection_sound_syncFree rs c κ hsf h q]
  refine leq_antisymm ?_ ?_
  · refine joinAll_le (mem_le_joinAll ((hds' _).mpr ⟨p, hp, rfl⟩) _) (fun d hd => ?_)
    obtain ⟨x, hx, rfl⟩ := (hds d).mp hd
    exact mem_le_joinAll ((hds' _).mpr ⟨x, hx, rfl⟩) _
  · refine joinAll_le (mem_le_joinAll ((hds _).mpr ⟨q, hq, rfl⟩) _) (fun d hd => ?_)
    obtain ⟨x, hx, rfl⟩ := (hds' d).mp hd
    exact mem_le_joinAll ((hds _).mpr ⟨x, hx, rfl⟩) _

/-- **…and the converged state is legal.** Whatever a replica merges, as long as
every delivered state is one the run produced, the invariant holds — from
I-confluence and local write-safety alone. -/
theorem coordination_free_safe {I : Invariant S} (hI : IConfluent I)
    (rs : List R) (c : Choreo R S) (κ : Cfg R S)
    (hws : WritesSafe I c) (hκ : ∀ z, I (κ z)) (p : R) (ds : List S)
    (hds : ∀ d ∈ ds, ∃ x, x ∈ rs ∧ d = denote rs c κ x) :
    I (joinAll (denote rs c κ p) ds) :=
  joinAll_preserves hI ds _ (denote_preserves hI rs c κ hws hκ p)
    (fun d hd => by obtain ⟨x, _, rfl⟩ := hds d hd; exact denote_preserves hI rs c κ hws hκ x)

/-! ## §5. The verdict theorem, iff-shaped — and the refutation.

`red_iff_coupled` rebuilt on this library's judgement. Two moves make the iff
honest rather than definitional:

  * the **spec** `CoordFree` is a property of *running the choreography with no
    barriers*, not a synonym for `IConfluent`; and
  * the family it is quantified over is **locally checked** (`guardedJoin` aborts
    exactly like `Necessity.bitAtMostOneImpl`), so the backward direction is not
    free — a write that would break `I` simply does not commit.

Neither direction is `Iff.rfl`. -/

/-- **The choreography-level coordination-freedom spec**: running `c` from any
legal configuration, with the reads agreed, every pair of replicas merges
legally. This is what "this choreography needs no coordination" *means*. -/
def CoordFree (rs : List R) (I : Invariant S) (c : Choreo R S) : Prop :=
  ∀ κ : Cfg R S, (∀ z, I (κ z)) → ReadsAgree rs c κ →
    ∀ p q : R, I (denote rs c κ p ⊔ denote rs c κ q)

/-- Erase every barrier. This is the operation the verdict is *about*: "can this
choreography drop its coordination?" is "does `desync c` still meet the spec?" -/
def desync : Choreo R S → Choreo R S
  | .done => .done
  | .write r m k => .write r m (desync k)
  | .read r o kt kf => .read r o (desync kt) (desync kf)
  | .sync k => desync k

omit [DecidableEq R] in
theorem desync_syncFree : ∀ c : Choreo R S, SyncFree (desync c)
  | .done => trivial
  | .write _ _ k => desync_syncFree k
  | .read _ _ kt kf => ⟨desync_syncFree kt, desync_syncFree kf⟩
  | .sync k => desync_syncFree k

omit [DecidableEq R] in
theorem desync_of_syncFree : ∀ (c : Choreo R S), SyncFree c → desync c = c
  | .done, _ => rfl
  | .write r m k, h => by rw [desync, desync_of_syncFree k h]
  | .read r o kt kf, h => by
      rw [desync, desync_of_syncFree kt h.1, desync_of_syncFree kf h.2]
  | .sync _, h => absurd h (by simp [SyncFree])

omit [DecidableEq R] in
theorem desync_writesSafe {I : Invariant S} :
    ∀ (c : Choreo R S), WritesSafe I c → WritesSafe I (desync c)
  | .done, _ => trivial
  | .write _ _ k, h => ⟨h.1, desync_writesSafe k h.2⟩
  | .read _ _ kt kf, h => ⟨desync_writesSafe kt h.1, desync_writesSafe kf h.2⟩
  | .sync k, h => desync_writesSafe k h

/-- **`c` realizes the pair `(x, y)`**: some legal configuration, with the reads
agreed, drives one replica to `x` and another to `y`. This is the reachability
premise the *necessity* direction needs — a lattice clash that no run can reach
must not condemn a choreography, exactly the gap `Uwueave.Necessity` names
between `¬ IConfluent` and `ReachableClash`. -/
def Realizes (rs : List R) (I : Invariant S) (c : Choreo R S) (x y : S) : Prop :=
  ∃ (κ : Cfg R S) (p q : R), (∀ z, I (κ z)) ∧ ReadsAgree rs c κ ∧
    denote rs c κ p = x ∧ denote rs c κ q = y

/-- **Necessity**: a choreography that can *reach* a legal pair and still meets
the coordination-free spec proves that pair merges legally. Realize every legal
pair and you have proved `IConfluent`. -/
theorem iconfluent_of_coordFree {I : Invariant S} (rs : List R) (F : S → S → Choreo R S)
    (hsat : ∀ x y, I x → I y → Realizes rs I (F x y) x y)
    (hcf : ∀ x y, I x → I y → CoordFree rs I (F x y)) :
    IConfluent I := by
  intro x y hx hy
  obtain ⟨κ, p, q, hκ, hra, hpx, hqy⟩ := hsat x y hx hy
  have := hcf x y hx hy κ hκ hra p q
  rwa [hpx, hqy] at this

/-- **Sufficiency**: an I-confluent invariant with locally-safe writes meets the
spec, for *any* choreography — barriers or none. -/
theorem coordFree_of_iconfluent {I : Invariant S} (hI : IConfluent I) (rs : List R)
    (c : Choreo R S) (hws : WritesSafe I c) : CoordFree rs I c :=
  fun κ hκ _ p q =>
    hI _ _ (denote_preserves hI rs c κ hws hκ p) (denote_preserves hI rs c κ hws hκ q)

/-! ### The saturating family — a concrete, locally-checked, sync-free witness. -/

/-- **A locally-checked join-in write.** Merge `x` into my copy *if the result is
still legal*, otherwise do nothing. Every such write is `WritesSafe` by
construction (the guard is the proof), and it is a `DeltaMutator` because both
branches are inflationary. This is `Necessity.bitAtMostOneImpl`'s
insert-or-abort, generically. -/
def guardedJoin (I : Invariant S) [DecidablePred I] (x : S) : DeltaMutator S :=
  ofInflationary (fun s => if I (s ⊔ x) then s ⊔ x else s)
    (fun s => by
      show s ⊑ (if I (s ⊔ x) then s ⊔ x else s)
      by_cases h : I (s ⊔ x)
      · rw [if_pos h]; exact le_merge_left s x
      · rw [if_neg h]; exact leq_refl s)

theorem guardedJoin_safe (I : Invariant S) [DecidablePred I] (x : S) :
    ∀ s, I s → I ((guardedJoin I x).op s) := by
  intro s hs
  show I (if I (s ⊔ x) then s ⊔ x else s)
  by_cases h : I (s ⊔ x)
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact hs

/-- **The saturating family**: replica `p` guard-joins `x`, replica `q`
guard-joins `y`, no barrier. Sync-free and locally safe by construction. -/
def satFamily (I : Invariant S) [DecidablePred I] (p q : R) (x y : S) : Choreo R S :=
  .write p (guardedJoin I x) (.write q (guardedJoin I y) .done)

omit [DecidableEq R] in
theorem satFamily_syncFree (I : Invariant S) [DecidablePred I] (p q : R) (x y : S) :
    SyncFree (satFamily I p q x y) := trivial

omit [DecidableEq R] in
theorem satFamily_readFree (I : Invariant S) [DecidablePred I] (p q : R) (x y : S) :
    ReadFree (satFamily I p q x y) := trivial

omit [DecidableEq R] in
theorem satFamily_writesSafe (I : Invariant S) [DecidablePred I] (p q : R) (x y : S) :
    WritesSafe I (satFamily I p q x y) :=
  ⟨guardedJoin_safe I x, guardedJoin_safe I y, trivial⟩

/-- The family really does saturate: from a legal bottom, `p` lands on `x` and `q`
lands on `y`, for every legal pair. -/
theorem satFamily_realizes {I : Invariant S} [DecidablePred I]
    (rs : List R) (bot : S) (hbot : ∀ s : S, bot ⊔ s = s) (hIbot : I bot)
    {p q : R} (hpq : p ≠ q) (x y : S) (hx : I x) (hy : I y) :
    Realizes rs I (satFamily I p q x y) x y := by
  refine ⟨fun _ => bot, p, q, fun _ => hIbot, readFree_readsAgree rs _ _ trivial, ?_, ?_⟩
  · show denote rs (.write q (guardedJoin I y) .done)
        (upd (fun _ => bot) p ((guardedJoin I x).op bot)) p = x
    show upd (upd (fun _ => bot) p ((guardedJoin I x).op bot)) q
        ((guardedJoin I y).op _) p = x
    rw [upd_other hpq, upd_self]
    show (if I (bot ⊔ x) then bot ⊔ x else bot) = x
    rw [hbot x, if_pos hx]
  · show upd (upd (fun _ => bot) p ((guardedJoin I x).op bot)) q
        ((guardedJoin I y).op (upd (fun _ => bot) p ((guardedJoin I x).op bot) q)) q = y
    rw [upd_self, upd_other (Ne.symm hpq)]
    show (if I (bot ⊔ y) then bot ⊔ y else bot) = y
    rw [hbot y, if_pos hy]

/-- **THE VERDICT THEOREM, iff-shaped.**

> For the sync-free, locally-checked saturating family over a lattice with a legal
> bottom: **the family meets the coordination-free spec ⟺ `I` is I-confluent.**

Neither direction is a definitional unfold. Forward (necessity) goes through an
actual *run* that reaches the clashing pair — so it is a statement about
reachability, not about the lattice alone. Backward (sufficiency) uses the merge
law plus the fact that every write in the family is locally checked.

This is `Dregg2.Spec.Choreography.red_iff_coupled` rebuilt on this library's
judgement: theirs classifies one interaction and its first half is `Iff.rfl`;
this classifies a whole choreography and neither half is. -/
theorem coordination_free_iff_iconfluent {I : Invariant S} [DecidablePred I]
    (rs : List R) (bot : S) (hbot : ∀ s : S, bot ⊔ s = s) (hIbot : I bot)
    {p q : R} (hpq : p ≠ q) :
    (∀ x y, I x → I y → CoordFree rs I (satFamily I p q x y)) ↔ IConfluent I := by
  constructor
  · exact fun hcf =>
      iconfluent_of_coordFree rs (satFamily I p q)
        (fun x y hx hy => satFamily_realizes rs bot hbot hIbot hpq x y hx hy) hcf
  · exact fun hI x y _ _ =>
      coordFree_of_iconfluent hI rs _ (satFamily_writesSafe I p q x y)

/-- **The refutation: a barrier that cannot be dropped, with a witness.**

If `I` is not I-confluent then some member of the saturating family *fails* the
coordination-free spec — there is a concrete legal pair `(x, y)` whose sync-free
choreography breaks the global spec. Running it and merging is the repro.

(Together with `desync_syncFree` and `desync_of_syncFree`: the family *is* its own
desynced form, so this is literally "delete the barrier and the spec breaks".) -/
theorem sync_cannot_be_dropped {I : Invariant S} [DecidablePred I]
    (rs : List R) (bot : S) (hbot : ∀ s : S, bot ⊔ s = s) (hIbot : I bot)
    {p q : R} (hpq : p ≠ q) (hbad : ¬ IConfluent I) :
    ∃ x y, I x ∧ I y ∧ ¬ CoordFree rs I (satFamily I p q x y) := by
  apply Classical.byContradiction
  intro hcon
  refine hbad ((coordination_free_iff_iconfluent rs bot hbot hIbot hpq).mp ?_)
  intro x y hx hy
  apply Classical.byContradiction
  intro hnot
  exact hcon ⟨x, y, hx, hy, hnot⟩

/-! ## §6. The seam refinement — coordination only where `σ` moves.

Past the prior art. `Dregg2`'s choreography layer knows two colours; a clash there
sends the interaction to an atomic joint commit. Whittaker–Hellerstein's
refinement says that is often far too much: the invariant may be confluent
*within the fibers of a projection* `σ`, so coordination is needed only to change
`σ`. `Uwueave.Segmented` has that judgement; this section reads it at the
choreography altitude, which `Dregg2/Coordination.lean`, `Dregg2/Projection.lean`
and `Dregg2/Spec/Choreography.lean` do not do (zero occurrences of
`SegmentedIConfluent` between them).

The punchline pair is the same invariant twice (§8): `spendChoreo` is fiber-local
and runs free; `realloc` moves `σ` and its desynced run breaks the invariant. -/

/-- A mutator is **fiber-local** for the seam `σ` when it never leaves the fiber:
the write is one a replica may perform between coordination events. -/
def FiberLocal {Seg : Type w} (σ : S → Seg) (m : DeltaMutator S) : Prop :=
  ∀ s, σ (m.op s) = σ s

/-- **The seam-disciplined fragment**: no barrier, and every write fiber-local —
a choreography that lives entirely inside one fiber of `σ`. -/
def FiberFree {Seg : Type w} (σ : S → Seg) : Choreo R S → Prop
  | .done => True
  | .write _ m k => FiberLocal σ m ∧ FiberFree σ k
  | .read _ _ kt kf => FiberFree σ kt ∧ FiberFree σ kf
  | .sync _ => False

omit [DecidableEq R] in
theorem fiberFree_syncFree {Seg : Type w} {σ : S → Seg} :
    ∀ c : Choreo R S, FiberFree σ c → SyncFree c
  | .done, _ => trivial
  | .write _ _ k, h => fiberFree_syncFree k h.2
  | .read _ _ kt kf, h => ⟨fiberFree_syncFree kt h.1, fiberFree_syncFree kf h.2⟩
  | .sync _, h => h

/-- **The fiber is preserved by the whole run.** Nothing a seam-disciplined
choreography does moves any replica out of its fiber. -/
theorem fiberFree_denote_stays {Seg : Type w} {σ : S → Seg} (rs : List R) :
    ∀ (c : Choreo R S) (κ : Cfg R S), FiberFree σ c → ∀ p : R,
      σ (denote rs c κ p) = σ (κ p) := by
  intro c
  induction c with
  | done => intro _ _ _; rfl
  | write r m k ih =>
    intro κ h p
    rw [show denote rs (Choreo.write r m k) κ = denote rs k (upd κ r (m.op (κ r))) from rfl,
        ih _ h.2 p]
    by_cases hpr : p = r
    · subst hpr; rw [upd_self]; exact h.1 (κ p)
    · rw [upd_other hpr]
  | read r o kt kf iht ihf =>
    intro κ h p
    simp only [denote]
    split
    · exact iht κ h.1 p
    · exact ihf κ h.2 p
  | sync _ _ => intro _ h _; exact absurd h (by simp [FiberFree])

/-- A sync-free run keeps the invariant with **no** confluence hypothesis: there is
no merge inside it, so local write-safety is the whole story. -/
theorem denote_preserves_syncFree {I : Invariant S} (rs : List R) :
    ∀ (c : Choreo R S) (κ : Cfg R S), SyncFree c → WritesSafe I c → (∀ z, I (κ z)) →
      ∀ p : R, I (denote rs c κ p) := by
  intro c
  induction c with
  | done => intro _ _ _ hκ p; exact hκ p
  | write r m k ih =>
    intro κ hsf h hκ p
    refine ih _ hsf h.2 (fun z => ?_) p
    by_cases hzr : z = r
    · subst hzr; rw [upd_self]; exact h.1 _ (hκ z)
    · rw [upd_other hzr]; exact hκ z
  | read r o kt kf iht ihf =>
    intro κ hsf h hκ p
    simp only [denote]
    split
    · exact iht κ hsf.1 h.1 hκ p
    · exact ihf κ hsf.2 h.2 hκ p
  | sync _ _ => intro _ hsf _ _ _; exact absurd hsf (by simp [SyncFree])

/-- **THE SEAM REFINEMENT.** A choreography whose every write is fiber-local and
which contains **no barrier** runs coordination-free *inside a fiber*: starting
from a configuration all in one fiber, every pair of replicas merges
invariant-safely **and** the merge stays in the fiber.

Read the hypotheses: there is **no `IConfluent`** anywhere. The whole guarantee
comes from `Segmented.SegmentedIConfluent σ I`, whose second conjunct (the fiber
is closed under the merge) is exactly what stops a sync from teleporting replicas
across the seam behind the program's back. Coordination is needed only where `σ`
moves — and a write that moves `σ` is, by definition, not `FiberLocal`. -/
theorem seam_coordination_free {Seg : Type w} {σ : S → Seg} {I : Invariant S}
    (hseg : SegmentedIConfluent σ I) (rs : List R) (c : Choreo R S) (κ : Cfg R S)
    (hff : FiberFree σ c) (hws : WritesSafe I c)
    (hκ : ∀ z, I (κ z)) (hfib : ∀ z z', σ (κ z) = σ (κ z')) (p q : R) :
    I (denote rs c κ p ⊔ denote rs c κ q)
    ∧ σ (denote rs c κ p ⊔ denote rs c κ q) = σ (κ p) := by
  have hsf := fiberFree_syncFree c hff
  have hIp := denote_preserves_syncFree rs c κ hsf hws hκ p
  have hIq := denote_preserves_syncFree rs c κ hsf hws hκ q
  have hσ : σ (denote rs c κ p) = σ (denote rs c κ q) := by
    rw [fiberFree_denote_stays rs c κ hff p, fiberFree_denote_stays rs c κ hff q]
    exact hfib p q
  obtain ⟨hI, hσ'⟩ := hseg _ _ hσ hIp hIq
  exact ⟨hI, by rw [hσ', fiberFree_denote_stays rs c κ hff p]⟩

/-! ## §7. The verdict carrier.

Carried the way this library carries verdicts (`Spec.Verdict`, `Spec.SegVerdict`):
never a `Bool`, always the evidence. Three answers, and `toSpecVerdict` demotes any
of them to the existing state-level carrier for a consumer that only understands
the binary judgement. -/

/-- **The coordination verdict on a whole choreography.**

(The universe is one above `S`/`R`'s because `seam` quantifies over the seam
*type* — an existential over `Type u` is a `Type (u+1)` field. `Spec.SegVerdict`
takes its `Seg` as a parameter and so stays small; here the seam is part of the
answer, not part of the question.) -/
inductive Verdict (rs : List R) (I : Invariant S) (c : Choreo R S) :
    Type (max (u + 1) (v + 1)) where
  /-- No barriers, every write locally safe, invariant I-confluent: the
  choreography is coordination-free (`free_coordFree`). -/
  | free (hsf : SyncFree c) (hws : WritesSafe I c) (hI : IConfluent I)
  /-- Not free globally — the carried `SegVerdict` refutes that with a repro — but
  the choreography lives inside one fiber of the seam, so it runs free anyway
  (`seam_stays`). -/
  | seam {Seg : Type u} (v : Spec.SegVerdict I Seg) (hws : WritesSafe I c)
      (hff : FiberFree v.σ c)
  /-- Coupled: a concrete legal pair whose merge is illegal. The barrier stays. -/
  | coupled (x y : S) (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y))

namespace Verdict

/-- A `free` verdict's payoff, both halves: the choreography meets the
coordination-free spec (from `hws`/`hI`), **and** it asks the network for nothing
— `SyncFree` means the run delivers an empty stream to every replica, so there is
no barrier to be late. -/
theorem free_payoff {rs : List R} {I : Invariant S} {c : Choreo R S}
    (hsf : SyncFree c) (hws : WritesSafe I c) (hI : IConfluent I) :
    CoordFree rs I c ∧ ∀ (κ : Cfg R S) (p : R), deliveries rs c κ p = [] :=
  ⟨coordFree_of_iconfluent hI rs c hws, fun κ p => deliveries_of_syncFree rs c κ hsf p⟩

/-- A `seam` verdict's payoff: fiber-safety *and* fiber-preservation, from the
segmented judgement alone. -/
theorem seam_stays {rs : List R} {I : Invariant S} {c : Choreo R S} {Seg : Type u}
    (v : Spec.SegVerdict I Seg) (hws : WritesSafe I c) (hff : FiberFree v.σ c)
    (κ : Cfg R S) (hκ : ∀ z, I (κ z)) (hfib : ∀ z z', v.σ (κ z) = v.σ (κ z')) (p q : R) :
    I (denote rs c κ p ⊔ denote rs c κ q)
    ∧ v.σ (denote rs c κ p ⊔ denote rs c κ q) = v.σ (κ p) :=
  seam_coordination_free v.seamFree rs c κ hff hws hκ hfib p q

/-- Demote to the state-level carrier this library already ships. -/
def toSpecVerdict {rs : List R} {I : Invariant S} {c : Choreo R S} :
    Verdict rs I c → Spec.Verdict I
  | .free _ _ hI => .free hI
  | .seam v _ _ => v.toClash
  | .coupled x y hx hy hbad => .clash x y hx hy hbad

/-- The answer without the evidence — for reporting only. -/
def isFree {rs : List R} {I : Invariant S} {c : Choreo R S} : Verdict rs I c → Bool
  | .free .. => true
  | _ => false

omit [DecidableEq R] in
/-- **Neither non-`free` answer is a shrug.** A `seam` verdict carries a
`SegVerdict`, whose clash refutes global I-confluence
(`Spec.SegVerdict.escalatesGlobally`); a `coupled` verdict carries the clashing
pair directly. So a verdict that is not `free` always *knows why* — it never
means "we could not prove freedom". -/
theorem not_free_escalates {rs : List R} {I : Invariant S} {c : Choreo R S} :
    ∀ V : Verdict rs I c, V.isFree = false → ¬ IConfluent I
  | .free .., h => absurd h (by simp [isFree])
  | .seam v _ _, _ => v.escalatesGlobally
  | .coupled x y hx hy hbad, _ => fun hI => hbad (hI x y hx hy)

omit [DecidableEq R] in
/-- …and `toSpecVerdict` agrees with `isFree`: the demotion loses the seam, never
the answer. -/
theorem toSpecVerdict_isFree {rs : List R} {I : Invariant S} {c : Choreo R S} :
    ∀ V : Verdict rs I c, V.toSpecVerdict.isFree = V.isFree
  | .free .. => rfl
  | .seam .. => rfl
  | .coupled .. => rfl

end Verdict

/-! ## §8. Worked miniatures.

Three choreographies, one of each colour, over concrete state, with their verdicts
computed and their refutations run. -/

/-- Two replicas. -/
abbrev Rep := Bool

/-- The roster. -/
def roster : List Rep := [false, true]

theorem mem_roster : ∀ z : Rep, z ∈ roster := by decide

/-! ### §8.1 The loom: edits free, pin = sync.

A loom document is a grow-only node set and a pin — and a document has **at most
one pinned node**. Edits are the coordination-free part; the pin is the ceiling.
The pin set is `Necessity.BitSet` (two pinnable nodes), so the ceiling here is
literally the one `Uwueave.Necessity` refutes CFCS for: `atMostOneBitClash` is a
**reachable** clash — two locally-legal runs from a common ancestor — and
`atMostOneBit_impl_not_cfcs` refutes CFCS for the natural insert-or-abort
implementation, strictly more than the bare lattice pair. ⚠ It does **not** say
"no implementation can"; that modal reading is Bailis's Theorem 3.1, which
`Uwueave.Confluence` deliberately cites rather than states. What is proved below
is the choreography-altitude fact: *this* program, desynced, breaks *this*
document. -/

/-- The loom document: nodes, and the pin set. -/
abbrev LoomDoc := GSet Nat × Necessity.BitSet

/-- Genesis node present, at most one pin. -/
def loomInv : Invariant LoomDoc := fun d =>
  d.1 0 = true ∧ Necessity.AtMostOneBit d.2

instance : DecidablePred Necessity.AtMostOneBit := fun s => by
  unfold Necessity.AtMostOneBit; infer_instance

/-- Add a node — a grow-only write, free by `Catalog.gset_monotone_iconfluent`. -/
def addNode (n : Nat) : DeltaMutator LoomDoc :=
  ofInflationary (fun d => (fun m => d.1 m || (m == n), d.2))
    (fun d => by
      have h1 : d.1 ⊔ (fun m => d.1 m || (m == n)) = (fun m => d.1 m || (m == n)) := by
        funext m
        show (d.1 m || (d.1 m || (m == n))) = (d.1 m || (m == n))
        cases d.1 m <;> simp
      have h2 : d.2 ⊔ d.2 = d.2 := merge_idem d.2
      show (d.1 ⊔ (fun m => d.1 m || (m == n)), d.2 ⊔ d.2)
          = ((fun m => d.1 m || (m == n)), d.2)
      rw [h1, h2])

/-- Pin node `b` **if nothing is pinned yet** — the locally-checked write. Legal on
its own; the ceiling breaks only at the merge. -/
def pinIfFree (b : Bool) : DeltaMutator LoomDoc :=
  ofInflationary
    (fun d => if (d.2 true || d.2 false) = true then d
              else (d.1, fun x => d.2 x || (x == b)))
    (fun d => by
      show d ⊑ (if (d.2 true || d.2 false) = true then d
                else (d.1, fun x => d.2 x || (x == b)))
      by_cases h : (d.2 true || d.2 false) = true
      · rw [if_pos h]; exact merge_idem d
      · rw [if_neg h]
        have h1 : d.1 ⊔ d.1 = d.1 := merge_idem d.1
        have h2 : d.2 ⊔ (fun x => d.2 x || (x == b)) = (fun x => d.2 x || (x == b)) := by
          funext x
          show (d.2 x || (d.2 x || (x == b))) = (d.2 x || (x == b))
          cases d.2 x <;> simp
        show (d.1 ⊔ d.1, d.2 ⊔ (fun x => d.2 x || (x == b)))
            = (d.1, fun x => d.2 x || (x == b))
        rw [h1, h2])

theorem addNode_safe (n : Nat) : ∀ d, loomInv d → loomInv ((addNode n).op d) := by
  intro d hd
  refine ⟨?_, hd.2⟩
  show (d.1 0 || (0 == n)) = true
  rw [hd.1]; rfl

theorem pinIfFree_safe (b : Bool) : ∀ d, loomInv d → loomInv ((pinIfFree b).op d) := by
  intro d hd
  by_cases h : (d.2 true || d.2 false) = true
  · show loomInv (if (d.2 true || d.2 false) = true then _ else _)
    rw [if_pos h]; exact hd
  · show loomInv (if (d.2 true || d.2 false) = true then _ else _)
    rw [if_neg h]
    refine ⟨hd.1, ?_⟩
    have ht : d.2 true = false := by
      cases hx : d.2 true with
      | false => rfl
      | true => exact absurd (by rw [hx]; rfl) h
    have hf : d.2 false = false := by
      cases hx : d.2 false with
      | false => rfl
      | true => exact absurd (by rw [hx]; simp) h
    show (((d.2 true || (true == b))) && ((d.2 false || (false == b)))) = false
    rw [ht, hf]
    cases b <;> rfl

/-- The starting document: genesis node, nothing pinned. -/
def loomBase : LoomDoc := (fun n => n == 0, fun _ => false)

/-- Both replicas start from the same base. -/
def loomStart : Cfg Rep LoomDoc := fun _ => loomBase

/-- **The loom choreography.** Both replicas edit freely; the two pin attempts are
each preceded by a barrier, so the second one *sees* the first and declines. -/
def loom : Choreo Rep LoomDoc :=
  .write false (addNode 1)
    (.write true (addNode 2)
      (.sync
        (.write false (pinIfFree true)
          (.sync (.write true (pinIfFree false) .done)))))

theorem loom_writesSafe : WritesSafe loomInv loom :=
  ⟨addNode_safe 1, addNode_safe 2, pinIfFree_safe true, pinIfFree_safe false, trivial⟩

/-- **With the barriers, the document is legal.** The second pin attempt runs
against a state that already has the first pin, so it declines: exactly one node
is pinned in the merged document. -/
theorem loom_synced_legal :
    loomInv (denote roster loom loomStart false ⊔ denote roster loom loomStart true) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚠ **Delete the barriers and the document breaks.** `desync loom` is the same
program with both `sync` nodes erased: neither replica sees the other's pin, both
pin, and the merged document pins two nodes. This is the concrete witness that
the barrier is load-bearing — paste it into a test. -/
theorem loom_desynced_broken :
    ¬ loomInv (denote roster (desync loom) loomStart false
               ⊔ denote roster (desync loom) loomStart true) := by
  intro h
  have := h.2
  revert this
  decide

/-- **The loom's verdict: coupled.** The clash is the two-pin document — both
halves legal, the merge illegal. `Necessity.atMostOneBit_not_iconfluent` is the
same ceiling at the lattice altitude, and `Necessity.atMostOneBit_impl_not_cfcs`
at the implementation altitude (for the insert-or-abort implementation, via a
*reachable* clash). `loom_desynced_broken` is the barrier's necessity for **this**
program; that no program over this ceiling can drop it is Bailis's Theorem 3.1,
cited, not proved here. -/
def loomVerdict : Verdict roster loomInv loom :=
  .coupled
    (fun n => n == 0, fun x => x == true)
    (fun n => n == 0, fun x => x == false)
    ⟨rfl, by decide⟩ ⟨rfl, by decide⟩ (by intro h; have := h.2; revert this; decide)

/-- A read *without* a preceding barrier can disagree: replica `false` holding the
`true`-pin and replica `true` holding the `false`-pin answer "is `true` pinned?"
differently. `ReadsAgree` is not free, and `readsAgree_sync_read` is what buys
it. -/
theorem reads_can_disagree :
    ∃ (κ : Cfg Rep LoomDoc) (o : LoomDoc → Bool) (p r : Rep), o (κ p) ≠ o (κ r) := by
  refine ⟨fun z => (fun n => n == 0, fun x => x == z), fun d => d.2 true, false, true, ?_⟩
  decide

/-! ### §8.1b The disciplined read — barrier, then branch.

`read` is the constructor that says "and now the program depends on what the state
*is*". In a replicated store that is a coordination question, because copies
differ; `reads_can_disagree` above is the cost of asking it cold. The disciplined
shape is `sync (read …)`, and `readsAgree_sync_read` is what makes it sound. -/

/-- "Is anything pinned?" — the observation the loom branches on. -/
def loomPinned : LoomDoc → Bool := fun d => d.2 true || d.2 false

/-- **Barrier, then branch.** Replica `false` edits, everyone syncs, and only then
does the choreography ask whether anything is pinned — pinning only if not. -/
def loomRead : Choreo Rep LoomDoc :=
  .write false (addNode 1)
    (.sync
      (.read false loomPinned
        .done
        (.write false (pinIfFree true) .done)))

/-- The read hypothesis is **discharged**, at every configuration, by the barrier
that precedes it — no side condition survives to the user. -/
theorem loomRead_readsAgree (κ : Cfg Rep LoomDoc) : ReadsAgree roster loomRead κ :=
  readsAgree_sync_read roster (upd κ false ((addNode 1).op (κ false)))
    false loomPinned .done (.write false (pinIfFree true) .done)
    mem_roster (mem_roster false) trivial trivial

/-- **Projection, computed — the writer's endpoint.** It carries its own write, the
barrier, and the branch. -/
theorem project_loomRead_writer :
    project loomRead false
      = .act (addNode 1)
          (.barrier (.obs loomPinned .fin (.act (pinIfFree true) .fin))) := rfl

/-- **Projection, computed — the other endpoint.** The remote write is erased, but
the barrier and the *branch* remain: a projected read sends no message, so every
replica re-evaluates the same predicate on its own copy. That is the shape the
silent-read boundary in the header describes, and `loomRead_readsAgree` is why it
is safe here. `Uwueave.ChoreoChoice` takes the other route: its remote endpoint
consumes a delivered label instead of re-evaluating this predicate. -/
theorem project_loomRead_other :
    project loomRead true = .barrier (.obs loomPinned .fin .fin) := rfl

/-- The barrier-then-branch loom keeps the document legal. -/
theorem loomRead_legal :
    loomInv (denote roster loomRead loomStart false
             ⊔ denote roster loomRead loomStart true) := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### §8.1c A free choreography — the third verdict, and convergence run.

Drop the pin and the loom's remaining schema is grow-only: "genesis is present" is
I-confluent (`Catalog.gset_mem_iconfluent`), so both replicas edit with no barrier
at all and every delivery order lands on the same document. -/

/-- Add a node to a bare node set. -/
def addOnly (n : Nat) : DeltaMutator (GSet Nat) :=
  ofInflationary (fun s m => s m || (m == n))
    (fun s => by
      funext m
      show (s m || (s m || (m == n))) = (s m || (m == n))
      cases s m <;> simp)

/-- Genesis is present. -/
def nodesInv : Invariant (GSet Nat) := fun s => s 0 = true

theorem addOnly_safe (n : Nat) : ∀ s, nodesInv s → nodesInv ((addOnly n).op s) := by
  intro s hs
  show (s 0 || (0 == n)) = true
  rw [hs]; rfl

/-- Both replicas edit; no barrier anywhere. -/
def editChoreo : Choreo Rep (GSet Nat) :=
  .write false (addOnly 1) (.write true (addOnly 2) .done)

theorem editChoreo_writesSafe : WritesSafe nodesInv editChoreo :=
  ⟨addOnly_safe 1, addOnly_safe 2, trivial⟩

/-- **The `free` verdict**, with its evidence: no barriers, locally safe writes,
and an I-confluent invariant. -/
def editVerdict : Verdict roster nodesInv editChoreo :=
  .free trivial editChoreo_writesSafe (gset_mem_iconfluent 0)

/-- **The free verdict cashed out — convergence under arbitrary delivery.** Two
replicas, each running only its own projection, each merging *any* list whose
content is the run's results: same document. Not "some schedule works" — every
schedule, and the lists need not even be permutations of one another. -/
theorem editChoreo_converges (κ : Cfg Rep (GSet Nat)) (ds ds' : List (GSet Nat))
    (hds : ∀ d, d ∈ ds ↔ ∃ x, x ∈ roster ∧ d = denote roster editChoreo κ x)
    (hds' : ∀ d, d ∈ ds' ↔ ∃ x, x ∈ roster ∧ d = denote roster editChoreo κ x) :
    joinAll (lrun (project editChoreo false) [] (κ false)) ds
      = joinAll (lrun (project editChoreo true) [] (κ true)) ds' :=
  coordination_free_converges roster editChoreo κ trivial
    (readFree_readsAgree roster editChoreo κ trivial)
    (mem_roster false) (mem_roster true) ds ds' hds hds'

/-- `Delta.same_deltas_same_state` is the `p = q` case of
`coordination_free_converges`: one replica, two delivery lists, same content. The
two-replica statement is strictly more — it crosses *bases*, which the fixed-base
lemma cannot do, and that is why the proof is a direct least-upper-bound argument
rather than an appeal to it. -/
theorem converges_single_replica (rs : List R) (c : Choreo R S) (κ : Cfg R S)
    (hsf : SyncFree c) (h : ReadsAgree rs c κ) {p : R} (hp : p ∈ rs)
    (ds ds' : List S)
    (hds : ∀ d, d ∈ ds ↔ ∃ x, x ∈ rs ∧ d = denote rs c κ x)
    (hds' : ∀ d, d ∈ ds' ↔ ∃ x, x ∈ rs ∧ d = denote rs c κ x) :
    joinAll (lrun (project c p) [] (κ p)) ds
      = joinAll (lrun (project c p) [] (κ p)) ds' :=
  coordination_free_converges rs c κ hsf h hp hp ds ds' hds hds'

/-! ### §8.2 The seam: spends free, re-allocation must coordinate.

One invariant — `Segmented.BudgetInv 10`, per-device spend under quota with the
quota summing to the budget — and **both verdicts**, exactly as
`Segmented.budget_not_iconfluent` / `Segmented.budget_segmented` pair them at the
state level. Here the pair is between two *programs*: `spendChoreo` is fiber-local
for `σ = Prod.fst` (the allocation) and runs free with no barrier at all;
`realloc` moves `σ`, and its desynced run busts the budget. -/

/-- Spend one unit **if there is room** — locally checked, and fiber-local: it
never touches the allocation. -/
def spendIfRoom (i : Bool) : DeltaMutator QuotaState :=
  ofInflationary
    (fun s => if s.2 i < s.1 i then (s.1, fun j => if j = i then s.2 j + 1 else s.2 j)
              else s)
    (fun s => by
      show s ⊑ (if s.2 i < s.1 i
                then ((s.1, fun j => if j = i then s.2 j + 1 else s.2 j) : QuotaState)
                else s)
      by_cases h : s.2 i < s.1 i
      · rw [if_pos h]
        have h1 : s.1 ⊔ s.1 = s.1 := merge_idem s.1
        have h2 : s.2 ⊔ (fun j => if j = i then s.2 j + 1 else s.2 j)
            = (fun j => if j = i then s.2 j + 1 else s.2 j) := by
          funext j
          show Nat.max (s.2 j) (if j = i then s.2 j + 1 else s.2 j)
              = (if j = i then s.2 j + 1 else s.2 j)
          by_cases hj : j = i
          · rw [if_pos hj, nat_max_def]; split <;> omega
          · rw [if_neg hj, nat_max_def]; split <;> omega
        show (s.1 ⊔ s.1, s.2 ⊔ (fun j => if j = i then s.2 j + 1 else s.2 j))
            = (s.1, fun j => if j = i then s.2 j + 1 else s.2 j)
        rw [h1, h2]
      · rw [if_neg h]; exact merge_idem s)

theorem spendIfRoom_fiberLocal (i : Bool) :
    FiberLocal (S := QuotaState) Prod.fst (spendIfRoom i) := by
  intro s
  show (if s.2 i < s.1 i then ((s.1, fun j => if j = i then s.2 j + 1 else s.2 j) : QuotaState)
        else s).1 = s.1
  by_cases h : s.2 i < s.1 i
  · rw [if_pos h]
  · rw [if_neg h]

theorem spendIfRoom_safe (B : Nat) (i : Bool) :
    ∀ s, BudgetInv B s → BudgetInv B ((spendIfRoom i).op s) := by
  intro s hs
  show BudgetInv B (if s.2 i < s.1 i then
      ((s.1, fun j => if j = i then s.2 j + 1 else s.2 j) : QuotaState) else s)
  by_cases h : s.2 i < s.1 i
  · rw [if_pos h]
    obtain ⟨⟨ht, hf⟩, hsum⟩ := hs
    cases i with
    | false =>
      refine ⟨⟨?_, ?_⟩, hsum⟩
      · show (if (true : Bool) = false then s.2 true + 1 else s.2 true) ≤ s.1 true
        simp; omega
      · show (if (false : Bool) = false then s.2 false + 1 else s.2 false) ≤ s.1 false
        simp; omega
    | true =>
      refine ⟨⟨?_, ?_⟩, hsum⟩
      · show (if (true : Bool) = true then s.2 true + 1 else s.2 true) ≤ s.1 true
        simp; omega
      · show (if (false : Bool) = true then s.2 false + 1 else s.2 false) ≤ s.1 false
        simp; omega
  · rw [if_neg h]; exact hs

/-- **Spends need no coordination at all** — a barrier-free choreography. -/
def spendChoreo : Choreo Rep QuotaState :=
  .write false (spendIfRoom false) (.write true (spendIfRoom true) .done)

theorem spendChoreo_fiberFree :
    FiberFree (S := QuotaState) Prod.fst spendChoreo :=
  ⟨spendIfRoom_fiberLocal false, spendIfRoom_fiberLocal true, trivial⟩

theorem spendChoreo_writesSafe : WritesSafe (BudgetInv 10) spendChoreo :=
  ⟨spendIfRoom_safe 10 false, spendIfRoom_safe 10 true, trivial⟩

/-- **The seam verdict, on a program.** The carried `Spec.budgetSegVerdict` refutes
global freedom with the 10+0 / 0+10 repro; `spendChoreo` nevertheless runs
coordination-free, because every one of its writes stays in the fiber of the
allocation. -/
def spendVerdict : Verdict roster (BudgetInv 10) spendChoreo :=
  .seam Spec.budgetSegVerdict spendChoreo_writesSafe spendChoreo_fiberFree

/-- Re-allocate: merge a new allocation in. **Not** fiber-local — this is the write
the seam is a seam *for*. -/
def allocTo (a : Bool → Nat) : DeltaMutator QuotaState :=
  ofInflationary (fun s => (s.1 ⊔ a, s.2))
    (fun s => by
      have h1 : s.1 ⊔ (s.1 ⊔ a) = s.1 ⊔ a := by rw [← merge_assoc, merge_idem]
      have h2 : s.2 ⊔ s.2 = s.2 := merge_idem s.2
      show (s.1 ⊔ (s.1 ⊔ a), s.2 ⊔ s.2) = (s.1 ⊔ a, s.2)
      rw [h1, h2])

/-- The allocation the second replica tries to install. -/
def altAlloc : Bool → Nat := fun b => if b then 0 else 10

/-- ⚠ **Re-allocation is exactly the write that leaves the fiber** — so the seam
verdict says nothing about it, and `spendVerdict` cannot be stretched to cover
it. -/
theorem allocTo_not_fiberLocal :
    ¬ FiberLocal (S := QuotaState) Prod.fst (allocTo altAlloc) := by
  intro h
  have := congrFun (h ((fun b => if b then 10 else 0), fun _ => 0)) false
  revert this
  decide

/-- Both replicas start from the legal allocation 10+0, nothing spent. -/
def quotaStart : Cfg Rep QuotaState := fun _ => ((fun b => if b then 10 else 0), fun _ => 0)

/-- A barrier-free re-allocation choreography: replica `true` installs a different
allocation without seeing anyone. -/
def realloc : Choreo Rep QuotaState :=
  .write true (allocTo altAlloc) .done

/-- ⚠ **The seam's necessity, run.** With no barrier the two replicas hold two
legal allocations whose merge is the pointwise max — 10+10 against a budget of 10.
Same invariant as `spendVerdict`; the only difference is that this write moves
`σ`. That is what "sync nodes are required exactly at σ-changes" means
operationally. -/
theorem realloc_desynced_breaks :
    ¬ BudgetInv 10 (denote roster realloc quotaStart false
                    ⊔ denote roster realloc quotaStart true) := by
  intro h
  have := h.2
  revert this
  decide

/-! ### §8.3 A free choreography, and the refutation, both from the general iff.

Non-vacuity in both directions: `CoordFree` is satisfiable and refutable, and
neither is provable in general. -/

instance : DecidablePred (fun s : GSet Nat => s 0 = true) := fun s => by
  infer_instance

/-- **Satisfiable**: "node 0 is present" is I-confluent
(`Catalog.gset_mem_iconfluent`), so its saturating family meets the spec. -/
theorem gsetMem_coordFree (x y : GSet Nat) :
    CoordFree roster (fun s : GSet Nat => s 0 = true)
      (satFamily (fun s : GSet Nat => s 0 = true) false true x y) :=
  coordFree_of_iconfluent (gset_mem_iconfluent 0) roster _
    (satFamily_writesSafe _ false true x y)

/-- **Refutable, with the witness**: the at-most-one-pin ceiling is not
I-confluent (`Necessity.atMostOneBit_not_iconfluent`), so *some* legal pair's
sync-free choreography breaks the spec — the barrier cannot be deleted. -/
theorem atMostOne_sync_cannot_be_dropped :
    ∃ x y, Necessity.AtMostOneBit x ∧ Necessity.AtMostOneBit y ∧
      ¬ CoordFree roster Necessity.AtMostOneBit
        (satFamily Necessity.AtMostOneBit false true x y) := by
  refine sync_cannot_be_dropped roster (fun _ => false) ?_ ?_ (by decide)
    Necessity.atMostOneBit_not_iconfluent
  · intro s
    funext a
    show (false || s a) = s a
    simp
  · show ((false : Bool) && false) = false
    rfl

end Uwueave.Choreo
