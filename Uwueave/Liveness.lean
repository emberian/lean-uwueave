/-
# Uwueave.Liveness — the other half of SEC: fair delivery reaches the LUB.

`Delta.lean` is the **safety** half of strong eventual consistency for delta
shipping: what arrives decides the state (`same_deltas_same_state`); order,
duplication, and batching cannot. Getting the same deltas to arrive everywhere
is the protocol's job — named there and left open.

This file is that job, miniaturized to an honest model:

  * replicas hold states of type `S` under `MergeState`;
  * a **delta-delivery** step joins one issued lattice element into one
    replica (`deliver`); a **state-pull** step joins one replica's whole
    state into another (`pull`) — anti-entropy / gossip;
  * **fairness** is a *finite* covering predicate (`FairOn`): every
    participant's received set is membership-equivalent to the issued set
    (one successful delivery of each delta to each replica is enough for a
    join-semilattice). This is a finite completion certificate, **not** the
    infinite "exchanges infinitely often" assumption: `Uwueave.Temporal`
    separately defines weak and strong fairness over infinite traces and does
    not identify either one with `FairOn`;
  * under fairness, every listed replica reaches `joinAll base issued` —
    the least upper bound already characterized by `le_joinAll` /
    `mem_le_joinAll` / `joinAll_le` — via `same_deltas_same_state` and
    `leq_antisymm`;
  * under an unfair schedule a starved replica can miss a delta another
    holds, so states differ (constructive G-Set witness).

## What this model does NOT capture

  * Real networks (packet loss as a probability, RTT, topology dynamics).
  * Wall clocks, timeouts, or an infinite execution in this module — `FairOn`
    remains a finite covering. `Uwueave.Temporal` supplies `Eventually`,
    action-labelled infinite traces, weak/strong fairness, a genuine
    `WorldFuture` delivery trace, and a `RenderProgress` pending exit. It still
    treats `Nat` as an event index rather than elapsed time and assumes rather
    than derives scheduler fairness.
  * Byzantine replicas, authenticated channels, or causal-delta-interval
    constraints (`Delta.lean`'s header lists those as network-layer
    obligations; they stay out of scope here too).
  * Multi-hop state epidemic diameter bounds for `n > 2` under pull-only
    schedules (the two-replica pull theorem is the clean case; the general
    convergence theorem is stated for delta delivery, where one hop
    ships the payload directly).

Literature:
  * Shapiro, Preguiça, Baquero, Zawirski — "Conflict-free Replicated Data
    Types", SSS 2011. (SEC = eventual delivery + strong convergence.)
  * Almeida, Shoker, Baquero — "Delta State Replicated Data Types",
    J. Parallel Distrib. Comput. 111, 2018. (Anti-entropy of deltas;
    safety is `Delta.lean`, liveness of the shipper is here.)
  * Gomes, Kleppmann, Mulligan, Beresford — "Verifying Strong Eventual
    Consistency in Distributed Systems", OOPSLA 2017. (Network model +
    fair delivery as the liveness hypothesis SEC needs.)
-/
import Uwueave.Delta

namespace Uwueave.Liveness

open Uwueave Uwueave.Catalog Uwueave.Delta

universe u v

variable {S : Type u} [MergeState S]

/-! ## §1. Configurations and steps -/

/-- A system configuration: one merge-state per replica. -/
abbrev Config (ι : Type v) (S : Type u) := ι → S

/-- **Delta delivery**: replica `r` joins delta `δ` into its local state.
The entire receiver of a delta-CRDT, one step at a time. -/
def deliver [DecidableEq ι] (c : Config ι S) (r : ι) (δ : S) : Config ι S :=
  fun r' => if r' = r then c r ⊔ δ else c r'

/-- **State pull** (anti-entropy gossip): replica `dst` joins replica `src`'s
whole state. Safe to repeat by `le_merge_left` / idempotence. -/
def pull [DecidableEq ι] (c : Config ι S) (dst src : ι) : Config ι S :=
  fun r => if r = dst then c dst ⊔ c src else c r

/-- Run a finite schedule of `(replica, delta)` deliveries. -/
def runDeliveries [DecidableEq ι] (c : Config ι S) (sched : List (ι × S)) :
    Config ι S :=
  sched.foldl (fun c e => deliver c e.1 e.2) c

/-- Run a finite schedule of `(dst, src)` state pulls. -/
def runPulls [DecidableEq ι] (c : Config ι S) (sched : List (ι × ι)) :
    Config ι S :=
  sched.foldl (fun c e => pull c e.1 e.2) c

@[simp] theorem runDeliveries_nil [DecidableEq ι] (c : Config ι S) :
    runDeliveries c ([] : List (ι × S)) = c := rfl

theorem runDeliveries_cons [DecidableEq ι] (c : Config ι S)
    (r : ι) (δ : S) (rest : List (ι × S)) :
    runDeliveries c ((r, δ) :: rest) = runDeliveries (deliver c r δ) rest := rfl

@[simp] theorem runPulls_nil [DecidableEq ι] (c : Config ι S) :
    runPulls c ([] : List (ι × ι)) = c := rfl

theorem runPulls_cons [DecidableEq ι] (c : Config ι S)
    (dst src : ι) (rest : List (ι × ι)) :
    runPulls c ((dst, src) :: rest) = runPulls (pull c dst src) rest := rfl

theorem deliver_at [DecidableEq ι] (c : Config ι S) (r : ι) (δ : S) :
    deliver c r δ r = c r ⊔ δ := by
  simp [deliver]

theorem deliver_ne [DecidableEq ι] (c : Config ι S) {r r' : ι} (δ : S)
    (h : r' ≠ r) : deliver c r' δ r = c r := by
  simp only [deliver]
  rw [if_neg (Ne.symm h)]

/-! ## §2. What a replica received -/

/-- The list of deltas the schedule delivered to replica `r`, in delivery
order. The receiver's history is exactly this list. -/
def received [DecidableEq ι] (r : ι) (sched : List (ι × S)) : List S :=
  (sched.filter (fun e => decide (e.1 = r))).map (·.2)

omit [MergeState S] in
theorem received_nil [DecidableEq ι] (r : ι) :
    received (S := S) r [] = [] := rfl

omit [MergeState S] in
theorem received_cons_self [DecidableEq ι] (r : ι) (δ : S) (rest : List (ι × S)) :
    received r ((r, δ) :: rest) = δ :: received r rest := by
  simp [received]

omit [MergeState S] in
theorem received_cons_other [DecidableEq ι] {r r' : ι} (δ : S)
    (rest : List (ι × S)) (h : r' ≠ r) :
    received r ((r', δ) :: rest) = received r rest := by
  simp [received, h]

/-- **Delivery is a fold of ⊔ at the target.** After any schedule, replica
`r` holds exactly `joinAll` of its pre-schedule state and the deltas that
landed there — the `Delta` receiver, scheduled. -/
theorem run_eq_joinAll [DecidableEq ι] (c : Config ι S)
    (sched : List (ι × S)) (r : ι) :
    runDeliveries c sched r = joinAll (c r) (received r sched) := by
  induction sched generalizing c with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨r', δ⟩ := e
    rw [runDeliveries_cons]
    by_cases h : r' = r
    · rw [h, received_cons_self, joinAll_cons, ih (deliver c r δ), deliver_at]
    · rw [received_cons_other (h := h), ih (deliver c r' δ), deliver_ne c δ h]

/-! ## §3. Fairness (finite covering) and convergence -/

/-- **Fair delta delivery on a finite participant set.** Every listed
replica's received *set* matches the issued *set* — membership equivalence,
so order, duplication, and retransmission are free (they are the safety
half). A finite schedule can only cover finitely many replicas; that is
the honest scope of a finite fairness predicate. -/
def FairOn [DecidableEq ι] (replicas : List ι) (issued : List S)
    (sched : List (ι × S)) : Prop :=
  ∀ r ∈ replicas, ∀ δ : S, δ ∈ issued ↔ δ ∈ received r sched

/-- **Convergence under fair delivery.** From a common base, a fair schedule
lands every listed replica at `joinAll base issued` — the LUB of the base
and everything issued (`le_joinAll`, `mem_le_joinAll`, `joinAll_le`). The
equality is `same_deltas_same_state`: fairness supplies set-equivalence of
histories; safety supplies that set-equivalence is enough. -/
theorem fair_converges [DecidableEq ι]
    (base : S) (issued : List S) (sched : List (ι × S)) (replicas : List ι)
    (hfair : FairOn (S := S) replicas issued sched) :
    ∀ r ∈ replicas,
      runDeliveries (fun _ => base) sched r = joinAll base issued := by
  intro r hr
  rw [run_eq_joinAll]
  exact same_deltas_same_state (fun δ => (hfair r hr δ).symm) base

/-- Initial configuration after each replica has joined its own issued
deltas into a shared base (partition mode: mutations done, gossip not
yet). -/
def initConfig [DecidableEq ι] (base : S) (locals : ι → List S) : Config ι S :=
  fun r => joinAll base (locals r)

/-- **Convergence from local issues + fair anti-entropy.** Each replica
starts holding only its own issues; a fair schedule that delivers the
global issued set to every participant equalizes them all at the LUB.
Local copies already present are absorbed by idempotence / set
equivalence — redelivery is free. -/
theorem fair_converges_from_init [DecidableEq ι]
    (base : S) (locals : ι → List S) (allIssued : List S)
    (sched : List (ι × S)) (replicas : List ι)
    (hunion : ∀ δ : S, δ ∈ allIssued ↔ ∃ r ∈ replicas, δ ∈ locals r)
    (hfair : FairOn (S := S) replicas allIssued sched) :
    ∀ r ∈ replicas,
      runDeliveries (initConfig base locals) sched r = joinAll base allIssued := by
  intro r hr
  rw [run_eq_joinAll, initConfig, ← joinAll_append]
  apply same_deltas_same_state
  intro δ
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with hloc | hrecv
    · exact (hunion δ).mpr ⟨r, hr, hloc⟩
    · exact (hfair r hr δ).mpr hrecv
  · intro hmem
    exact List.mem_append.mpr (Or.inr ((hfair r hr δ).mp hmem))

/-- Under fair delivery, any two listed replicas agree (the SEC equality
half, once liveness has supplied the same deltas). -/
theorem fair_replicas_agree [DecidableEq ι]
    (base : S) (issued : List S) (sched : List (ι × S)) (replicas : List ι)
    (hfair : FairOn (S := S) replicas issued sched)
    {r₁ r₂ : ι} (h₁ : r₁ ∈ replicas) (h₂ : r₂ ∈ replicas) :
    runDeliveries (fun _ => base) sched r₁ =
      runDeliveries (fun _ => base) sched r₂ := by
  rw [fair_converges base issued sched replicas hfair r₁ h₁,
      fair_converges base issued sched replicas hfair r₂ h₂]

/-! ## §4. State-pull gossip — the two-replica fair round -/

/-- A single mutual exchange: each of two replicas pulls the other once.
After both pulls, both hold the join — the smallest fair state-sync
schedule that equalizes a pair. -/
def pairExchange : List (Bool × Bool) :=
  [(false, true), (true, false)]

/-- **Two-replica pull convergence.** Starting from `s₀` at `false` and
`s₁` at `true`, one fair pair-exchange lands both at `s₀ ⊔ s₁` (the LUB,
by `merge_le_iff`). -/
theorem pair_exchange_converges (s₀ s₁ : S) :
    let c₀ : Config Bool S := fun b => if b then s₁ else s₀
    let c := runPulls c₀ pairExchange
    c false = s₀ ⊔ s₁ ∧ c true = s₀ ⊔ s₁ := by
  constructor
  · simp [pairExchange, runPulls, pull, List.foldl]
  · simp [pairExchange, runPulls, pull, List.foldl]
    -- s₁ ⊔ (s₀ ⊔ s₁) = s₀ ⊔ s₁
    rw [merge_comm s₀ s₁, ← merge_assoc, merge_idem]

/-- Pull is monotone at the destination: the destination only moves up. -/
theorem pull_extends [DecidableEq ι] (c : Config ι S) (dst src : ι) :
    c dst ⊑ pull c dst src dst := by
  simp only [pull, ↓reduceIte]
  exact le_merge_left (c dst) (c src)

/-! ## §5. Satisfiability — a concrete fair schedule converges -/

section GSetWitness
variable {α : Type} [DecidableEq α]

/-- Empty G-Set. -/
def gempty : GSet α := fun _ => false

/-- Two replicas each need both of two issued singleton deltas; the schedule
delivers both deltas to both replicas (a one-round fair covering). -/
def fairSched (a b : α) : List (Bool × GSet α) :=
  [ (false, addDelta a), (false, addDelta b)
  , (true,  addDelta a), (true,  addDelta b) ]

def fairReplicas : List Bool := [false, true]

def fairIssued (a b : α) : List (GSet α) := [addDelta a, addDelta b]

theorem fairSched_received_false (a b : α) :
    received (S := GSet α) false (fairSched a b) = fairIssued a b := by
  simp [received, fairSched, fairIssued]

theorem fairSched_received_true (a b : α) :
    received (S := GSet α) true (fairSched a b) = fairIssued a b := by
  simp [received, fairSched, fairIssued]

/-- The fair schedule really is fair for `{false, true}`. -/
theorem fairSched_is_fair (a b : α) :
    FairOn (S := GSet α) fairReplicas (fairIssued a b) (fairSched a b) := by
  intro r hr δ
  simp only [fairReplicas, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · rw [fairSched_received_false]
  · rw [fairSched_received_true]

/-- **Satisfiability of fair convergence.** On a G-Set, the concrete fair
schedule equalizes both replicas at the join of everything issued. The
definitions are not vacuously over-strong: deltas actually extend state
(`addDelta_adds`), and both sides land on that extension. -/
theorem fair_delivery_converges_gset (a b : α) :
    runDeliveries (fun _ => gempty) (fairSched a b) false =
      joinAll gempty (fairIssued a b)
    ∧ runDeliveries (fun _ => gempty) (fairSched a b) true =
      joinAll gempty (fairIssued a b)
    ∧ runDeliveries (S := GSet α) (fun _ => gempty) (fairSched a b) false =
        runDeliveries (fun _ => gempty) (fairSched a b) true
    ∧ (runDeliveries (fun _ => gempty) (fairSched a b) false : GSet α) a = true
    ∧ (runDeliveries (fun _ => gempty) (fairSched a b) false : GSet α) b = true := by
  have hfair := fairSched_is_fair a b
  have hf := fair_converges (S := GSet α) (ι := Bool)
    gempty (fairIssued a b) (fairSched a b) fairReplicas hfair
  have hfalse := hf false (by simp [fairReplicas])
  have htrue := hf true (by simp [fairReplicas])
  refine ⟨hfalse, htrue, hfalse.trans htrue.symm, ?_, ?_⟩
  · rw [hfalse]
    simp only [fairIssued, joinAll_cons, joinAll_nil]
    have h0 : ((gempty ⊔ addDelta a) ⊔ addDelta b : GSet α) a = true := by
      rw [gset_mem_merge]
      have : (gempty ⊔ addDelta a : GSet α) a = true := addDelta_adds gempty a
      simp [this]
    exact h0
  · rw [hfalse]
    simp only [fairIssued, joinAll_cons, joinAll_nil]
    exact addDelta_adds (gempty ⊔ addDelta a) b

/-! ## §6. Refutation — unfair schedules starve -/

/-- An unfair schedule: only replica `false` ever receives `addDelta a`.
Replica `true` is starved of `a`. -/
def unfairSched (a : α) : List (Bool × GSet α) :=
  [(false, addDelta a)]

theorem unfairSched_received_false (a : α) :
    received (S := GSet α) false (unfairSched a) = [addDelta a] := by
  simp [received, unfairSched]

theorem unfairSched_received_true (a : α) :
    received (S := GSet α) true (unfairSched a) = [] := by
  simp [received, unfairSched]

/-- Unfairness is refutable: `true` does not receive `addDelta a`. -/
theorem unfairSched_misses (a : α) :
    addDelta a ∉ received (S := GSet α) true (unfairSched a) := by
  simp [unfairSched_received_true]

/-- If replica `r` received nothing and replica `s` received exactly `δ`,
with `δ` not already below `base`, their states differ. -/
theorem missed_delta_lags_empty [DecidableEq ι]
    (base : S) (δ : S) (r s : ι) (sched : List (ι × S))
    (hmiss : received r sched = [])
    (hgot : received s sched = [δ])
    (hstrict : ¬ δ ⊑ base) :
    runDeliveries (fun _ => base) sched r ≠
      runDeliveries (fun _ => base) sched s := by
  rw [run_eq_joinAll, run_eq_joinAll, hmiss, hgot, joinAll_nil, joinAll_cons,
    joinAll_nil]
  intro heq
  apply hstrict
  show δ ⊔ base = base
  rw [merge_comm, ← heq]

/-- **Starvation witness.** Under the unfair schedule, replica `false`
holds `a` and replica `true` does not — states differ. Fairness is
necessary for convergence: without it, SEC's equality half has nothing
to apply to. -/
theorem unfair_starvation (a : α) :
    (runDeliveries (fun _ => gempty) (unfairSched a) false : GSet α) a = true
    ∧ (runDeliveries (fun _ => gempty) (unfairSched a) true : GSet α) a = false
    ∧ runDeliveries (S := GSet α) (fun _ => gempty) (unfairSched a) false ≠
        runDeliveries (fun _ => gempty) (unfairSched a) true := by
  have hf : runDeliveries (fun _ => gempty) (unfairSched a) false =
      joinAll gempty [addDelta a] := by
    rw [run_eq_joinAll, unfairSched_received_false]
  have ht : runDeliveries (fun _ => gempty) (unfairSched a) true = gempty := by
    rw [run_eq_joinAll, unfairSched_received_true, joinAll_nil]
  constructor
  · rw [hf]; simp only [joinAll_cons, joinAll_nil]; exact addDelta_adds gempty a
  constructor
  · rw [ht]; rfl
  · -- abstract lag instance (starved replica first, holder second)
    refine Ne.symm ?_
    apply missed_delta_lags_empty (base := (gempty : GSet α)) (δ := addDelta a)
      (r := true) (s := false) (sched := unfairSched a)
      (hmiss := unfairSched_received_true a)
      (hgot := unfairSched_received_false a)
    intro h
    have ha : (addDelta a ⊔ gempty) a = gempty a := congrFun h a
    have htrue : (addDelta a ⊔ gempty : GSet α) a = true := by
      rw [merge_comm]; exact addDelta_adds gempty a
    simp only [gempty] at ha
    rw [htrue] at ha
    exact Bool.noConfusion ha

end GSetWitness

/-! ## §7. Scope seal

Everything above is a finite schedule over an abstract join-semilattice.
This module has no network, clocks, Byzantine model, or infinite traces. Its
successor `Uwueave.Temporal` supplies the infinite-trace vocabulary without
rewriting this finite contract: `WorldAdapter.pendingDeliveryTrace_adjacent`
is a genuine adjacent delivery run,
`RenderAdapter.fair_bob_delivery_exits_pending` connects fairness to a real
pending exit, and `WorldAdapter.starvedPendingTrace_not_weakFair` proves that a
constant transition-valid run may still starve. No theorem there turns event
indices into wall-clock time or proves a deployed scheduler fair.

The keystone here remains `fair_converges`: finite set-covering delivery + the
already-proved LUB character of `joinAll` ⇒ every replica attains the same
least upper bound of everything issued. The G-Set section shows the hypothesis
is inhabitable and that dropping it is refutable. -/

end Uwueave.Liveness
