/-
# Uwueave.Delta — delta shipping: the join cannot tell how the news arrived.

Everything so far syncs by shipping **whole states**. A delta-state CRDT
(Almeida–Shoker–Baquero) ships **deltas** instead: a mutation also returns a
small lattice element — just what changed — and replicas gossip streams of
these, joining each arrival into the local state. No new algebra appears: a
delta IS a state by type, usually a tiny one, and the entire receiver is one
fold of ⊔ (`joinAll` below).

That design is sound only if the fold cannot distinguish delivery histories.
This file proves exactly those indistinguishabilities, from the three merge
laws alone:

  * order       — `joinAll_perm` (commutativity, pushed through a history);
  * duplication — `joinAll_dup`, `joinAll_redeliver` (idempotence:
                  at-least-once delivery is as good as exactly-once);
  * batching    — `joinAll_group`, `joinAll_batch`, `joinAll_packets`
                  (associativity: pre-merging packets at the sender changes
                  nothing), and `joinAll_append_merge` (the batch-of-everything
                  — full-state shipping — agrees too);
  * the composite `same_deltas_same_state`: replicas of common base that
    received the same *set* of deltas — any order, any duplication, any
    multiplicity — hold equal states.

§5 grounds the "why" on the G-Set: the delta of `add a` is the one-element
indicator — it delivers `a` (`addDelta_adds`), touches no other element
(`addDelta_frame`), and sits ⊑-below every delta that could have delivered
`a` to a replica lacking it (`addDelta_least`). The minimal patch and the
full state meet the same join.

## What is NOT formalized — the paper's network layer

  * **The causal-delta-merging condition and delta-interval anti-entropy**
    (the paper's §4–5). When partial deltas are forwarded arbitrarily, a
    replica can pass through intermediate states that show an effect without
    its cause; convergence survives (that part is here), per-step causal
    consistency does not. The paper's remedy constrains *which* delta-intervals
    a replica may join — a delivery-protocol obligation with no lattice-level
    content, and none of it is modeled in this file.
  * **Anti-entropy algorithms and eventual delivery.** Every theorem below is
    conditional on what arrived; making "the same delta-set arrives
    everywhere" true is the protocol's job. No liveness is proved here.
  * **Delta-mutators in general.** A delta here is an arbitrary lattice
    element. The paper's mutator interface — and delta minimality for anything
    beyond the G-Set `add` — is not modeled.

Literature:
  * Almeida, Shoker, Baquero — "Delta State Replicated Data Types",
    J. Parallel Distrib. Comput. 111, 2018. (Earlier as "Efficient State-based
    CRDTs by Delta-Mutation", NETYS 2015; arXiv:1603.01529.)
-/
import Uwueave.Catalog

namespace Uwueave.Delta

open Uwueave Uwueave.Catalog

universe u

variable {S : Type u} [MergeState S]

/-! ## §1. The receiver: one fold of ⊔. -/

/-- A replica's state after a delivery history: the base state with every
delta joined in, in arrival order. This fold is the *entire* runtime of a
delta-CRDT receiver; the rest of the file lists the histories it provably
cannot tell apart. -/
def joinAll (base : S) (deltas : List S) : S :=
  deltas.foldl (· ⊔ ·) base

/-- The fold's two computation rules, `rfl`-true but stated so `simp`/`rw`
can see them (foldl hides them behind a recursor otherwise). -/
@[simp] theorem joinAll_nil (base : S) : joinAll base [] = base := rfl

@[simp] theorem joinAll_cons (base d : S) (l : List S) :
    joinAll base (d :: l) = joinAll (base ⊔ d) l := rfl

/-- Delivering one history, then another, is delivering the concatenation —
so a sync that pauses and resumes is already an instance of every law below,
not a new case. -/
theorem joinAll_append (base : S) (l₁ l₂ : List S) :
    joinAll base (l₁ ++ l₂) = joinAll (joinAll base l₁) l₂ := by
  induction l₁ generalizing base with
  | nil => rfl
  | cons d _ ih => exact ih (base ⊔ d)

/-- A join sitting in the base slides out of the fold. This is the bridge
between "merged before shipping" and "merged after arrival" that every
batching law in §3 crosses. -/
theorem merge_joinAll (x y : S) (l : List S) :
    joinAll (x ⊔ y) l = x ⊔ joinAll y l := by
  induction l generalizing y with
  | nil => rfl
  | cons d l ih =>
    show joinAll ((x ⊔ y) ⊔ d) l = x ⊔ joinAll (y ⊔ d) l
    rw [merge_assoc]
    exact ih (y ⊔ d)

/-! ## §2. Where the fold lands in the order: `joinAll base l` is the least
upper bound of `base` and the deltas in `l`. Three lemmas — nothing dropped,
nothing invented — and together they are the whole proof kit for §4. -/

/-- Receiving deltas only moves a replica *up*: the base is never forgotten.
(`le_merge_left`, history-long.) -/
theorem le_joinAll (base : S) (l : List S) : base ⊑ joinAll base l := by
  induction l generalizing base with
  | nil => exact leq_refl base
  | cons d _ ih => exact leq_trans (le_merge_left base d) (ih (base ⊔ d))

/-- No delivered delta is forgotten either: each one sits below the final
state. (`le_merge_right`, history-long.) -/
theorem mem_le_joinAll {d : S} {l : List S} (h : d ∈ l) (base : S) :
    d ⊑ joinAll base l := by
  induction h generalizing base with
  | head l => exact leq_trans (le_merge_right base d) (le_joinAll (base ⊔ d) l)
  | tail e _ ih => exact ih (base ⊔ e)

/-- And nothing else is invented: the fold sits below every state that
dominates the base and each delta. With the previous two lemmas, `joinAll`
is exactly the least upper bound of the base and the deltas — a delta sync
can neither drop nor add knowledge (`merge_le_iff`, history-long). -/
theorem joinAll_le {z : S} : {l : List S} → {base : S} →
    base ⊑ z → (∀ d ∈ l, d ⊑ z) → joinAll base l ⊑ z
  | [], _, hbase, _ => hbase
  | d :: l, base, hbase, hdeltas =>
    joinAll_le (l := l) (base := base ⊔ d)
      (merge_le_iff.mpr ⟨hbase, hdeltas d (List.Mem.head l)⟩)
      (fun e he => hdeltas e (List.Mem.tail d he))

/-! ## §3. The shipping laws. -/

/-- **(a) Order-invariance.** Two histories that are permutations of one
another produce the same state: the network may reorder freely. Proved by
induction on the permutation derivation — `nil`/`cons` ride the fold, `swap`
is commutativity (with associativity steering it into place), `trans`
composes. -/
theorem joinAll_perm {l l' : List S} (h : l.Perm l') (base : S) :
    joinAll base l = joinAll base l' := by
  induction h generalizing base with
  | nil => rfl
  | cons d _ ih => exact ih (base ⊔ d)
  | swap d e l =>
    show joinAll ((base ⊔ e) ⊔ d) l = joinAll ((base ⊔ d) ⊔ e) l
    rw [merge_assoc, merge_comm e d, ← merge_assoc]
  | trans _ _ ih₁ ih₂ => exact (ih₁ base).trans (ih₂ base)

/-- **(b) Duplication-invariance**, adjacent form: joining a delta twice is
joining it once. Idempotence riding the fold — the reason a delta protocol
never needs receiver-side deduplication for *correctness* (it may still want
it for traffic). -/
theorem joinAll_dup (base d : S) (l : List S) :
    joinAll base (d :: d :: l) = joinAll base (d :: l) := by
  show joinAll ((base ⊔ d) ⊔ d) l = joinAll (base ⊔ d) l
  rw [merge_assoc, merge_idem]

/-- **(b′) Re-delivery anywhere:** a delta the rest of the history already
contains adds nothing, however far away the other copy sits — and with
`joinAll_perm` this kills a duplicate at *any* position, not just the front.
At-least-once delivery is exactly as good as exactly-once. -/
theorem joinAll_redeliver {d : S} {l : List S} (h : d ∈ l) (base : S) :
    joinAll base (d :: l) = joinAll base l := by
  induction h generalizing base with
  | head l => exact joinAll_dup base d l
  | tail e _ ih =>
    simp only [joinAll_cons]
    rw [merge_assoc, merge_comm d e, ← merge_assoc]
    exact ih (base ⊔ e)

/-- **(c) Grouping-invariance**, two-delta form: merging two deltas into one
packet before shipping changes nothing. Associativity riding the fold. -/
theorem joinAll_group (base d₁ d₂ : S) (l : List S) :
    joinAll base ((d₁ ⊔ d₂) :: l) = joinAll base (d₁ :: d₂ :: l) := by
  show joinAll (base ⊔ (d₁ ⊔ d₂)) l = joinAll ((base ⊔ d₁) ⊔ d₂) l
  rw [merge_assoc]

/-- **(c′) Whole-packet form:** a nonempty packet `d :: l₁`, pre-merged into
a single delta at the sender, lands exactly where its loose deltas would
have. -/
theorem joinAll_batch (base d : S) (l₁ l₂ : List S) :
    joinAll base (joinAll d l₁ :: l₂) = joinAll base ((d :: l₁) ++ l₂) := by
  rw [joinAll_append, joinAll_cons, joinAll_cons, merge_joinAll base d l₁]

/-- **(c″) Any packeting at all:** a batched history — each packet a nonempty
group `(d, l)` the sender pre-merged — equals the flat history of its pieces.
`joinAll_group` is the two-delta reading of this closure. -/
theorem joinAll_packets (base : S) (gs : List (S × List S)) :
    joinAll base (gs.map fun g => joinAll g.1 g.2)
      = joinAll base (gs.flatMap fun g => g.1 :: g.2) := by
  induction gs generalizing base with
  | nil => rfl
  | cons g _ ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [joinAll_batch, joinAll_append, joinAll_append]
    exact ih (joinAll base (g.1 :: g.2))

/-- Full-state shipping is the degenerate batch, and it agrees: two replicas
that grew from a common base by folding their own delta streams, then sync by
merging whole *states*, land exactly where one replica folding both streams
lands. Delta shipping and state shipping meet at the same join. -/
theorem joinAll_append_merge (base : S) (l₁ l₂ : List S) :
    joinAll base (l₁ ++ l₂) = joinAll base l₁ ⊔ joinAll base l₂ := by
  rw [joinAll_append, ← merge_joinAll (joinAll base l₁) base l₂]
  have habs : joinAll base l₁ ⊔ base = joinAll base l₁ := by
    rw [merge_comm]
    exact le_joinAll base l₁
  rw [habs]

/-! ## §4. The punchline. -/

/-- **Same deltas, same state.** Replicas that share a base and have received
the same *set* of deltas — the hypothesis is mere membership-equivalence of
the two histories, so order, duplication, and multiplicity are all free —
hold equal states. `joinAll_perm` and `joinAll_redeliver` are special cases;
a batched history reduces to its flat one first by `joinAll_packets`. This is
the safety half of strong eventual consistency for delta shipping, at the
lattice level: *what* arrived decides the state, *how* it arrived cannot.
Getting the same deltas to arrive everywhere is the liveness half — the
anti-entropy protocol's job, and out of scope here (see the header). -/
theorem same_deltas_same_state {l l' : List S}
    (h : ∀ d, d ∈ l ↔ d ∈ l') (base : S) :
    joinAll base l = joinAll base l' :=
  leq_antisymm
    (joinAll_le (le_joinAll base l') fun d hd => mem_le_joinAll ((h d).mp hd) base)
    (joinAll_le (le_joinAll base l) fun d hd => mem_le_joinAll ((h d).mpr hd) base)

/-! ## §5. Why ship deltas: they can be minimal. A G-Set case study. -/

section GSetDeltas

variable {α : Type} [DecidableEq α]

/-- The delta the G-Set `add a` mutator ships: the one-element indicator. An
entire replica state, by type — and the smallest one that carries the news
(`addDelta_least`). -/
def addDelta (a : α) : GSet α := fun b => decide (b = a)

/-- Joining the singleton delta delivers its element... -/
theorem addDelta_adds (x : GSet α) (a : α) : (x ⊔ addDelta a) a = true := by
  rw [gset_mem_merge]
  simp [addDelta]

/-- ...and touches nothing else: at every other element the receiving state
is unchanged. With `addDelta_adds`: `x ⊔ addDelta a` differs from `x` exactly
at `a` — the delta is a point patch, however large `x` has grown. -/
theorem addDelta_frame (x : GSet α) {a b : α} (h : b ≠ a) :
    (x ⊔ addDelta a) b = x b := by
  rw [gset_mem_merge]
  simp [addDelta, h]

/-- **The singleton is the least effective delta.** Any delta `δ` that gets
`a` into a replica that genuinely lacked it (`x a = false` — the delivery was
news, not an echo) must itself contain `a`, i.e. it sits ⊑-above
`addDelta a`. Minimal patch and full state are two points on one ⊑-chain,
and every delta that can do this job lies between them. (For a replica
already holding `a` the hypothesis fails, and rightly: there the empty delta
"delivers" too, and nothing nontrivial is least.) -/
theorem addDelta_least {x δ : GSet α} {a : α}
    (hgets : (x ⊔ δ) a = true) (hnew : x a = false) :
    addDelta a ⊑ δ := by
  have hδ : δ a = true := by
    have h' : (x a || δ a) = true := hgets
    rw [hnew, Bool.false_or] at h'
    exact h'
  show (addDelta a ⊔ δ) = δ
  funext b
  rw [gset_mem_merge]
  by_cases hb : b = a
  · subst hb
    simp [addDelta, hδ]
  · simp [addDelta, hb]

end GSetDeltas

end Uwueave.Delta
