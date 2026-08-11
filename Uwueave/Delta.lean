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

§6 is the paper's mutator interface itself (`DeltaMutator`: an operation given
as a state transformer *and* as a patch, `s ⊔ delta s = op s`), with the
theorem the design rests on — `mutator_delta_sound`: for a receiver holding
the sender's pre-state, joining the patch and joining the sender's whole
successor state are the same state, one step (`mutator_delta_sound`) or a
whole run (`joinAll_deltas_eq_state`, `run_eq_joinAll`). Four instances past
the G-Set add, three with state-dependent patches; and the general minimality
claim is refuted rather than assumed (`sufficient_delta_not_least`).

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
  * **Which patch an implementation should pick.** §6 models the mutator
    interface and proves patch-shipping and state-shipping interchangeable for
    any receiver holding the pre-state — but *minimality* of a patch is not a
    consequence of the interface, and `sufficient_delta_not_least` shows it
    fails in general. What is true is instance-level and carries a
    news hypothesis (`addDelta_least`); the size of a mutator's patch is an
    engineering choice this file bounds (`delta_le_op`) rather than dictates.

Literature:
  * Almeida, Shoker, Baquero — "Delta State Replicated Data Types",
    J. Parallel Distrib. Comput. 111, 2018. (Earlier as "Efficient State-based
    CRDTs by Delta-Mutation", NETYS 2015; arXiv:1603.01529.)
-/
import Uwueave.ORSet

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

/-! ## §6. The delta-mutator interface — the paper's `mᵟ`, and what it buys.

§1-§4 take a delta to be an arbitrary lattice element and ask what the
receiver can tell apart. The paper's actual programming interface is narrower:
an operation is given **twice** — as the state transformer `op` a state-based
CRDT would ship whole, and as the patch `delta` a delta-CRDT ships instead —
tied by one law, `ships : s ⊔ delta s = op s`. Read the type: `delta : S → S`,
a function of the *pre-state*, not a constant. `orsetRemoveAll` is why — the
patch an element-wide remove must ship is the tombstone set for the tags this
replica has observed, which no constant knows.

What the interface buys, and what it does not:

  * `mutator_delta_sound` — **the prize**: to a receiver that already has the
    sender's pre-state, joining the delta and joining the sender's whole
    successor state are the *same state*. Delta shipping is not an
    approximation of state shipping; it is observationally identical to it.
  * `joinAll_deltas_eq_state`, `run_eq_joinAll` — the same over a whole run of
    mutators, not one step: a receiver folding the delta stream lands exactly
    where merging the sender's final state would put it, and a receiver that
    started from the base reconstructs that final state on the nose. With
    `same_deltas_same_state` (`run_reconstructed`), any order, any
    duplication.
  * `le_op` / `delta_le_op` / `ofInflationary` — the honest structural
    reading: a delta-mutator is exactly a **monotone** operation (every
    inflationary op is one, shipping its result), so the interface itself
    constrains nothing more. All of the engineering is in *which* delta, and
    `delta_le_op` is its whole economics: the patch never exceeds the state it
    replaces.
  * ⚠ `sufficient_delta_not_least` — minimality is **not** part of the deal
    and is false in general: an operation whose news the receiver already has
    is served by the empty delta, which the mutator's own patch does not sit
    below. Least-ness is an instance-level fact with a hypothesis
    ("the delivery was news"), which is exactly the shape of `addDelta_least`.

Instances beyond §5's G-Set add: `gcounterInc` (a state-dependent patch — you
cannot ship "+k", only "your key is now at least n"), `lwwWrite`,
`orsetAddTag`, and `orsetRemoveAll`. -/

/-- **A delta-mutator**: an operation presented as a state transformer and as
a patch, with the law that joining the patch into the pre-state IS the
operation (Almeida–Shoker–Baquero's `mᵟ`). -/
structure DeltaMutator (S : Type u) [MergeState S] where
  /-- The state-based operation: what a CvRDT would apply and ship whole. -/
  op : S → S
  /-- The patch a delta-CRDT ships instead — a function of the pre-state. -/
  delta : S → S
  /-- The interface law. -/
  ships : ∀ s, s ⊔ delta s = op s

/-- A mutator only moves a replica up the lattice: it never forgets. -/
theorem le_op (m : DeltaMutator S) (s : S) : s ⊑ m.op s := by
  rw [← m.ships s]
  exact le_merge_left s (m.delta s)

/-- The patch never exceeds the state it replaces — the reason to ship it. -/
theorem delta_le_op (m : DeltaMutator S) (s : S) : m.delta s ⊑ m.op s := by
  rw [← m.ships s]
  exact le_merge_right s (m.delta s)

/-- Conversely, **every inflationary operation is a delta-mutator**: ship the
result. So the interface is exactly monotonicity — it is not a constraint that
buys the theorems below, it is a *presentation*, and the content is which
delta an implementation picks. -/
def ofInflationary (f : S → S) (h : ∀ s, s ⊑ f s) : DeltaMutator S where
  op := f
  delta := f
  ships := h

/-- **Delta shipping is observationally identical to state shipping.** For a
receiver `r` that already holds the sender's pre-state `s` — the condition a
delta protocol maintains — joining the small patch and joining the sender's
whole successor state give *the same state*, not merely equivalent ones. This
is the theorem the entire delta-CRDT design rests on, and it is three lines of
the three merge laws.

(The hypothesis is load-bearing, and is exactly what the paper's causal
delta-merging condition is for: a receiver *missing* `s` gets strictly less
from the patch than from the state — see the header's §4-§5 note.) -/
theorem mutator_delta_sound (m : DeltaMutator S) (s r : S) (h : s ⊑ r) :
    r ⊔ m.delta s = r ⊔ m.op s := by
  have hrs : r ⊔ s = r := by rw [merge_comm]; exact h
  rw [← m.ships s, ← merge_assoc, hrs]

/-- A patch is **sufficient** from `s` when every up-to-date receiver joining
it lands where the sender's whole state would have put it. -/
def Sufficient (m : DeltaMutator S) (s d : S) : Prop :=
  ∀ r : S, s ⊑ r → r ⊔ d = r ⊔ m.op s

/-- The mutator's own patch is sufficient — `mutator_delta_sound`, quantified. -/
theorem delta_sufficient (m : DeltaMutator S) (s : S) : Sufficient m s (m.delta s) :=
  fun r h => mutator_delta_sound m s r h

/-- Shipping the whole successor state is the degenerate sufficient patch, so
"delta shipping" and "state shipping" are two points of one notion. -/
theorem op_sufficient (m : DeltaMutator S) (s : S) : Sufficient m s (m.op s) :=
  fun _ _ => rfl

/-- A run of mutators from a base state: the sender's own history. -/
def run : List (DeltaMutator S) → S → S
  | [], s => s
  | m :: ms, s => run ms (m.op s)

/-- The patches that run ships, each computed against the state it was applied
to — the delta stream a replica gossips. -/
def deltasOf : List (DeltaMutator S) → S → List S
  | [], _ => []
  | m :: ms, s => m.delta s :: deltasOf ms (m.op s)

/-- A run only moves up the lattice (`le_op`, history-long). -/
theorem le_run : ∀ (ms : List (DeltaMutator S)) (s : S), s ⊑ run ms s
  | [], s => leq_refl s
  | m :: ms, s => leq_trans (le_op m s) (le_run ms (m.op s))

/-- **The delta stream reconstructs the sender's state exactly.** A replica
holding the base and folding the shipped patches — nothing else, no whole
state ever transmitted — ends at the sender's final state, on the nose. -/
theorem run_eq_joinAll : ∀ (ms : List (DeltaMutator S)) (s : S),
    joinAll s (deltasOf ms s) = run ms s
  | [], _ => rfl
  | m :: ms, s => by
    show joinAll (s ⊔ m.delta s) (deltasOf ms (m.op s)) = run ms (m.op s)
    rw [m.ships s]
    exact run_eq_joinAll ms (m.op s)

/-- **And for a receiver that is ahead of the base**: folding the sender's
delta stream lands exactly where merging the sender's whole final state would
— `mutator_delta_sound` iterated over a history. Whole-state anti-entropy and
delta gossip are interchangeable for any receiver that has the pre-state, at
every prefix. -/
theorem joinAll_deltas_eq_state : ∀ (ms : List (DeltaMutator S)) (s r : S),
    s ⊑ r → joinAll r (deltasOf ms s) = r ⊔ run ms s
  | [], s, r, h => by
    show r = r ⊔ s
    rw [merge_comm, h]
  | m :: ms, s, r, h => by
    have hnext : m.op s ⊑ r ⊔ m.delta s := by
      rw [← m.ships s]
      exact merge_le_iff.mpr ⟨leq_trans h (le_merge_left r (m.delta s)),
        le_merge_right r (m.delta s)⟩
    show joinAll (r ⊔ m.delta s) (deltasOf ms (m.op s)) = r ⊔ run ms (m.op s)
    rw [joinAll_deltas_eq_state ms (m.op s) (r ⊔ m.delta s) hnext, merge_assoc]
    have hd : m.delta s ⊔ run ms (m.op s) = run ms (m.op s) :=
      leq_trans (delta_le_op m s) (le_run ms (m.op s))
    rw [hd]

/-- The gossip laws apply to mutator runs unchanged: a receiver that got the
same *set* of patches — any order, any duplication, any batching — holds the
sender's state. §4's punchline, now about an actual program's output. -/
theorem run_reconstructed {ms : List (DeltaMutator S)} {l : List S} (s : S)
    (h : ∀ d, d ∈ l ↔ d ∈ deltasOf ms s) : joinAll s l = run ms s := by
  rw [same_deltas_same_state h s, run_eq_joinAll]

/-! ### Instances — four mutators, three of them state-dependent. -/

/-- G-Set `add`, §5's case study, as a mutator: the one instance whose patch
is a constant, which is why it is the misleading one to generalise from. -/
def gsetAdd {α : Type} [DecidableEq α] (a : α) : DeltaMutator (GSet α) where
  op s := fun b => s b || decide (b = a)
  delta _ := addDelta a
  ships _ := rfl

/-- G-Counter increment. The patch is **not** "+k" — a lattice has no such
element — it is "key `i` is now at least `n`", which the mutator can only
compute from the pre-state. -/
def gcounterInc {ι : Type} [DecidableEq ι] (i : ι) (k : Nat) :
    DeltaMutator (GCounter ι) where
  op s := fun j => if j = i then s j + k else s j
  delta s := fun j => if j = i then s j + k else 0
  ships s := by
    funext j
    show Nat.max (s j) (if j = i then s j + k else 0) = if j = i then s j + k else s j
    by_cases h : j = i
    · rw [if_pos h, if_pos h, nat_max_def]
      split <;> omega
    · rw [if_neg h, if_neg h, nat_max_def]
      split <;> omega

/-- LWW write: the patch is the register itself, stamped past whatever the
replica had — again a function of the pre-state, since the timestamp must beat
the one being overwritten. -/
def lwwWrite (v : Nat) : DeltaMutator LWW where
  op s := ⟨s.ts + 1, v⟩
  delta s := ⟨s.ts + 1, v⟩
  ships s := by
    have hlt : LWW.Lt s ⟨s.ts + 1, v⟩ := Or.inl (Nat.lt_succ_self s.ts)
    show LWW.join s ⟨s.ts + 1, v⟩ = ⟨s.ts + 1, v⟩
    unfold LWW.join
    exact if_pos hlt

/-- OR-Set add-with-tag: a one-pair patch into the adds component, whatever
the replica has accumulated. -/
def orsetAddTag {α τ : Type} [DecidableEq α] [DecidableEq τ] (a : α) (t : τ) :
    DeltaMutator (ORSet.ORSet α τ) where
  op s := ORSet.addTag s a t
  delta _ := (fun p => decide (p = (a, t)), fun _ => false)
  ships s := by
    have h2 : (s.2 ⊔ (fun _ => false)) = s.2 := by
      funext p
      show (s.2 p || false) = s.2 p
      exact Bool.or_false (s.2 p)
    show ((s.1 ⊔ fun p => decide (p = (a, t))), s.2 ⊔ (fun _ => false))
        = ORSet.addTag s a t
    rw [h2]
    rfl

/-- ⚠ **Element-wide remove — the instance the constant-delta reading cannot
express.** "Remove everything I have seen of `a`" ships the tombstones for the
tags *this replica observed*: the patch is a genuine function of the
pre-state, and two replicas running the same operation ship different deltas.
That is the whole reason the interface is `S → S`. -/
def orsetRemoveAll {α τ : Type} [DecidableEq α] (a : α) :
    DeltaMutator (ORSet.ORSet α τ) where
  op s := ORSet.removeAll s a
  delta s := (fun _ => false, fun p => decide (p.1 = a) && s.1 p)
  ships s := by
    have h1 : (s.1 ⊔ (fun _ => false)) = s.1 := by
      funext p
      show (s.1 p || false) = s.1 p
      exact Bool.or_false (s.1 p)
    show (s.1 ⊔ (fun _ => false), s.2 ⊔ fun p => decide (p.1 = a) && s.1 p)
        = ORSet.removeAll s a
    rw [h1]
    rfl

/-- ⚠ **The mutator's patch is not least among the sufficient ones.** Take
`gsetAdd 0` applied to a replica that already holds `0`: the operation is a
no-op there, so the *empty* patch is sufficient — every up-to-date receiver
joining it lands exactly where the sender's whole state would put it — and the
mutator still ships the singleton, which does not sit ⊑-below the empty one.

So "delta minimality" is not a consequence of the interface, and any general
claim of it is false. What is true is instance-level and carries a news
hypothesis: `addDelta_least`, whose `x a = false` ("the delivery was news, not
an echo") is precisely the premise missing here. -/
theorem sufficient_delta_not_least :
    ∃ (m : DeltaMutator (GSet Nat)) (s d : GSet Nat),
      Sufficient m s d ∧ ¬ (m.delta s ⊑ d) := by
  refine ⟨gsetAdd 0, addDelta 0, (fun _ => false), ?_, ?_⟩
  · intro r hr
    -- `r` is above the singleton, so it already holds `0` and the op adds nothing.
    have h0 : r 0 = true := by
      cases hr0 : r 0 with
      | true => rfl
      | false =>
        have h : (addDelta 0 0 || r 0) = r 0 := congrFun hr 0
        rw [hr0] at h
        simp [addDelta] at h
    funext b
    show (r b || false) = (r b || (addDelta 0 b || decide (b = 0)))
    by_cases hb : b = 0
    · subst hb; simp [h0]
    · simp [addDelta, hb]
  · intro h
    exact absurd (congrFun h 0) (by decide)

end Uwueave.Delta
