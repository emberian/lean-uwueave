/-
# Leanuweave.Catalog — the standard CRDTs, each with its keystone invariant classified.

Every entry is (a) a concrete `MergeState` instance whose merge laws are *proved*,
not assumed, and (b) at least one invariant classified — `IConfluent` (runs
coordination-free) or refuted with a constructive clashing pair (must escalate).

The refutations matter more than the confirmations. A `¬ IConfluent` result tells
a loom author "this feature cannot be a pure CRDT no matter how clever the
library is" — and each comes with the exact two-replica scenario that breaks it,
which is also the test an implementation must decide a policy for.

Everything here is Lean core only. Sets are `α → Bool` (decidable membership,
merge = pointwise `||`); counters are `ι → Nat` (merge = pointwise `max`).
-/
import Leanuweave.Confluence

namespace Leanuweave.Catalog

open Leanuweave

/-! ## §1. G-Set — the grow-only set. The substrate of everything append-only. -/

/-- A grow-only set with decidable membership. -/
abbrev GSet (α : Type) := α → Bool

instance instMergeStateGSet (α : Type) : MergeState (GSet α) where
  merge x y := fun a => x a || y a
  merge_comm x y := funext fun a => Bool.or_comm (x a) (y a)
  merge_assoc x y z := funext fun a => Bool.or_assoc (x a) (y a) (z a)
  merge_idem x := funext fun a => Bool.or_self (x a)

/-- Membership after merge is membership in either replica — the merge really is
set union, not an accident of the encoding. -/
theorem gset_mem_merge {α : Type} (x y : GSet α) (a : α) :
    (x ⊔ y) a = (x a || y a) := rfl

/-- **"Contains `a`" is I-confluent.** Anything a replica has observed survives
every merge. This is the tier-1 workhorse: node presence, tombstones, bookmarks,
acks — all instances of this one theorem. -/
theorem gset_mem_iconfluent {α : Type} (a : α) :
    IConfluent (S := GSet α) (fun s => s a = true) := by
  intro x y hx _
  show (x a || y a) = true
  simp [hx]

/-- **"Does not contain `a`" is ALSO I-confluent** — union of two sets both
lacking `a` lacks `a`. Together with the previous theorem this is why 2P-set
presence (`added ∧ ¬removed`) is confluent: removal is itself monotone
information. The 2P price is paid elsewhere (no re-add), not at merge. -/
theorem gset_notmem_iconfluent {α : Type} (a : α) :
    IConfluent (S := GSet α) (fun s => s a = false) := by
  intro x y hx hy
  show (x a || y a) = false
  simp [hx, hy]

/-- **Monotone-closed invariants are I-confluent** — the general positive form:
any invariant upward-closed under inclusion survives union. Grow-only lower
bounds, "at least these members", reachability of an existing node. -/
theorem gset_monotone_iconfluent {α : Type} {I : Invariant (GSet α)}
    (hmono : ∀ s t : GSet α, (∀ a, s a = true → t a = true) → I s → I t) :
    IConfluent I := by
  intro x y hx _
  exact hmono x (x ⊔ y)
    (fun a ha => by show (x a || y a) = true; simp [ha]) hx

/-- ⚠ **"At most one element" is NOT I-confluent** — the canonical bounded
invariant, refuted with the canonical pair: `{0}` and `{1}` are each singletons,
their union is not. This is the `card ≤ k` / "at most N bookmarks" / uniqueness
shape: any *ceiling* on a grow-only structure escalates. -/
theorem gset_atMostOne_not_iconfluent :
    ¬ IConfluent (S := GSet Nat)
      (fun s => ∀ m n, s m = true → s n = true → m = n) := by
  intro h
  have h01 := h (fun n => n == 0) (fun n => n == 1)
    (fun m n hm hn => by simp at hm hn; omega)
    (fun m n hm hn => by simp at hm hn; omega)
  exact absurd (h01 0 1 (by decide) (by decide)) (by decide)

/-- ⚠ **Disjunction breaks I-confluence** (the trap flagged in
`Confluence.lean`). "Only Alice holds the lock or only Bob holds the lock":
Alice's replica satisfies the left disjunct, Bob's the right, and the merged
state satisfies neither. Mutual exclusion cannot be replicated
coordination-free, however you phrase it. -/
theorem or_breaks_iconfluence :
    ¬ IConfluent (S := GSet Nat)
      (fun s => (s 0 = true ∧ s 1 = false) ∨ (s 1 = true ∧ s 0 = false)) := by
  intro h
  have hmerge := h (fun n => n == 0) (fun n => n == 1)
    (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
  cases hmerge with
  | inl hbad => exact absurd hbad.2 (by decide)
  | inr hbad => exact absurd hbad.2 (by decide)

/-! ## §2. G-Counter and PN-Counter. -/

/-- `Nat` under `max` — the height/high-water-mark lattice. (`omega` knows
`Nat.max`, so the laws are one word each.) -/
instance instMergeStateNatMax : MergeState Nat where
  merge := Nat.max
  merge_comm := Nat.max_comm
  merge_assoc := Nat.max_assoc
  merge_idem := Nat.max_self

/-- A grow-only counter: per-replica counts, merged by per-key max (the
pointwise lift — no new proof needed for the instance). -/
abbrev GCounter (ι : Type) := ι → Nat

example (ι : Type) : MergeState (GCounter ι) := inferInstance

/-- **A grow-only lower bound is I-confluent**: "replica `i` has counted at
least `k`" survives merge, because merge only raises counts. -/
theorem gcounter_lowerBound_iconfluent {ι : Type} (i : ι) (k : Nat) :
    IConfluent (S := GCounter ι) (fun f => k ≤ f i) := by
  intro x y hx _
  show k ≤ Nat.max (x i) (y i)
  exact Nat.le_trans hx (Nat.le_max_left _ _)

/-- A PN-counter: a pair of grow-only counters (increments, decrements). The
`MergeState` is the product instance — again free. Its *observable* is `net`,
which is where the trouble lives. -/
abbrev PNCounter (ι : Type) := GCounter ι × GCounter ι

/-- The net value over a two-replica world (`ι = Bool`): total increments minus
total decrements, in `Int` so overdraft is representable. -/
def net (c : PNCounter Bool) : Int :=
  ((c.1 true + c.1 false : Nat) : Int) - ((c.2 true + c.2 false : Nat) : Int)

/-- ⚠ **`net ≥ 0` (a non-negative balance) is NOT I-confluent** — Bailis's
motivating example, concretely. Both replicas start from 10 credited; each
spends 10 on its own decrement key; each is individually legal (net 0); the
merge has spent 20 against 10 (net −10).

This kills "we'll just make the balance a CRDT": a bounded shared resource
cannot be replicated coordination-free. The three standard exits each give
something up — **escrow** (§4: pre-partition the budget), **escalation**
(consensus on spends), or **compensation** (admit overdraft, repair after). -/
theorem pncounter_nonneg_not_iconfluent :
    ¬ IConfluent (S := PNCounter Bool) (fun c => 0 ≤ net c) := by
  intro h
  exact absurd
    (h (fun b => if b then 10 else 0, fun b => if b then 10 else 0)
       (fun b => if b then 10 else 0, fun b => if b then 0 else 10)
       (by decide) (by decide))
    (by decide)

/-! ## §3. LWW — the last-writer-wins register.

A register is *not* naturally monotone: "set the title to X" overwrites. LWW
makes it monotone by fiat: pair every write with a timestamp and let merge keep
the lexicographically larger (timestamp, value) pair. The value tiebreak is
load-bearing — without it, two writes at the same timestamp make merge
non-commutative, a real bug class in shipping CRDTs.

The punchline of this section is a *pair* of theorems:

  * `lww_every_invariant_iconfluent` — a single LWW register can never violate
    any invariant at merge, because its join **selects** one of the two states.
    You cannot observe a merge anomaly by watching one register.
  * `lww_cross_field_not_iconfluent` — two LWW registers can: the merged
    document keeps field A from one replica and field B from the other, an
    interleaving **neither replica ever had**. Every relational invariant
    between LWW fields is at risk.

Per-field LWW is safe alone and unsafe relationally. This is the single most
practical fact in this file for a document-shaped application. -/

/-- A timestamped register value. `ts` is a Lamport-style timestamp; `val` is
kept `Nat` for a fully concrete, decidable instance (the construction is
uniform in any linearly ordered value type). -/
structure LWW where
  ts  : Nat
  val : Nat
  deriving DecidableEq, Repr

namespace LWW

theorem ext {a b : LWW} (hts : a.ts = b.ts) (hval : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- The lexicographic strict order: later timestamp, or same timestamp and
larger value. -/
def Lt (a b : LWW) : Prop := a.ts < b.ts ∨ (a.ts = b.ts ∧ a.val < b.val)

instance (a b : LWW) : Decidable (Lt a b) := by unfold Lt; infer_instance

theorem Lt_trans {a b c : LWW} (h1 : Lt a b) (h2 : Lt b c) : Lt a c := by
  unfold Lt at *; omega

/-- Lexicographic max: total, deterministic, and — the point — a genuine
semilattice join. -/
def join (a b : LWW) : LWW := if Lt a b then b else a

/-- The join **selects** one of its arguments. This one observation makes every
single-register invariant question trivial (see `selection_iconfluent`). -/
theorem join_selects (a b : LWW) : join a b = a ∨ join a b = b := by
  unfold join
  by_cases h : Lt a b
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

theorem join_comm (a b : LWW) : join a b = join b a := by
  unfold join
  by_cases h1 : Lt a b
  · by_cases h2 : Lt b a
    · exact absurd h2 (by unfold Lt at h1 ⊢; omega)
    · rw [if_pos h1, if_neg h2]
  · by_cases h2 : Lt b a
    · rw [if_neg h1, if_pos h2]
    · rw [if_neg h1, if_neg h2]
      exact ext (by unfold Lt at h1 h2; omega) (by unfold Lt at h1 h2; omega)

theorem join_idem (a : LWW) : join a a = a := by
  unfold join; split <;> rfl

theorem join_assoc (a b c : LWW) : join (join a b) c = join a (join b c) := by
  unfold join
  by_cases h1 : Lt a b
  · rw [if_pos h1]
    by_cases h2 : Lt b c
    · rw [if_pos h2]
      by_cases h3 : Lt a c
      · rw [if_pos h3]
      · exact absurd (Lt_trans h1 h2) h3
    · rw [if_neg h2, if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : Lt b c
    · rw [if_pos h2]
    · rw [if_neg h2, if_neg h1]
      by_cases h3 : Lt a c
      · exact absurd h3 (by unfold Lt at h1 h2 ⊢; omega)
      · rw [if_neg h3]

instance : MergeState LWW where
  merge := join
  merge_comm := join_comm
  merge_assoc := join_assoc
  merge_idem := join_idem

end LWW

/-- **Selection lattices are invariant-proof.** If a merge always returns one of
its two arguments, *every* invariant is I-confluent — the merged state is a
state some replica already legally held. Linear orders (LWW, max-counters,
version-number races) are all of this shape. -/
theorem selection_iconfluent {S : Type u} [MergeState S]
    (hsel : ∀ x y : S, x ⊔ y = x ∨ x ⊔ y = y) (I : Invariant S) :
    IConfluent I := by
  intro x y hx hy
  cases hsel x y with
  | inl h => rw [h]; exact hx
  | inr h => rw [h]; exact hy

/-- A single LWW register can never violate any invariant at merge. -/
theorem lww_every_invariant_iconfluent (I : Invariant LWW) : IConfluent I :=
  selection_iconfluent LWW.join_selects I

/-- ⚠ **Two LWW registers can.** The invariant `fieldA ≤ fieldB` holds on each
replica; the merge keeps A's `fieldA` (fresher) and B's `fieldB` (fresher), an
interleaving neither replica ever had, and the invariant dies. Refutation
states: replica A wrote both fields to 5 at t=2; replica B wrote `fieldA := 0`
at t=1 (stale, loses) and `fieldB := 0` at t=3 (fresh, wins). Merge: (5, 0).

Note what this does **not** contradict: `product_iconfluent` lifts invariants
that mention one field each. `fieldA ≤ fieldB` mentions both, gets no lift, and
is in fact false-at-merge. The lift's independence hypothesis is real. -/
theorem lww_cross_field_not_iconfluent :
    ¬ IConfluent (S := LWW × LWW) (fun p => p.1.val ≤ p.2.val) := by
  intro h
  exact absurd
    (h (⟨2, 5⟩, ⟨2, 5⟩) (⟨1, 0⟩, ⟨3, 0⟩) (by decide) (by decide))
    (by decide)

/-! ## §4. The bounded counter, done right: ESCROW.

`pncounter_nonneg_not_iconfluent` says a shared bound cannot be free. The escrow
construction (Balegas et al.'s bounded counter) recovers coordination-freedom by
*pre-partitioning* the bound: give each replica a quota and make the invariant
per-replica — "replica `i` has spent at most its quota". Per-replica invariants
are pointwise, so I-confluence is inherited, and the global bound follows by
summing quotas. The nonmonotonic square edit (spend) became monotone by
shrinking what each replica may assert alone. -/

/-- Per-replica spend tracking; spends only grow, merged by max. -/
abbrev Escrow (ι : Type) := ι → Nat

/-- **The escrowed local bound IS I-confluent.** Merge takes per-key max, and
the max of two values ≤ `q i` is ≤ `q i`. Contrast with
`pncounter_nonneg_not_iconfluent`: same resource, same safety goal, opposite
verdict — because the invariant was *rephrased* to be per-replica. That
rephrasing is the entire escrow trick. -/
theorem escrow_local_bound_iconfluent {ι : Type} (q : ι → Nat) :
    IConfluent (S := Escrow ι) (fun f => ∀ i, f i ≤ q i) := by
  intro x y hx hy i
  show Nat.max (x i) (y i) ≤ q i
  exact Nat.max_le.mpr ⟨hx i, hy i⟩

/-- The global bound follows from the local ones — stated over `Bool` (two
replicas) to stay concrete; the n-ary version is the same sum pushed through a
fold. -/
theorem escrow_global_bound (q : Bool → Nat) (f : Escrow Bool)
    (h : ∀ i, f i ≤ q i) : f true + f false ≤ q true + q false :=
  Nat.add_le_add (h true) (h false)

end Leanuweave.Catalog
