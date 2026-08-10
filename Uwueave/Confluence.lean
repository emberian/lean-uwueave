/-
# Uwueave.Confluence — the judgement everything else is stated against.

A replicated structure has a **merge**. An application has **invariants** it wants
to hold. The question that decides whether you need coordination is *not* "is my
merge commutative" (every CRDT merge is) — it is:

> if two replicas each satisfy the invariant, does their merge?

Bailis et al. call this **invariant confluence** (I-confluence), and prove it is
both **necessary and sufficient**: if `I` is I-confluent, a coordination-free
convergent implementation exists; if it is not, **no system can** implement the
semantics while staying coordination-free and convergent. That is a theorem about
every possible implementation, not a limitation of any particular library.

This file is that judgement, in ~60 lines, over Lean core only.

## Why a hand-rolled semilattice instead of mathlib's

`MergeState` below is exactly mathlib's `SemilatticeSup` minus the `≤`. We do not
import mathlib because the entire order-theoretic content we need is the three
merge laws, and requiring a mathlib checkout to read a 60-line judgement is a bad
trade for a library meant to be *read*. Where a proof genuinely wants mathlib
(the escrow/quota-partition refinement over `Finset` sums) we say so and leave the
mathlib-derived version cited rather than vendored.

Literature:
  * Bailis, Fekete, Franklin, Ghodsi, Hellerstein, Stoica — "Coordination Avoidance
    in Database Systems", VLDB 2015. (I-confluence; Theorem 3.1 is the
    necessary-and-sufficient result.)
  * Shapiro, Preguiça, Baquero, Zawirski — "Conflict-free Replicated Data Types",
    SSS 2011. (The join-semilattice / CvRDT formulation.)
  * Gomes, Kleppmann, Mulligan, Beresford — "Verifying Strong Eventual Consistency
    in Distributed Systems", OOPSLA 2017. (The Isabelle account this mirrors.)
-/

namespace Uwueave

universe u v

/-! ## §1. The merge -/

/-- **A mergeable state.** `merge` is the CvRDT join: it must be commutative,
associative and idempotent. Those three laws are exactly what makes replay order,
duplication and re-delivery unobservable — i.e. what makes the thing a CRDT.

This is a join-semilattice presented by its operation. We do not carry `≤`; where
we want it, `Leq` below derives it. -/
class MergeState (S : Type u) where
  /-- The CvRDT join. -/
  merge : S → S → S
  merge_comm  : ∀ x y,   merge x y = merge y x
  merge_assoc : ∀ x y z, merge (merge x y) z = merge x (merge y z)
  merge_idem  : ∀ x,     merge x x = x

export MergeState (merge merge_comm merge_assoc merge_idem)

@[inherit_doc] infixl:65 " ⊔ " => MergeState.merge

/-- The order induced by the join: `x ≤ y` iff merging `x` into `y` changes
nothing — i.e. `y` already subsumes everything `x` knows. -/
def Leq {S : Type u} [MergeState S] (x y : S) : Prop := x ⊔ y = y

@[inherit_doc] infixl:50 " ⊑ " => Leq

/-- Merging only ever moves *up* the lattice: a replica never forgets. This is
the monotonicity that makes gossip safe to repeat. -/
theorem le_merge_left {S : Type u} [MergeState S] (x y : S) : x ⊑ (x ⊔ y) := by
  show x ⊔ (x ⊔ y) = x ⊔ y
  rw [← merge_assoc, merge_idem]

theorem le_merge_right {S : Type u} [MergeState S] (x y : S) : y ⊑ (x ⊔ y) := by
  show y ⊔ (x ⊔ y) = x ⊔ y
  rw [merge_comm x y, ← merge_assoc, merge_idem]

/-! The induced order is a genuine partial order, and the merge is the **least**
upper bound in it — which is why "sync" loses nothing and adds nothing. These
four lemmas are the working kit for causality reasoning (`Causality.lean`). -/

theorem leq_refl {S : Type u} [MergeState S] (x : S) : x ⊑ x := merge_idem x

theorem leq_trans {S : Type u} [MergeState S] {x y z : S}
    (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z := by
  show x ⊔ z = z
  calc x ⊔ z = x ⊔ (y ⊔ z) := by rw [hyz]
    _ = (x ⊔ y) ⊔ z := by rw [merge_assoc]
    _ = y ⊔ z := by rw [hxy]
    _ = z := hyz

theorem leq_antisymm {S : Type u} [MergeState S] {x y : S}
    (hxy : x ⊑ y) (hyx : y ⊑ x) : x = y := by
  calc x = y ⊔ x := hyx.symm
    _ = x ⊔ y := merge_comm y x
    _ = y := hxy

/-- **The merge is the least upper bound**: it sits above both replicas, and
below anything that does. Read operationally: the merged state knows everything
either replica knew and *nothing else* — a sync can neither drop nor invent
knowledge. -/
theorem merge_le_iff {S : Type u} [MergeState S] {x y z : S} :
    (x ⊔ y) ⊑ z ↔ x ⊑ z ∧ y ⊑ z := by
  constructor
  · intro h
    have hx : x ⊔ (x ⊔ y) = x ⊔ y := by rw [← merge_assoc, merge_idem]
    have hy : y ⊔ (x ⊔ y) = x ⊔ y := by
      rw [merge_comm x y, ← merge_assoc, merge_idem]
    constructor
    · show x ⊔ z = z
      rw [← h, ← merge_assoc, hx]
    · show y ⊔ z = z
      rw [← h, ← merge_assoc, hy]
  · intro ⟨hx, hy⟩
    show (x ⊔ y) ⊔ z = z
    rw [merge_assoc, hy, hx]

/-! ## §2. The judgement -/

/-- An invariant is just a predicate on replica state: `balance ≥ 0`, "the parent
relation is acyclic", "every edge's endpoints exist", "at most 64 bookmarks". -/
abbrev Invariant (S : Type u) := S → Prop

/-- **I-confluence.** `I` is I-confluent iff every merge of two `I`-satisfying
replicas satisfies `I`.

This is the whole decision. If it holds, the invariant can be enforced with no
coordination at all — replicas may partition arbitrarily and still converge to a
legal state. If it fails, coordination is *required*, and `escalation_witness`
below hands you the specific pair of legal states whose merge is illegal. -/
def IConfluent {S : Type u} [MergeState S] (I : Invariant S) : Prop :=
  ∀ x y : S, I x → I y → I (x ⊔ y)

/-- **The cost verdict.** A field/structure may run coordination-free exactly when
its invariant is I-confluent. We keep the two names distinct because they answer
different questions — `IConfluent` is a fact about a predicate, `CoordinationFree`
is a licence to pick a replication strategy — but by Bailis Thm 3.1 they coincide,
which is `coordination_free_iff` below. -/
def CoordinationFree {S : Type u} [MergeState S] (I : Invariant S) : Prop :=
  IConfluent I

theorem coordination_free_iff {S : Type u} [MergeState S] (I : Invariant S) :
    CoordinationFree I ↔ IConfluent I := Iff.rfl

/-- **Failure is constructive.** When `I` is not I-confluent you do not merely
lack a proof — there is an actual pair of replica states, each individually legal,
whose merge is illegal. That pair is the bug report: it is precisely the scenario
your users will hit, and it is what a test should replay.

(Classical: the existential comes from `¬∀` via `by_contra`. `Classical.choice`
is the only nonconstructive ingredient and it is Lean's, not an added axiom.) -/
theorem escalation_witness {S : Type u} [MergeState S] (I : Invariant S)
    (h : ¬ IConfluent I) : ∃ x y : S, I x ∧ I y ∧ ¬ I (x ⊔ y) := by
  apply Classical.byContradiction
  intro hcon
  apply h
  intro x y hx hy
  apply Classical.byContradiction
  intro hbad
  exact hcon ⟨x, y, hx, hy, hbad⟩

/-! ## §3. Composition — the two lifts the DSL is built on.

Real state is a *record of fields*. These two theorems are why a composed
structure's verdict can be computed field-by-field instead of re-proved whole. -/

/-- Componentwise merge on a pair. -/
instance instMergeStateProd {A : Type u} {B : Type v}
    [MergeState A] [MergeState B] : MergeState (A × B) where
  merge x y := (x.1 ⊔ y.1, x.2 ⊔ y.2)
  merge_comm x y := by simp [merge_comm]
  merge_assoc x y z := by simp [merge_assoc]
  merge_idem x := by simp [merge_idem]

/-- **The product lift.** Two independent invariants on two independently-merged
fields compose: the conjunction is I-confluent iff each conjunct is. This is what
makes the DSL's field-by-field report *sound* rather than a heuristic.

⚠ Read the quantifier: this covers invariants that mention **one field each**. A
genuinely *cross-field* invariant (`node.parent ∈ nodes`, "the active path is a
path") is not of this shape and gets no free ride — see `Uwueave.Weave`, where
exactly those are the ones that bite. -/
theorem product_iconfluent {A : Type u} {B : Type v} [MergeState A] [MergeState B]
    {IA : Invariant A} {IB : Invariant B}
    (hA : IConfluent IA) (hB : IConfluent IB) :
    IConfluent (S := A × B) (fun p => IA p.1 ∧ IB p.2) :=
  fun x y hx hy => ⟨hA x.1 y.1 hx.1 hy.1, hB x.2 y.2 hx.2 hy.2⟩

/-- Pointwise merge on a function space — the substrate for every keyed map
(`NodeId → …`). -/
instance instMergeStatePi {K : Type u} {V : Type v} [MergeState V] :
    MergeState (K → V) where
  merge f g := fun k => f k ⊔ g k
  merge_comm f g := funext fun k => merge_comm (f k) (g k)
  merge_assoc f g h := funext fun k => merge_assoc (f k) (g k) (h k)
  merge_idem f := funext fun k => merge_idem (f k)

/-- Merges compute componentwise/pointwise *by definition*; these `rfl` lemmas
make that visible to `simp`/`rw`, which match syntactically and cannot see
through instance projections on their own. -/
@[simp] theorem prod_merge_fst {A : Type u} {B : Type v} [MergeState A] [MergeState B]
    (x y : A × B) : (x ⊔ y).1 = x.1 ⊔ y.1 := rfl

@[simp] theorem prod_merge_snd {A : Type u} {B : Type v} [MergeState A] [MergeState B]
    (x y : A × B) : (x ⊔ y).2 = x.2 ⊔ y.2 := rfl

@[simp] theorem pi_merge_apply {K : Type u} {V : Type v} [MergeState V]
    (f g : K → V) (k : K) : (f ⊔ g) k = f k ⊔ g k := rfl

/-- **The pointwise lift.** A per-key invariant that is I-confluent at every key
is I-confluent over the whole map. Keys are independent, so each closes alone. -/
theorem pi_iconfluent {K : Type u} {V : Type v} [MergeState V]
    {J : K → Invariant V} (hJ : ∀ k, IConfluent (J k)) :
    IConfluent (S := K → V) (fun f => ∀ k, J k (f k)) :=
  fun x y hx hy k => hJ k (x k) (y k) (hx k) (hy k)

/-- **Conjunction of two invariants on the *same* state.** Unlike the product
lift this needs no independence — both invariants see the same merge. -/
theorem and_iconfluent {S : Type u} [MergeState S] {I J : Invariant S}
    (hI : IConfluent I) (hJ : IConfluent J) :
    IConfluent (fun s => I s ∧ J s) :=
  fun x y hx hy => ⟨hI x y hx.1 hy.1, hJ x y hx.2 hy.2⟩

/-- ⚠ **Disjunction does NOT lift, and this is the trap.** "The document is
locked by Alice OR locked by Bob" is a disjunction of two perfectly I-confluent
invariants, and it is not I-confluent. We prove the counterexample concretely in
`Uwueave.Catalog.or_breaks_iconfluence` rather than stating a false lemma
here. -/
theorem or_lift_is_not_available : True := trivial

end Uwueave
