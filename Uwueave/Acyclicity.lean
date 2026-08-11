/-
# Uwueave.Acyclicity — the DAG dichotomy.

> "isn't the hard part of making a DAG/tree CRDT just enforcing the requirements
>  of a DAG/tree?"

Yes — and this file states exactly where that hardness lives and where it
vanishes. Three theorems:

  1. `acyclicity_not_iconfluent` — over a graph with **arbitrary edge
     insertion**, acyclicity is not I-confluent: replica A adds `a → b`,
     replica B adds `b → a`, each graph is a DAG, the union is not. What Lean
     shows is `¬ IConfluent` with that witness; per Bailis et al.'s necessity
     theorem (cited, not re-proved here) that means no coordination-free
     convergent implementation maintains it — a claim otherwise is hiding
     either coordination or a repair policy.

  2. `grounded_iconfluent` — the invariant "every edge descends in rank" IS
     I-confluent. It is per-edge-local, so it survives union trivially.

  3. `grounded_acyclic` — grounded implies acyclic: a cycle would descend
     forever.

Together, 2+3 are the round hole that fits the square edit: **acyclicity itself
escalates, but a strictly stronger, edge-local invariant is free and implies
it.** You don't coordinate to keep the graph acyclic; you restrict insertion so
that no insertable edge could ever close a cycle.

## Where a real system gets `rank` — the content-addressing remark

In a hash-linked (content-addressed) DAG — git, IPFS, a blocklace, a weave whose
node ids are hashes of (contents, parent ids) — the rank function is not stored
or coordinated: it is *implied*. A node's id is computed from its parents' ids,
so a parent must exist (be hashable) before its child; "height in the hash DAG"
is a rank, and every edge descends in it by construction. A reference cycle
would require a hash cycle (`h = H(…H(…h…)…)`), i.e. a collision-resistance
break. That last step is a **cryptographic premise, not a theorem here** — we
model rank as an explicit function and say so, rather than pretending Lean
proved anything about SHA-2. (Same discipline as Almeida–Shapiro's blocklace,
which gets Byzantine-repelling structure from exactly this construction.)

The practical reading for a weave: **append-only, parents-fixed-at-creation
node insertion needs no cycle check and no coordination, ever** — DAG-ness is
free at any replication scale. The operations that genuinely leave this island
are the ones that *re-point existing edges*: node moving, reparenting, merge-
with-parent. Those are square edits (see `Uwueave.Move`).
-/
import Uwueave.Catalog

namespace Uwueave.Acyclicity

open Uwueave Uwueave.Catalog

/-- A directed graph as a grow-only edge set: `g (a, b) = true` means the edge
`a → b` is present. -/
abbrev EdgeGraph := GSet (Nat × Nat)

/-- Reachability by at least one edge. -/
inductive Reaches (g : EdgeGraph) : Nat → Nat → Prop where
  | edge {a b : Nat}   : g (a, b) = true → Reaches g a b
  | step {a b c : Nat} : Reaches g a b → g (b, c) = true → Reaches g a c

/-- Acyclicity: no vertex reaches itself through ≥ 1 edge. -/
def Acyclic (g : EdgeGraph) : Prop := ∀ v, ¬ Reaches g v v

/-- Every reachability fact in the single-edge graph `{0 → 1}` is that edge. -/
private theorem reaches_single01 {a b : Nat}
    (h : Reaches (fun e => e == ((0 : Nat), (1 : Nat))) a b) : a = 0 ∧ b = 1 := by
  induction h with
  | edge h => simp_all
  | step _ h ih => simp_all

private theorem reaches_single10 {a b : Nat}
    (h : Reaches (fun e => e == ((1 : Nat), (0 : Nat))) a b) : a = 1 ∧ b = 0 := by
  induction h with
  | edge h => simp_all
  | step _ h ih => simp_all

/-- ⚠ **Theorem 1: acyclicity is NOT I-confluent under arbitrary edge
insertion.** `{0 → 1}` and `{1 → 0}` are each acyclic; their union has the
2-cycle. This is the clashing pair every graph-CRDT design must pick a policy
for — coordination (refuse one insert), arbitration (drop an edge
deterministically at merge), or compensation (admit the cycle, repair it). The
2025 PaPoC "Directed Acyclic Graph CRDTs" paper is a compensation design;
Kleppmann's move-op is arbitration-by-timestamp. Neither escapes this theorem —
they choose an exit. -/
theorem acyclicity_not_iconfluent : ¬ IConfluent (S := EdgeGraph) Acyclic := by
  intro h
  have hbad := h (fun e => e == ((0 : Nat), (1 : Nat)))
                 (fun e => e == ((1 : Nat), (0 : Nat)))
    (fun v hv => by have := reaches_single01 hv; omega)
    (fun v hv => by have := reaches_single10 hv; omega)
  exact hbad 0 (Reaches.step (b := 1) (Reaches.edge (by decide)) (by decide))

/-- **Groundedness**: a global rank function under which every present edge
strictly descends. This is the shape content-addressing hands you for free
(rank = height in the hash DAG); in a non-hashed system it is a creation-time
stamp with the same discipline. The invariant is *per-edge-local* — and that
locality is exactly why it will survive merge. -/
def Grounded (rank : Nat → Nat) (g : EdgeGraph) : Prop :=
  ∀ a b : Nat, g (a, b) = true → rank b < rank a

/-- **Theorem 2: groundedness IS I-confluent.** An edge of the union came from
one of the two replicas, and it descended there. No coordination, any number of
replicas, any partition pattern. -/
theorem grounded_iconfluent (rank : Nat → Nat) :
    IConfluent (S := EdgeGraph) (Grounded rank) := by
  intro x y hx hy a b hmem
  cases (Bool.or_eq_true _ _).mp hmem with
  | inl h => exact hx a b h
  | inr h => exact hy a b h

/-- Reachability descends in rank on a grounded graph. -/
private theorem reaches_rank_lt {rank : Nat → Nat} {g : EdgeGraph}
    (hg : Grounded rank g) {a b : Nat} (h : Reaches g a b) : rank b < rank a := by
  induction h with
  | edge h => exact hg _ _ h
  | step _ h ih => exact Nat.lt_trans (hg _ _ h) ih

/-- **Theorem 3: grounded implies acyclic.** A cycle would descend below
itself. -/
theorem grounded_acyclic {rank : Nat → Nat} {g : EdgeGraph}
    (hg : Grounded rank g) : Acyclic g :=
  fun v hv => Nat.lt_irrefl (rank v) (reaches_rank_lt hg hv)

/-- **The dichotomy, packaged.** Enforce the stronger, local, free invariant;
receive the weaker, global, expensive one at every reachable state — including
every merge of every set of replicas, which is what `grounded_iconfluent` adds
over `grounded_acyclic` alone. -/
theorem causal_dag_free (rank : Nat → Nat) :
    IConfluent (S := EdgeGraph) (Grounded rank)
    ∧ ∀ g : EdgeGraph, Grounded rank g → Acyclic g :=
  ⟨grounded_iconfluent rank, fun _ => grounded_acyclic⟩

end Uwueave.Acyclicity
