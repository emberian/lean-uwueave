/-
# Uwueave.Ancestral — does the lowest common ancestor buy invariant safety?

State-based CRDTs merge two states with a binary join `⊔`. **Mergeable Replicated
Data Types** (Kaki, Priya, Sivaramakrishnan, Jagannathan, OOPSLA 2019) merge
**three**: the two replicas *and their lowest common ancestor*, `merge σ_lca σ₁ σ₂`
— the Git model, backed by a versioned store that can supply the LCA. A three-way
merge sees strictly more data than a two-way join: it can compute each side's
*delta* since the fork, and a two-way join cannot.

So the question this file asks, which we could not find asked anywhere:

> **Is invariant-confluence with an LCA strictly weaker than I-confluence?**
> Are there invariants that escalate under `⊔` but run coordination-free under a
> three-way merge?

## The answer, in one line

**Neither judgement implies the other. At a fixed state space the LCA does buy
real invariant safety, and its power has an exact shape: it neutralizes
*resurrection*, never *accumulation*.**

(«At a fixed state space» is load-bearing and §6.1 spends a paragraph on it: a
two-way CRDT can always escape by enlarging Σ with causal metadata, and the
price of that escape is the space the MRDT line exists to avoid. Nothing here
claims an invariant is unimplementable two-way.)

Both halves are proved here, over concrete data types with reachable witnesses:

  * §4 `iconfluent_does_not_imply_ancestral` — a ceiling invariant that **is**
    I-confluent for the max-join and is **not** ancestrally confluent for the
    MRDT counter merge. The direction the brief expected to be free is refuted;
    and the reason is worth more than the refutation (§4.3): the two-way verdict
    was bought by a join that **drops an operation's effect**
    (`join_not_serializing` vs `counter_serializing`). *I-confluence is a property
    of the merge, not of the semantics — a lossy merge is I-confluent for
    invariants the semantics cannot keep.*
  * §5 `lock_ancestral_confluent` — **the prize**: a hand-off lock whose
    `AtMostOne` invariant has a *reachable* two-way clash (so it refutes
    `IConfluent`, refutes the reachability-restricted `JoinConfluentFrom`, and
    by `Necessity.reachable_clash_refutes_cfcs` refutes CFCS outright), yet is
    ancestrally confluent for a three-way merge that is commutative,
    fast-forwarding **and effect-faithful**. With an LCA, mutual exclusion under
    hand-off is free. §8 packages the two halves as
    `two_way_free_three_way_escalates` and `two_way_escalates_three_way_free`.

    ⚠ Read which difference did the work. Ancestral confluence differs from
    I-confluence in *two* ways — the merge sees more, and the quantifier is
    restricted to co-reachable pairs. The prize uses only the first:
    `lock_merge_atMostOne` holds for **every** triple, with no reachability and
    no hypothesis on the ancestor. The win is the merge's information, not a
    weaker quantifier.
  * §6 says why that is not just a lucky choice of lattice. The law doing the
    work is **fast-forward**, `merge l l y = y` — "a replica that did nothing
    does not roll back one that did". Its two-way form is `l ⊑ x` for reachable
    `x`, and `lock_no_update_preserving_join` proves **no join whatsoever** on
    that state space has it, because reachability there contains a cycle and
    `⊑` is antisymmetric. Sharper still, §1's `join_is_ancestral_merge_iff_trivial`:
    a two-way join *is* a three-way merge only on a one-point state space. (And
    `constant_merge_collapses` shows the laws are not free money either: the
    invariant-preserving cheat "just return the ancestor" is excluded.)
  * §7 is the impossibility, and it is the honest verdict on the brief's headline
    candidate. **The bounded counter is not saved by the LCA**, and not for want
    of a clever merge: `serialization_clash_defeats_every_merge` quantifies over
    *every* effect-faithful three-way merge, and `budget_defeats_every_faithful_merge`
    instantiates it at every budget. Escrow (`Catalog` §4, `Segmented`) is still
    required. The LCA is an *information* instrument; a bounded counter's clash
    is not an information failure — both spends really happened, every
    serialization of them is illegal, and no merge may un-spend them.

§8's `clash_dichotomy` is the design rule that falls out: for two concurrent
operations legal at a legal ancestor, either some serialization of them is legal
(**resurrection** — the join broke what the operations kept, and an
ancestor-reading merge has something to choose) or the merge escalates
(**accumulation** — the operations broke it, and §7 says no effect-faithful
merge does better). Only the first is an LCA's business.

## The three-way model, and exactly what is assumed

Sal §2 (`sal-multimodal-crdt-verification-2026.pdf`) gives an MRDT as
`⟨Σ, σ₀, do, merge, rc⟩`. `AncestralMerge` below carries `merge : Σ → Σ → Σ → Σ`
and **two laws only**:

  * `comm : merge l x y = merge l y x` — both replicas compute the same merge
    from the same triple; without it, *which peer merged* is observable.
  * `fastforward : merge l l y = y` — if one side never left the ancestor, adopt
    the other side. This is Git's fast-forward, and it is satisfied by both MRDTs
    in Sal §2: the counter's `l + (a - l) + (b - l)` gives `l + 0 + (y - l) = y`,
    and the OR-set's `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)` gives `(l ∩ y) ∪ (y \ l) = y`.

`fastforward_left` and `self` (`merge l l l = l`) are *derived*, not assumed.

**Not assumed, deliberately:** associativity and idempotence in the `⊔` sense (a
version DAG is not a lattice), and — the load-bearing omission — any form of
monotonicity. `merge l x y` may sit *below* `x ⊔ y`, may sit below `x`. That
freedom is the whole subject of this file.

## No LCA is assumed to exist, and none is assumed unique

A general version DAG need not admit a lowest common ancestor at all: two
distinct *maximal* common bases exclude a lowest one, and a merge-base procedure
has to answer selected / ambiguous / unavailable rather than return a node
(prior art below). So nothing here quantifies over "the" LCA. `AncestralConfluent`
takes a **given** common ancestor `l` and demands the merge be legal for *every*
such `l` — the ancestor is universally quantified, not selected. That makes both
halves of the result robust to ambiguity, in opposite ways:

  * the positive is stronger for it — `lock_merge_atMostOne` holds for **every**
    `l`, including an `l` that is not an ancestor at all, so a merge procedure
    that picks the wrong base, or picks arbitrarily among ambiguous ones, stays
    safe;
  * the negatives do not sneak in via a badly chosen base — in every refuting
    witness each branch is **one operation** from `l`, so `l` is the immediate
    fork point, the node any merge-base procedure would select.

## Honest scope — what of the MRDT literature is modeled, and what is not

  * **Modeled**: Σ, `do` (as `Guarded.eff` with a local admissibility `guard`,
    which is Bailis's "would-violate transactions abort" folded in), `merge`, and
    `rc` — implicitly: `lockPriority` *is* a conflict-resolution policy, a
    symmetric total preference over concurrently granted holders.
  * **Modeled only in its one-op-per-branch form**: RA-linearizability. `Serializing`
    demands that the merge of two single, concurrently admitted operations be
    one of the two serializations. The full condition (arbitrary op sequences,
    an interleaving witness) is not formalized; the one-op form is what both the
    prize and the impossibility need, and it is a *weaker* hypothesis, so §7's
    ∀-quantified impossibility is *stronger* for it.
  * **Not modeled**: `σ₀` and initial-state reachability (an LCA here is any
    `I`-legal state the two branches fork from — the analogue of Bailis's legal
    ancestor); convergence on a *version DAG*. This file models the single
    fork-and-join, which is exactly the shape of the two-way I-confluence
    question and therefore the only shape in which the two can be compared.
    Repeated/criss-cross merging needs Kaki et al.'s further conditions and gets
    no verdict here.
  * **Not modeled**: timestamps and replica ids in `do : Σ × T × R × O → Σ`. Our
    `eff : Op → S → S` folds them into `Op`.
  * Everything in §7 quantifies over merges satisfying `Serializing`; a merge
    that lies about what happened is out of its scope, and `lockMerge` (§5) is
    proved `Serializing` so the prize is not bought with a lie.

## Prior art in the neighbourhood — and what it reserved

`~/dev/minidregg` (sibling Lean repo, same author; no dependency either way —
uwueave stays self-contained) has already built the *hygiene* layer under this
question and deliberately declined the algebra:

  * `Theory/CausalVersionAncestry.lean` — `Ancestry`/`Reaches` with acyclicity
    and `antisymm`, `CommonAncestor`, `LowestCommonBase` with `selected_unique`
    (any two lowest-base certificates select the same node), `MaximalCommonBase`
    with `AmbiguousCommonBases.excludes_lowest` (two distinct maximal bases ⇒ no
    LCA), and `BaseSelection` as the honest output of a conservative merge-base
    procedure. This is the source of the stance above: an LCA is a *decision*,
    not a given.
  * `Kernel/HyperdocumentMerge.lean` — a three-way merge with a per-field
    `base : Option VersionEventId`, a `ValidMerge` condition set, and
    `BaseDecision = selected | ambiguous | unavailable` with
    `unavailableOfAbsent` making absence a proof obligation rather than a free
    flag. Also the honest negative `raw_pair_order_observable`.
  * `docs/decisions/D-0005-hyperdocument-semantic-family.md`, "Patch and merge
    claim ceiling" — reserves the names *isomorphism, pushout, I-confluence,
    binding, refinement* for exact proved definitions, and says minidregg will
    accept either (1) proved residual/commutation/join laws over the canonical
    operation semantics, or (2) a justified contextual-equivalence quotient —
    **neither of which has been done there**.

So this file's question is not merely unasked in the literature; it is
explicitly reserved as open next door. §5's positive is an instance of route (1)
at the scale of one data type: an exact join/merge law over the canonical
operation semantics, with the invariant verdict proved rather than named. It is
one instance, not the general route — the general converse is left open in §8
for exactly the reason D-0005 gives, that the laws must be proved and not
assumed.

Literature:
  * Kaki, Priya, Sivaramakrishnan, Jagannathan — "Mergeable Replicated Data
    Types", OOPSLA 2019. (Σ, σ₀, do, merge; the LCA/versioned-store model.)
  * Sal — "Multi-modal Verification of Replicated Data Types", 2026, §2.
    (The `⟨Σ, σ₀, do, merge, rc⟩` tuple and the counter/OR-set MRDTs quoted above.)
  * Bailis et al. — "Coordination Avoidance in Database Systems", VLDB 2015.
    (I-confluence; `Uwueave.Confluence`, `Uwueave.Necessity`.)
-/
import Uwueave.Necessity

namespace Uwueave.Ancestral

open Uwueave Uwueave.Catalog Uwueave.Necessity

universe u v

/-! ## §1. The three-way merge -/

/-- **A three-way (MRDT) merge.** `merge3 lca x y` reconciles two replicas
against their lowest common ancestor. Two laws, and only two:

  * `comm` — the merge is symmetric in the two replicas, so both sides compute
    the same result from the same triple;
  * `fastforward` — a replica that never left the ancestor does not hold the
    other one back.

Not assumed: associativity, idempotence in the join sense, and any monotonicity.
A three-way merge is free to return a state *below* both inputs, which is
precisely what a two-way join cannot do. -/
structure AncestralMerge (S : Type u) where
  /-- The three-way merge: ancestor first, then the two replicas. -/
  merge3 : S → S → S → S
  /-- Symmetric in the two replicas. -/
  comm : ∀ l x y, merge3 l x y = merge3 l y x
  /-- A replica that did not move is fast-forwarded past. -/
  fastforward : ∀ l y, merge3 l l y = y

/-- Fast-forward on the other side, from `comm`. -/
theorem AncestralMerge.fastforward_left {S : Type u} (M : AncestralMerge S)
    (l x : S) : M.merge3 l x l = x := by
  rw [M.comm, M.fastforward]

/-- Merging an ancestor with itself twice is that ancestor — the three-way
analogue of `merge_idem`, derived rather than assumed. -/
theorem AncestralMerge.self {S : Type u} (M : AncestralMerge S) (l : S) :
    M.merge3 l l l = l := M.fastforward l l

/-- **The two laws have teeth: "keep the ancestor" is not a legal merge.** The
merge that discards both replicas trivially preserves every invariant the
ancestor had, so `AncestralConfluent` would be vacuously easy if it were
admissible. Fast-forward excludes it — except on a one-point state space, where
nothing is being discarded. -/
theorem constant_merge_collapses {S : Type u} (M : AncestralMerge S)
    (hconst : ∀ l x y : S, M.merge3 l x y = l) (x y : S) : x = y := by
  calc x = M.merge3 y y x := (M.fastforward y x).symm
    _ = y := hconst y y x

/-- **A two-way join is a three-way merge only on a one-point state space.**
If some `AncestralMerge` computes `x ⊔ y` and ignores the ancestor, then
fast-forward reads `l ⊔ y = y` for *all* `l, y` — i.e. `l ⊑ y` always — and
antisymmetry collapses the carrier. Conversely a one-point carrier admits the
join as a three-way merge trivially.

This is why the two judgements below can be incomparable without paradox: the
two structures overlap only where nothing is happening. -/
theorem join_is_ancestral_merge_iff_trivial {S : Type u} [MergeState S] :
    (∃ M : AncestralMerge S, ∀ l x y : S, M.merge3 l x y = x ⊔ y) ↔ ∀ x y : S, x = y := by
  constructor
  · intro ⟨M, hM⟩ x y
    have hle : ∀ l z : S, l ⊑ z := by
      intro l z
      show l ⊔ z = z
      rw [← hM l l z]
      exact M.fastforward l z
    exact leq_antisymm (hle x y) (hle y x)
  · intro h
    refine ⟨⟨fun _ x y => x ⊔ y, fun _ x y => merge_comm x y, fun l y => ?_⟩, fun _ _ _ => rfl⟩
    exact h (l ⊔ y) y

/-! ## §2. Reachability, and the two judgements side by side

An LCA is an *ancestor*: the two replicas must be reachable from it by local
runs. That restriction is a second difference from `IConfluent`, independent of
the merge's extra information, so both judgements below are stated with it. The
two-way one, `JoinConfluentFrom`, is `Necessity.MergeSafe` in the shape that
makes the comparison an apples-to-apples one (§2 closes that identification). -/

variable {S : Type u} {Op : Type v}

/-- `x` is reachable from `l`: some sequence of locally-committed operations
takes `l` to `x`. -/
def Reachable (impl : Impl S Op) (l x : S) : Prop := ∃ ops : List Op, RunsTo impl l x ops

/-- Every state is reachable from itself, by the empty run. -/
theorem Reachable.refl (impl : Impl S Op) (l : S) : Reachable impl l l := ⟨[], rfl⟩

/-- **Ancestral confluence.** For every legal ancestor and every pair of legal
replicas reachable from it, the three-way merge is legal. This is the MRDT
analogue of I-confluence: the same "no coordination needed" question, asked of
the merge the Git model actually performs. -/
def AncestralConfluent (M : AncestralMerge S) (impl : Impl S Op)
    (I : Invariant S) : Prop :=
  ∀ l x y : S, I l → I x → I y →
    Reachable impl l x → Reachable impl l y → I (M.merge3 l x y)

/-- **The two-way judgement on the same triples**: for every legal ancestor and
every pair of legal replicas reachable from it, the *join* is legal. Weaker than
`IConfluent` (it only quantifies over co-reachable pairs), so refuting *this* is
the strong way to say an invariant escalates. -/
def JoinConfluentFrom [MergeState S] (impl : Impl S Op) (I : Invariant S) : Prop :=
  ∀ l x y : S, I l → I x → I y →
    Reachable impl l x → Reachable impl l y → I (x ⊔ y)

/-- I-confluence is the ancestor-blind, reachability-blind version: it implies
the restricted judgement for every implementation. -/
theorem iconfluent_implies_joinConfluentFrom [MergeState S] {impl : Impl S Op}
    {I : Invariant S} (h : IConfluent I) : JoinConfluentFrom impl I :=
  fun _ x y _ hx hy _ _ => h x y hx hy

/-- `JoinConfluentFrom` is `Necessity.MergeSafe` written with `Reachable`: merge
safety gives it directly. -/
theorem mergeSafe_implies_joinConfluentFrom [MergeState S] {impl : Impl S Op}
    {I : Invariant S} (h : MergeSafe impl I) : JoinConfluentFrom impl I :=
  fun l x y hl _ _ ⟨px, hpx⟩ ⟨py, hpy⟩ => h l x y px py hl hpx hpy

/-- …and conversely, under local safety (which makes `I x`, `I y` free along
successful runs). So refuting `JoinConfluentFrom` for a locally safe
implementation refutes `MergeSafe`, hence `IsCFCS`. -/
theorem joinConfluentFrom_implies_mergeSafe [MergeState S] {impl : Impl S Op}
    {I : Invariant S} (hloc : LocallySafe impl I) (h : JoinConfluentFrom impl I) :
    MergeSafe impl I :=
  fun base x y opsx opsy hb hx hy =>
    h base x y hb (hx.preserves hloc hb) (hy.preserves hloc hb) ⟨opsx, hx⟩ ⟨opsy, hy⟩

/-! ## §3. Operations with effects and guards

`Necessity.Impl` bundles the effect of an operation with its local admissibility
check inside `tryApply`. §7 needs them apart: an *effect-faithful* merge must
land on a state the operations would have produced **whether or not** a guard
would have let them run in that order — otherwise "faithful" is vacuous, since a
budget's second spend aborts in every serialization and no faithful merge would
exist at all. `Guarded` splits them and rebuilds `Impl`. -/

/-- An implementation given as an unconditional **effect** plus a local
**guard**. `Guarded.impl` folds them back into the `Necessity.Impl` shape:
commit `eff op s` when `guard op s`, abort otherwise. -/
structure Guarded (S : Type u) (Op : Type v) where
  /-- The unconditional effect of an operation. -/
  eff : Op → S → S
  /-- The local admissibility check; `false` aborts. -/
  guard : Op → S → Bool

/-- The coordination-free implementation a `Guarded` denotes. -/
def Guarded.impl (g : Guarded S Op) : Impl S Op where
  tryApply op s := if g.guard op s then some (g.eff op s) else none

/-- An admitted operation reaches its effect in one step. -/
theorem Guarded.reachable_step (g : Guarded S Op) {op : Op} {s : S}
    (h : g.guard op s = true) : Reachable g.impl s (g.eff op s) :=
  ⟨[op], by simp [RunsTo, run, Guarded.impl, h]⟩

/-- **Effect-faithfulness** (RA-linearizability, one operation per branch): the
merge of two concurrently admitted operations is one of their two
serializations. The guard hypotheses are load-bearing: an aborted operation
produces no branch delta, so faithfulness must not constrain a triple that no
run can produce. A merge satisfying this invents no outcome and skips no
committed operation: it applies both, and only chooses the order — which is
exactly what an MRDT's `rc` policy is for. (Under that order an earlier effect
may of course be overwritten by a later one; that is sequential semantics, not
loss.) Both guards are checked at the common ancestor; the two right-hand sides
then apply the effects unconditionally, even when the second operation's guard
would reject that sequential state. -/
def Serializing (M : AncestralMerge S) (g : Guarded S Op) : Prop :=
  ∀ (l : S) (a b : Op),
    g.guard a l = true → g.guard b l = true →
    M.merge3 l (g.eff a l) (g.eff b l) = g.eff b (g.eff a l) ∨
    M.merge3 l (g.eff a l) (g.eff b l) = g.eff a (g.eff b l)

/-- The guard-free analogue for a two-way join. §4 refutes it for the max-join
on a counter, which is how "the two-way verdict was bought by losing an effect"
becomes a theorem rather than a remark. Unlike `Serializing`, this comparison
deliberately ranges over every effect, including effects the implementation
would abort. -/
def SerializingJoin [MergeState S] (g : Guarded S Op) : Prop :=
  ∀ (l : S) (a b : Op),
    (g.eff a l ⊔ g.eff b l) = g.eff b (g.eff a l) ∨
    (g.eff a l ⊔ g.eff b l) = g.eff a (g.eff b l)

/-! ## §4. Direction (a) refuted: I-confluent does not imply ancestrally confluent

The counter MRDT of Sal §2, and a ceiling on it. Under the two-way max-join a
ceiling is I-confluent — `max` of two legal counters is legal. Under the
three-way merge `l + (a - l) + (b - l)` it is not: two replicas that each spend
their last unit merge to a state two over. -/

/-- The counter MRDT merge, made total on `Nat`. On the region an LCA actually
sees (`l ≤ a`, `l ≤ b`) this is Sal §2's `l + (a - l) + (b - l)`; the third
summand is just `l` there, and only pins down behaviour off that region so the
two laws hold unconditionally (`counterMerge_on_reachable` proves the
agreement). Everything is truncated subtraction, which keeps the whole section
inside `omega`. -/
def counterMerge (l a b : Nat) : Nat :=
  (a - l) + (b - l) + (l - ((l - a) + (l - b)))

/-- On states above the ancestor — the only triples an LCA produces — the total
merge **is** the paper's `a + b - l`. -/
theorem counterMerge_on_reachable {l a b : Nat} (ha : l ≤ a) (hb : l ≤ b) :
    counterMerge l a b = a + b - l := by
  unfold counterMerge; omega

/-- The counter MRDT as an `AncestralMerge`: symmetric, and fast-forwarding. -/
def counterAM : AncestralMerge Nat where
  merge3 := counterMerge
  comm l x y := by unfold counterMerge; omega
  fastforward l y := by unfold counterMerge; omega

/-- Spending against a budget: each operation adds one unit, and is locally
admitted only while the budget holds. -/
def spendOps (B : Nat) : Guarded Nat Unit where
  eff := fun _ s => s + 1
  guard := fun _ s => decide (s + 1 ≤ B)

/-- **A ceiling is I-confluent for the max-join** — `Nat.max` of two counters
under `B` is under `B`. The two-way theory says: no coordination needed. -/
theorem ceiling_iconfluent (B : Nat) : IConfluent (S := Nat) (fun n => n ≤ B) := by
  intro x y hx hy
  show Nat.max x y ≤ B
  rw [nat_max_def]
  split <;> assumption

/-- ⚠ **The same ceiling is not ancestrally confluent for the counter MRDT.**
Ancestor `B` with budget `B + 1`; each replica spends its one remaining unit, a
locally admitted step, reaching `B + 1`; the three-way merge adds both deltas
and lands on `B + 2`. Direction (a) of the research question is refuted. -/
theorem ceiling_not_ancestral (B : Nat) :
    ¬ AncestralConfluent counterAM (spendOps (B + 1)).impl (fun n => n ≤ B + 1) := by
  intro h
  have hg : (spendOps (B + 1)).guard () B = true := by simp [spendOps]
  have hr : Reachable (spendOps (B + 1)).impl B (B + 1) :=
    (spendOps (B + 1)).reachable_step hg
  have hm := h B (B + 1) (B + 1) (by omega) (by omega) (by omega) hr hr
  have hval : counterAM.merge3 B (B + 1) (B + 1) = B + 2 := by
    show counterMerge B (B + 1) (B + 1) = B + 2
    unfold counterMerge; omega
  rw [hval] at hm
  omega

/-- **Direction (a), packaged as a refutation.** There is an invariant that is
I-confluent and not ancestrally confluent: the LCA's extra information is extra
*liability*, not only extra power. -/
theorem iconfluent_does_not_imply_ancestral :
    ∃ I : Invariant Nat,
      IConfluent I ∧ ¬ AncestralConfluent counterAM (spendOps 1).impl I :=
  ⟨fun n => n ≤ 1, ceiling_iconfluent 1, ceiling_not_ancestral 0⟩

/-! ### §4.3 Why the two-way verdict was free: the join dropped an effect.

`ceiling_iconfluent` is not the invariant being safe. It is `max` refusing to
count the second spend. The next pair makes that a theorem: the three-way merge
is effect-faithful and the two-way join is not, and the escalation in
`ceiling_not_ancestral` is the price of the faithfulness. -/

/-- The counter MRDT merge **is** effect-faithful: two concurrent spends merge
to the state either serialization would have produced. -/
theorem counter_serializing (B : Nat) : Serializing counterAM (spendOps B) := by
  intro l a b _ _
  left
  show counterMerge l (l + 1) (l + 1) = l + 1 + 1
  unfold counterMerge
  omega

/-- ⚠ **The max-join is not guard-free effect-faithful**: the witness is two
spend effects from `0`, which join to `1` while either serialization gives `2`.
One effect is gone. The theorem deliberately ranges over effects even when the
budget guard would reject them; §7's reachable impossibility and
`serialization_clash_defeats_every_merge` carry the admitted-operation claim. -/
theorem join_not_serializing (B : Nat) : ¬ SerializingJoin (spendOps B) := by
  intro h
  have h0 := h 0 () ()
  have e1 : (spendOps B).eff () 0 = 1 := rfl
  have e2 : (spendOps B).eff () 1 = 2 := rfl
  rw [e1, e2] at h0
  have hidem : ((1 : Nat) ⊔ 1) = 1 := merge_idem 1
  cases h0 with
  | inl hbad => exact absurd (hidem.symm.trans hbad) (by decide)
  | inr hbad => exact absurd (hidem.symm.trans hbad) (by decide)

/-! ## §5. The prize: an invariant that escalates two-way and is free three-way

A lock with two candidate holders. Operations grant it to Alice, grant it to Bob,
or release it; the invariant is that at most one of them holds it. Every
operation is a *replacement*, so the state space has a **cycle** — and a cycle is
exactly what a two-way join cannot follow (§6). -/

/-- Who holds the lock. -/
structure Lock where
  /-- Alice holds it. -/
  alice : Bool
  /-- Bob holds it. -/
  bob : Bool
  deriving DecidableEq, Repr

/-- The canonical two-way join for a pair of presence flags: componentwise `||`,
the state-based CRDT anyone would write for "who holds it". -/
instance : MergeState Lock where
  merge x y := ⟨x.alice || y.alice, x.bob || y.bob⟩
  merge_comm x y := by cases x; cases y; simp [Bool.or_comm]
  merge_assoc x y z := by cases x; cases y; cases z; simp [Bool.or_assoc]
  merge_idem x := by cases x; simp

/-- **Mutual exclusion**: Alice and Bob do not both hold the lock. -/
def AtMostOne : Invariant Lock := fun s => ¬ (s.alice = true ∧ s.bob = true)

/-- Mutual exclusion is decidable, so every concrete verdict below is a
computation rather than an argument. -/
instance (s : Lock) : Decidable (AtMostOne s) := by unfold AtMostOne; infer_instance

/-- Granting the lock to one holder, or releasing it. Each is a replacement of
the whole holder state — which is what makes the reachability graph cyclic. -/
inductive LockOp where
  /-- Hand the lock to Alice. -/
  | grantAlice
  /-- Hand the lock to Bob. -/
  | grantBob
  /-- Release the lock. -/
  | release
  deriving DecidableEq, Repr

/-- The effect of a lock operation: it overwrites the holder state. -/
def lockEff : LockOp → Lock → Lock
  | .grantAlice, _ => ⟨true, false⟩
  | .grantBob, _ => ⟨false, true⟩
  | .release, _ => ⟨false, false⟩

/-- Lock operations are always locally admissible: every effect is a legal
state, so no local check ever needs to abort. -/
def lockOps : Guarded Lock LockOp where
  eff := lockEff
  guard := fun _ _ => true

/-- The coordination-free implementation of the lock. -/
def lockImpl : Impl Lock LockOp := lockOps.impl

/-- Every committed lock operation lands on a legal state. -/
theorem lock_locally_safe : LocallySafe lockImpl AtMostOne := by
  intro op s s' h _
  have : s' = lockEff op s := by
    simpa [lockImpl, lockOps, Guarded.impl] using h.symm
  subst this
  cases op
  · show AtMostOne ⟨true, false⟩; decide
  · show AtMostOne ⟨false, true⟩; decide
  · show AtMostOne ⟨false, false⟩; decide

/-! ### §5.1 The two-way verdict: escalate, and it is reachable.

Alice holds the lock; her replica hands it to Bob; the other replica does
nothing at all. The union merge resurrects Alice's dead grant and both hold it. -/

/-- The reachable clash: from Alice holding the lock, one replica grants it to
Bob and the other runs nothing; the union merge has both holders. Legal
ancestor, legal replicas, illegal join — Bailis's partition argument applies
verbatim. -/
def lockClash : ReachableClash lockImpl AtMostOne where
  base := ⟨true, false⟩
  x := ⟨false, true⟩
  y := ⟨true, false⟩
  opsx := [LockOp.grantBob]
  opsy := []
  hbase := by decide
  hx_run := rfl
  hy_run := rfl
  hx := by decide
  hy := by decide
  hbad := by decide

/-- ⚠ **Mutual exclusion under hand-off is not I-confluent.** -/
theorem lock_not_iconfluent : ¬ IConfluent AtMostOne :=
  reachable_clash_not_iconfluent lockClash

/-- ⚠ **…nor even confluent on co-reachable triples**, which is the strong form:
the clash is not a lattice artifact reachable by no run. -/
theorem lock_not_joinConfluentFrom : ¬ JoinConfluentFrom lockImpl AtMostOne := by
  intro h
  exact lockClash.hbad
    (h ⟨true, false⟩ ⟨false, true⟩ ⟨true, false⟩ (by decide) (by decide) (by decide)
      ⟨[LockOp.grantBob], rfl⟩ ⟨[], rfl⟩)

/-- ⚠ **…so no coordination-free convergent safe two-way implementation of these
operations exists** (`Necessity.reachable_clash_refutes_cfcs`, i.e. Bailis's
necessity direction). The two-way theory's verdict is: coordinate. -/
theorem lock_two_way_needs_coordination : ¬ IsCFCS lockImpl AtMostOne :=
  reachable_clash_refutes_cfcs lockClash

/-- **Every local check passes and the merge is still where it dies.** The
escalation is not an artifact of a sloppy local guard: each committed operation
lands on a legal state, and merge safety fails anyway. -/
theorem lock_local_checks_pass_merge_fails :
    LocallySafe lockImpl AtMostOne ∧ ¬ MergeSafe lockImpl AtMostOne :=
  ⟨lock_locally_safe, fun h => lock_not_joinConfluentFrom (mergeSafe_implies_joinConfluentFrom h)⟩

/-! ### §5.2 The three-way verdict: free.

`lockMerge` reads the ancestor. If a side did not move, adopt the other side —
that single branch is what the two-way join cannot express, and it is what makes
the hand-off safe. If both moved, a fixed symmetric preference (Alice over Bob
over nobody) resolves it: this is an `rc` policy in Sal's sense, and it is
effect-faithful — the winner's state *is* one of the two serializations. -/

/-- The conflict-resolution policy for two concurrently-moved replicas: Alice
outranks Bob outranks nobody. Symmetric in its arguments, so the merge stays
commutative. -/
def lockPriority (x y : Lock) : Lock :=
  if x.alice || y.alice then ⟨true, false⟩
  else if x.bob || y.bob then ⟨false, true⟩
  else ⟨false, false⟩

/-- The policy is symmetric. -/
theorem lockPriority_comm (x y : Lock) : lockPriority x y = lockPriority y x := by
  unfold lockPriority
  rw [Bool.or_comm x.alice y.alice, Bool.or_comm x.bob y.bob]

/-- The policy's result is always a legal state — it names at most one holder by
construction. -/
theorem lockPriority_atMostOne (x y : Lock) : AtMostOne (lockPriority x y) := by
  unfold lockPriority
  split
  · decide
  · split
    · decide
    · decide

/-- **The three-way lock merge.** Fast-forward past a replica that did not move;
otherwise apply the priority policy. -/
def lockMerge (l x y : Lock) : Lock :=
  if x = l then y else if y = l then x else lockPriority x y

/-- The merge returns one of: the second replica, the first replica, or the
policy's verdict. Everything about it follows from this case split. -/
theorem lockMerge_cases (l x y : Lock) :
    lockMerge l x y = y ∨ lockMerge l x y = x ∨ lockMerge l x y = lockPriority x y := by
  unfold lockMerge
  by_cases hx : x = l
  · exact Or.inl (if_pos hx)
  · by_cases hy : y = l
    · exact Or.inr (Or.inl (by rw [if_neg hx, if_pos hy]))
    · exact Or.inr (Or.inr (by rw [if_neg hx, if_neg hy]))

/-- The lock merge is symmetric in the two replicas. -/
theorem lockMerge_comm (l x y : Lock) : lockMerge l x y = lockMerge l y x := by
  unfold lockMerge
  by_cases hx : x = l
  · by_cases hy : y = l
    · rw [if_pos hx, if_pos hy, hx, hy]
    · rw [if_pos hx, if_neg hy, if_pos hx]
  · by_cases hy : y = l
    · rw [if_neg hx, if_pos hy, if_pos hy]
    · rw [if_neg hx, if_neg hy, if_neg hy, if_neg hx, lockPriority_comm]

/-- The lock MRDT: commutative and fast-forwarding. -/
def lockAM : AncestralMerge Lock where
  merge3 := lockMerge
  comm := lockMerge_comm
  fastforward l y := by unfold lockMerge; rw [if_pos rfl]

/-- **The lock merge preserves mutual exclusion — with no hypothesis on the
ancestor and no reachability at all.** Each of the three branches lands on a
legal state: an unmoved side yields the other side, and the policy's verdict is
legal by construction.

The `∀ l` is what makes this survive ancestor ambiguity: a merge-base procedure
that finds two maximal common bases and picks either, or that has no common base
and supplies a wrong one, still cannot break mutual exclusion. Safety here does
not rest on the base being *the* LCA. -/
theorem lock_merge_atMostOne (l x y : Lock) (hx : AtMostOne x) (hy : AtMostOne y) :
    AtMostOne (lockMerge l x y) := by
  rcases lockMerge_cases l x y with h | h | h
  · rw [h]; exact hy
  · rw [h]; exact hx
  · rw [h]; exact lockPriority_atMostOne x y

/-- **THE PRIZE. Mutual exclusion under hand-off is ancestrally confluent.**
The invariant that `lock_two_way_needs_coordination` says no two-way system can
keep coordination-free runs free under a three-way merge. -/
theorem lock_ancestral_confluent : AncestralConfluent lockAM lockImpl AtMostOne :=
  fun l x y _ hx hy _ _ => lock_merge_atMostOne l x y hx hy

/-- **The prize in one line.** The exact triple that busts the two-way join —
ancestor "Alice holds", one replica handed off to Bob, the other did nothing —
merges to "Bob holds, alone". -/
theorem lock_clash_triple_merges_legally :
    lockAM.merge3 ⟨true, false⟩ ⟨false, true⟩ ⟨true, false⟩ = ⟨false, true⟩ := by decide

/-- …while the join of that same pair has both of them holding it. Set the two
side by side: this is the whole separation, computed. -/
theorem lock_clash_triple_joins_illegally :
    ((⟨false, true⟩ : Lock) ⊔ ⟨true, false⟩) = ⟨true, true⟩ := by decide

/-- The prize is not bought by a merge that lies: `lockMerge` is
effect-faithful. Whenever both replicas moved, the policy's winner is the state
one of the two serializations produces; whenever one did not, the other's state
is trivially that serialization. -/
theorem lock_serializing : Serializing lockAM lockOps := by
  intro l a b _ _
  have hconst : ∀ (o : LockOp) (s t : Lock), lockEff o s = lockEff o t := by
    intro o s t; cases o <;> rfl
  show lockMerge l (lockEff a l) (lockEff b l) = lockEff b (lockEff a l) ∨
       lockMerge l (lockEff a l) (lockEff b l) = lockEff a (lockEff b l)
  rcases lockMerge_cases l (lockEff a l) (lockEff b l) with h | h | h
  · exact Or.inl (by rw [h, hconst b (lockEff a l) l])
  · exact Or.inr (by rw [h, hconst a (lockEff b l) l])
  · rw [h, hconst b (lockEff a l) l, hconst a (lockEff b l) l]
    cases a <;> cases b <;> simp only [lockEff] <;> decide

/-! ## §6. Why this is the LCA and not a luckier lattice

The obvious objection: maybe the lock just needs a better join. It does not, and
the reason is exact. The law doing the work in §5 is `fastforward`. Its two-way
form is `UpdatePreserving`: syncing with a peer that has not moved must not roll
the mover back, i.e. `l ⊑ x` whenever `x` is reachable from `l`. Reachability
for a *replacement* operation is cyclic — Alice can grant to Bob and Bob back to
Alice — and `⊑` is antisymmetric, so no join on this state space can have it. -/

/-- **Update preservation**, the two-way form of fast-forward: a replica that
has not moved sits below one that has, so syncing with it changes nothing. -/
def UpdatePreserving [MergeState S] (impl : Impl S Op) : Prop :=
  ∀ l x : S, Reachable impl l x → l ⊑ x

/-- **A cycle in reachability collapses any update-preserving join.** If each of
two states reaches the other, update preservation puts each below the other and
antisymmetry identifies them. This is the general obstruction: state-based
joins can only follow reachability when reachability is a partial order. -/
theorem cyclic_reachability_collapses_join [MergeState S] {impl : Impl S Op}
    {x y : S} (h : UpdatePreserving impl) (hxy : Reachable impl x y)
    (hyx : Reachable impl y x) : x = y :=
  leq_antisymm (h x y hxy) (h y x hyx)

/-- ⚠ **No two-way join on `Lock` preserves updates — not one.** Alice grants to
Bob and Bob grants back to Alice, a two-cycle, so any update-preserving join
would identify the two states. The quantifier is over *every* `MergeState Lock`
instance, so this is not a statement about the componentwise-`||` choice: it is
the reason state-based CRDTs need tombstones and version metadata to express
replacement at all. -/
theorem lock_no_update_preserving_join (M : MergeState Lock) :
    ¬ @UpdatePreserving Lock LockOp M lockImpl := by
  intro h
  have hcol := @cyclic_reachability_collapses_join Lock LockOp M lockImpl
    ⟨true, false⟩ ⟨false, true⟩ h ⟨[LockOp.grantBob], rfl⟩ ⟨[LockOp.grantAlice], rfl⟩
  exact absurd hcol (by decide)

/-- …while the three-way merge has the very same property, unconditionally.
Set beside `lock_no_update_preserving_join`, this is the exact statement of what
the LCA buys: fast-forward is satisfiable with an ancestor and refutable
without one. -/
theorem lock_three_way_fastforward (l y : Lock) : lockAM.merge3 l l y = y :=
  lockAM.fastforward l y

/-! ### §6.1 ⚠ The separation is at *fixed* Σ. Say so, because the escape is real.

`lock_no_update_preserving_join` quantifies over every join on `Lock` — and
`Lock` is two bits. A two-way CRDT is not actually stuck: it escapes by
**enlarging the state**, attaching causal metadata (tags, tombstones, a version
vector) so that a hand-off is monotone information rather than a cycle. That is
what an OR-register is, and it is why `Uwueave.ORSet` and `Uwueave.MVRegister`
carry the machinery they carry. Under that larger Σ the invariant may well be
I-confluent again.

So the honest form of the separation is: **at a fixed state space, the LCA is
strictly stronger; the two-way escape exists and its price is metadata.** That
price is exactly the one the MRDT line is motivated by — Sal §2 notes a counter
MRDT is `O(1)` where a state-based counter CRDT needs `Ω(n)` in the number of
replicas. This file proves the fixed-Σ half, which is the half that was open;
it does **not** claim mutual exclusion is unimplementable two-way, and no
theorem here says so. -/

/-! ## §7. The impossibility: the LCA cannot save the bounded counter

The brief's headline candidate was the bounded counter — with the LCA you can
see both deltas and detect the double-spend. You can. Detection is not
prevention: a merge must return a state, and both spends really happened. The
theorem below quantifies over *every* effect-faithful three-way merge, so no
cleverer MRDT is waiting to be found. -/

/-- **A serialization clash defeats every effect-faithful three-way merge.** If
two operations are each individually legal at a legal ancestor, both are locally
admitted, and *both* of their serializations are illegal, then no merge that
returns a serialization can be ancestrally confluent. The LCA's information is
irrelevant to this failure: the illegality is in the operations, not in the
merge's ignorance.

Note where the clash sits: each branch is a *single* operation from `l`, so `l`
is the immediate fork point. The refutation is not evaded by a better merge-base
procedure — this is the base any procedure selects. -/
theorem serialization_clash_defeats_every_merge (M : AncestralMerge S)
    (g : Guarded S Op) (I : Invariant S) (l : S) (a b : Op)
    (hser : Serializing M g)
    (hl : I l) (hga : g.guard a l = true) (hgb : g.guard b l = true)
    (ha : I (g.eff a l)) (hb : I (g.eff b l))
    (hab : ¬ I (g.eff b (g.eff a l))) (hba : ¬ I (g.eff a (g.eff b l))) :
    ¬ AncestralConfluent M g.impl I := by
  intro hAC
  have hm := hAC l (g.eff a l) (g.eff b l) hl ha hb
    (g.reachable_step hga) (g.reachable_step hgb)
  cases hser l a b hga hgb with
  | inl h => exact hab (h ▸ hm)
  | inr h => exact hba (h ▸ hm)

/-- ⚠ **The bounded counter is not saved by the LCA — at any budget, against
every effect-faithful merge.** From an ancestor one unit below the budget, both
replicas legally spend that unit; every serialization spends two. Escrow
(`Catalog.escrow_local_bound_iconfluent`) or segmentation
(`Segmented.budget_segmented`) is still required, and the Git model buys nothing
here.

Non-vacuous: `counter_serializing` exhibits a merge satisfying the hypothesis. -/
theorem budget_defeats_every_faithful_merge (B : Nat) (M : AncestralMerge Nat)
    (hser : Serializing M (spendOps (B + 1))) :
    ¬ AncestralConfluent M (spendOps (B + 1)).impl (fun n => n ≤ B + 1) :=
  serialization_clash_defeats_every_merge M (spendOps (B + 1)) (fun n => n ≤ B + 1)
    B () () hser (by omega) (by simp [spendOps]) (by simp [spendOps])
    (by simp [spendOps]) (by simp [spendOps])
    (by simp [spendOps]) (by simp [spendOps])

/-- **The impossibility is not vacuous.** `counterAM` satisfies the hypothesis
of `budget_defeats_every_faithful_merge`, so the class of merges that theorem
quantifies over is inhabited, and the bounded counter's escalation is a fact
about a merge that exists rather than about an empty premise. -/
theorem budget_defeats_counter_merge (B : Nat) :
    ¬ AncestralConfluent counterAM (spendOps (B + 1)).impl (fun n => n ≤ B + 1) :=
  budget_defeats_every_faithful_merge B counterAM (counter_serializing (B + 1))

/-! ## §8. The verdict

The two judgements are **incomparable**, each half witnessed by a concrete data
type with reachable runs. -/

/-- **Half one**: an invariant that runs free two-way and escalates three-way —
because the two-way join preserved it by dropping an operation
(`join_not_serializing`). -/
theorem two_way_free_three_way_escalates :
    IConfluent (S := Nat) (fun n => n ≤ 1) ∧
      ¬ AncestralConfluent counterAM (spendOps 1).impl (fun n => n ≤ 1) :=
  ⟨ceiling_iconfluent 1, ceiling_not_ancestral 0⟩

/-- **Half two — the prize**: an invariant that escalates two-way *on reachable
triples* and runs free three-way. Mutual exclusion under hand-off costs
coordination in every two-way system (`lock_two_way_needs_coordination`) and
costs nothing in the Git model. -/
theorem two_way_escalates_three_way_free :
    ¬ JoinConfluentFrom lockImpl AtMostOne ∧
      AncestralConfluent lockAM lockImpl AtMostOne :=
  ⟨lock_not_joinConfluentFrom, lock_ancestral_confluent⟩

/-- **The dichotomy.** Take any effect-faithful merge, any legal ancestor, and
two locally-admitted operations that are each legal there. Then either some
serialization of the two is legal — **resurrection**, and there is something for
an ancestor-reading merge to choose — or the merge is not ancestrally confluent —
**accumulation**, and by `serialization_clash_defeats_every_merge` no other
effect-faithful merge does better either.

Read as a design rule: when an invariant escalates two-way, ask whether *the
operations themselves* can be run one after the other legally. If they can, the
join broke something the operations kept and the LCA is the fix (§5: hand-off,
replacement, mutual exclusion). If they cannot, the invariant is an accumulation
bound and no merge is coming to save it (§7: budgets, ceilings, `card ≤ k`) —
escrow or coordinate.

What is **not** proved here is the general converse: that every resurrection
clash admits a repairing merge. It does not follow, and this file does not claim
it. A merge sees states, not operations, and a state need not determine the
operation that produced it, so the legal serialization may not be a function of
the triple at all. §5 realizes the resurrection branch for one concrete data
type; closing it in general needs a delta-recovery hypothesis (states determine
their deltas) and is left open.

(Classical: the case split is on an arbitrary `Prop`, so `Classical.choice`
enters here exactly as it does in `Confluence.escalation_witness`. Every other
result in this file is choice-free.) -/
theorem clash_dichotomy (M : AncestralMerge S) (g : Guarded S Op) (I : Invariant S)
    (l : S) (a b : Op) (hser : Serializing M g)
    (hl : I l) (hga : g.guard a l = true) (hgb : g.guard b l = true)
    (ha : I (g.eff a l)) (hb : I (g.eff b l)) :
    (I (g.eff b (g.eff a l)) ∨ I (g.eff a (g.eff b l)))
      ∨ ¬ AncestralConfluent M g.impl I := by
  by_cases h1 : I (g.eff b (g.eff a l))
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : I (g.eff a (g.eff b l))
    · exact Or.inl (Or.inr h2)
    · exact Or.inr (serialization_clash_defeats_every_merge M g I l a b hser hl
        hga hgb ha hb h1 h2)

end Uwueave.Ancestral
