/-
# Uwueave.Fugue — a Fugue-style order, its insertion model, and non-interleaving

JOB 8 (GROKJOB.md). `Uwueave/Sequence.lean` proves the interleaving anomaly
(Kleppmann–Gomes–Mulligan–Beresford, PaPoC 2019) *against* the RGA order, and
`Uwueave/SeqKernel.lean` ships that order as the kernel's decision core with
no-interleaving as an explicit non-claim. This file builds the design that
targets exactly that anomaly — Fugue (Weidner–Kleppmann, "The Art of the
Fugue") — at this repo's miniature scale: the order decision (§1), the
insertion model that generates the states it decides on (§8–§9), the general
non-interleaving theorem over generated concurrent histories (§9), and the RGA
contrast in the same model on the same editing intent (§10).

## The order, as defined

Elements are dense indices `0 ≤ i < n`, exactly as in `SeqKernel`: the index
order IS the id/arbitration order and the traversal never sees anything else.
Each element carries two words:

  * `origin[i] : Int` — the tree parent (`-1` = the root sentinel), read
    through `SeqKernel.anchorAt` (out-of-range degrades to `-1`);
  * `side[i] : Bool` — whether `i` hangs as a **right** child (`true`) or a
    **left** child (`false`) of its origin.

`fugueOrder` is the classic in-order tree walk, fuel-totalized in the
`SeqKernel.emitK` discipline: for each node, first the subtrees of its left
children, then the node itself, then the subtrees of its right children;
same-side siblings are visited in **ascending index order**. That sibling
order is pure arbitration no user chose — `Sequence.run_order_by_id`'s caveat
applies verbatim; nothing below depends on its direction.

The point of the tree discipline (and the whole reason Fugue exists): a
replica's consecutive insertion run becomes a **chain of descendants** (each
element a child of the previous one), never a family of siblings. A rival
replica's concurrent run hangs off its own element elsewhere in the tree, so
a same-side sibling contest decides only where whole *runs* land relative to
each other — the runs' interiors cannot interleave. Under RGA-style anchoring
the same two runs are four siblings of one anchor and strictly alternate.

## The insertion model (§8–§9)

An `InsOp` is one keystroke: the new element's `id`, the `origin` it hangs
from, and the `side`. A replica's state is the set of ops it has applied
(`OpSet`); `apply` adds one, `merge` is the grow-only union, and a replica
reads its document by materializing its id space into the two word arrays
above and running `fugueOrder` (`docOrder`). The substrate is a CRDT and says
so: `merge_assoc`, `docOrder_merge_self` (idempotent), `docOrder_merge_comm`
(commutative wherever two op sets agree on shared ids — which disjoint id
spaces give). `rgaDoc` reads the *same* operations RGA-style, so §10's
contrast compares two readings of one editing history.

`runOps o b₀ b ids` is **the chain rule**, Fugue's insert path at this scale:
the first keystroke lands at the insertion point `(o, b₀)` the replica chose
in the document it could see, and every later one hangs off *the character it
just typed*, on the typing side `b` (`false` = each new character before the
last — the back-to-front typing that is RGA's worst case; `true` = forwards).
A run is therefore a chain of descendants, never a family of siblings, and
that is exactly why two runs cannot interleave.

`Concurrent` is what concurrency means here, stated as facts about operations
rather than about the tree: distinct minted ids, an ancestor that predates
both runs, and the load-bearing one — **neither session's operations can name
an element it never received**. Drop that last clause and the two sessions are
sequential, one having seen the other, and nothing below should hold.

## What is proved

  * `fugueOrder_mem` — completeness: under `SeqKernel.WFK` (same hypothesis,
    imported, not restated) every in-range element appears in the order.
  * `rga_head_runs_interleave` / `fugue_head_runs_stay_contiguous` — **the
    contrast pair**, decide-computed through the actual decision cores. The
    same editing intent (two replicas, each typing a two-element run at the
    head of an empty document — the paper's §3 worst case for RGA): under
    `SeqKernel.linearizeK` the merged document strictly alternates the two
    runs; under `fugueOrder` each run survives as a contiguous block reading
    exactly as it did on its author's screen. `rga_head_run_local` /
    `fugue_head_run_local` pin that the two designs agree on each replica's
    *local* document — the divergence is purely in the merge.
  * `fugue_forward_runs_stay_contiguous` / `rga_forward_runs_arbitrated` —
    the forward-typing variant (runs as right-child chains): Fugue keeps runs
    contiguous here too; RGA also happens to (this is `run_order_by_id`'s
    witness in kernel encoding) — which is exactly why the *head-insert*
    scenario above, not this one, is the anomaly and the contrast.
  * `run_contiguous` (and `run_contiguous_of_wfk`) — **the general theorem
    at this scale**: any `Clan` — a maximal single-child descent chain, i.e.
    a run with nothing else inserted into it — appears in `fugueOrder` as a
    contiguous infix (`l <:+: fugueOrder origin side`), in exactly its
    document order, in ANY state (any number of other elements anywhere else
    in the tree), under groundedness alone. The concrete witnesses above are
    also derived from this theorem (`head_runs_contiguous_by_the_theorem`),
    so the general statement is exercised, not just stated.
  * `fugueOrder_nodup` — **duplicate-freedom for the in-order walk**, under
    groundedness alone. `SeqKernel` §7's sibling-subtree disjointness is an
    origin-edge argument (`not_belowK_sibling`, `belowK_sibling_disjoint`),
    imported; only the counting is redone for the `left ++ c :: right` shape.
    This used to be a non-claim of this file.
  * `not_splits_of_infix` / `runs_ordered_of_infix` — contiguity *is* the
    absence of interleaving: in a duplicate-free document, a contiguous run
    admits no foreign element between two of its own (`Splits`), and two
    disjoint contiguous runs land one wholly before the other — Kleppmann et
    al.'s clause 1(d) in its literal disjunctive form.
  * `fugue_runs_never_interleave` — **the general theorem, over generated
    histories**: for ANY two runs produced by the chain rule from a common
    ancestor (any lengths, any insertion points, either typing direction, any
    number of other elements) the merged document keeps each run contiguous
    and in its author's order, `clustered`, with nothing of the other run
    between two of its elements; `fugue_runs_in_one_order` states clause 1(d)
    for the same history. `fugue_runs_never_interleave_creation_ordered`
    discharges the well-formedness from the model when ids are minted in
    creation order.
  * `rga_head_runs_interleave_general` — **the contrast, generalized to
    match**: the same intent under RGA's insert path (anchor to the
    *predecessor character*, so a back-to-front run is a fan of siblings)
    `Splits` X's run with a Y character whenever the two replicas' ids
    straddle — which is what interleaved clocks give. `rga_flat_doc` is the
    reason: a flat forest reads in pure id order and nothing else.
  * The §2 witnesses are now **derived** rather than parallel:
    `headMerged_materializes` shows §2's hand-written arrays are exactly what
    the chain rule emits, `head_runs_contiguous_by_the_operational_theorem`
    re-obtains §2's contiguity from the general theorem, `headFan_rgaDoc`
    re-obtains §2's `[3, 2, 1, 0]` from the fan encoding, and
    `headFan_run_is_split` shows the `¬ Splits` conclusion denies something
    that really happens. `long_runs_never_interleave` fires the general
    theorem past the sampled pair: three keystrokes each, over a non-empty
    common ancestor, with `long_rga_interleaves` as its RGA half.

## Non-claims — the honest boundary

  * **Weidner–Kleppmann's *maximality* is not proved, and it is a different
    quantifier.** What is proved here is that *this* order does not interleave
    two runs generated by the chain rule. Maximal non-interleaving is a claim
    about the space of designs — that no list CRDT does strictly better — and
    nothing in this file quantifies over orders or over designs. Strengthening
    the hypotheses of a theorem about one order never turns it into a theorem
    about all of them.
  * **The placement function is given, not computed.** `runOps` takes the
    insertion point `(o, b₀)` as the replica's choice. Real Fugue *computes*
    it, from the pair of elements the cursor sits between (leftOrigin,
    rightOrigin) at insert time; that arithmetic is what makes a real editor's
    run come out as a chain. Everything downstream of the choice is modeled
    and proved; the choice itself is an input. So: the chain rule does not
    interleave — not that Fugue's cursor arithmetic always yields the chain
    rule.
  * **Two sessions, by name.** The statement names X and Y. The lemma that
    does the work (`clan_of_runOps`) takes arbitrary `pre`/`post` op sets, and
    a third *concurrent* session satisfies exactly what the `base` hypotheses
    ask (it anchors to none of X's or Y's elements either), so k sessions
    follow pairwise by putting the others in `base` — but the k-session
    statement is not written.
  * **Sequential re-editing is out of scope, and must be.** A replica that has
    *seen* the other's run may anchor into it, and then the runs SHOULD split.
    `Concurrent.concurrentX`/`concurrentY` exclude exactly that case, and
    `run_contiguous`'s `Clan` hypothesis is its state-level shadow: a run
    somebody typed into is not claimed contiguous, here or in the paper. What
    is ruled out is interleaving caused by *arbitration between runs*, which
    is the anomaly. `typed_into_run_splits` exhibits the violating history and
    proves the conclusion fails on it — so the hypothesis is load-bearing, not
    decoration.
  * **No deletion, and no causal-order model.** The op model has insertions
    only — `docOrder` has no tombstone array, unlike `linearizeK` — and
    concurrency enters as `Concurrent`'s origin hypotheses rather than as a
    delivery/visibility relation of the kind `Sequence.lean` and
    `Causality.lean` speak. Those hypotheses are what a generated history
    satisfies by construction; deriving them from a happens-before relation is
    undone work, not a theorem of this file.
  * **The ancestor-precedes family and the tombstone output filter are not
    re-proved for the in-order walk** (`SeqKernel` §8). Duplicate-freedom used
    to share this bullet and no longer does.
  * **This is a pure order-theory module beside the kernel, not in it.** The
    export surface still has exactly one symbol (`uwueave_seq_kernel`), which
    still runs `linearizeK`. Adopting this order would mean: one more word
    array (side bits) in SEQ FORMAT, an in-order `emitK` twin, and in-order
    re-proofs of `SeqKernel`'s §8 theorems — an ordinary flag-day rebuild,
    listed here so the distance is measured, not hidden.

Groundedness, chains, completeness and sibling-disjointness machinery are
`SeqKernel`'s own (`ChainK`, `GroundedAnchors`, `WFK`, `chain_to_root`,
`not_belowK_sibling`, `belowK_sibling_disjoint`), imported and reused — the
side array is invisible to origin-edge descent, so not one of those proofs is
duplicated.
-/
import Uwueave.SeqKernel
import Uwueave.ListProofs

namespace Uwueave.Fugue

open Uwueave.SeqKernel (anchorAt linearizeK emitAll emitK childrenK ChainK
  GroundedAnchors BelowK WFK chain_to_root wfk_of_index_ordered mem_childrenK
  not_belowK_sibling belowK_sibling_disjoint)

/-! ## §1. The order decision -/

variable {origin : Array Int} {side : Array Bool}

/-- The side word of element `i`: `true` = right child, `false` = left child.
Out-of-range reads degrade to `true` (such indices are never emitted anyway —
the traversal only ranges over `origin.size`). -/
def sideAt (side : Array Bool) (i : Nat) : Bool :=
  side.getD i true

/-- The children of origin value `p` (`-1` = root) on side `b`, in
**ascending index order** — same-side sibling contests are resolved by id,
pure arbitration (`Sequence.run_order_by_id`'s caveat verbatim). Contrast
`SeqKernel.childrenK`: descending, and side-blind. -/
def childrenF (origin : Array Int) (side : Array Bool) (b : Bool) (p : Int) :
    List Nat :=
  (List.range origin.size).filter
    (fun i => anchorAt origin i == p && sideAt side i == b)

/-- **In-order subtree emission**, fuel-totalized (the `SeqKernel.emitK`
discipline): the subtrees of `c`'s left children, then `c` itself, then the
subtrees of its right children. This middle position is the whole design:
a descendant chain grows *inward* from its head, so a rival run hanging off
a different node can land before or after the chain but never inside it. -/
def subF (origin : Array Int) (side : Array Bool) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, c =>
    (childrenF origin side false (c : Int)).flatMap (subF origin side fuel)
      ++ c :: (childrenF origin side true (c : Int)).flatMap (subF origin side fuel)

/-- The emission below one origin value: left-side subtrees, then right-side
subtrees. (For a node this is its children's contribution *without* the node
itself; `fugueOrder` uses it at the root sentinel, which is not an element.) -/
def emitAtF (origin : Array Int) (side : Array Bool) (fuel : Nat) (p : Int) :
    List Nat :=
  (childrenF origin side false p).flatMap (subF origin side fuel)
    ++ (childrenF origin side true p).flatMap (subF origin side fuel)

/-- **The Fugue-style document order**: in-order walk from the root sentinel
with fuel `n`. Fuel `n` is adequate for every root-reachable element under
groundedness — the same pigeonhole as `SeqKernel.emitAll`, via the imported
`ChainK.length_le`; `fugueOrder_mem` below is the theorem. -/
def fugueOrder (origin : Array Int) (side : Array Bool) : List Nat :=
  emitAtF origin side origin.size (-1)

theorem mem_childrenF {b : Bool} {p : Int} {c : Nat} :
    c ∈ childrenF origin side b p
      ↔ c < origin.size ∧ anchorAt origin c = p ∧ sideAt side c = b := by
  simp [childrenF, List.mem_filter, List.mem_range, Bool.and_eq_true,
    beq_iff_eq]

/-- Everything a subtree emits is its own head or an in-range element — for
*every* input, junk included (the `SeqKernel` junk-degradation discipline). -/
theorem subF_mem_lt :
    ∀ fuel (c j : Nat), j ∈ subF origin side fuel c →
      j = c ∨ j < origin.size := by
  intro fuel
  induction fuel with
  | zero => intro c j h; simp [subF] at h
  | succ fuel ih =>
    intro c j h
    simp only [subF, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · obtain ⟨c', hc', hj⟩ := List.mem_flatMap.mp h
      rcases ih c' j hj with rfl | h'
      · exact .inr (mem_childrenF.mp hc').1
      · exact .inr h'
    · exact .inl h
    · obtain ⟨c', hc', hj⟩ := List.mem_flatMap.mp h
      rcases ih c' j hj with rfl | h'
      · exact .inr (mem_childrenF.mp hc').1
      · exact .inr h'

/-- Everything in the document order is below the size bound — for every
input. -/
theorem fugueOrder_lt {j : Nat} (h : j ∈ fugueOrder origin side) :
    j < origin.size := by
  simp only [fugueOrder, emitAtF, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp h
    rcases subF_mem_lt _ c j hj with rfl | h'
    · exact (mem_childrenF.mp hc).1
    · exact h'
  · obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp h
    rcases subF_mem_lt _ c j hj with rfl | h'
    · exact (mem_childrenF.mp hc).1
    · exact h'

/-! ## §2. The contrast pair — one editing intent, two merge outcomes

The intent, in both encodings: two replicas start from the empty document and
each types a two-element run at the head — the PaPoC'19 paper's §3 worst case
for RGA ("all characters anchored to the head of the document, ordered only
by timestamp"). Ids are dense indices in id-sorted order, `SeqKernel` style:
`0`/`2` are replica X's first and second insertions, `1`/`3` are replica Y's
(the same interleaved id assignment as `Sequence.headX`/`headY`, shifted down
by one because there is no sentinel id here).

RGA encodes the intent as four siblings of the root. Fugue encodes it as two
left-child chains: X's second keystroke goes *before* its first, so it hangs
as a left child of it — the run grows inward, `2 ← 0` and `3 ← 1`. -/

/-- Bool test: do the elements of `xs` occupy one contiguous block inside
`l`?  Mapped to a Bool mask, the mask must read `false* true* false*` — drop
the leading non-members, drop the member block, and nothing of `xs` may
remain. This tests *clustering only* (adjacency, not the block's internal
order); the exact-list equalities alongside pin the order. -/
def clustered (xs l : List Nat) : Bool :=
  (((l.map (fun i => xs.contains i)).dropWhile (fun b => !b)).dropWhile
    (fun b => b)).all (fun b => !b)

/-- ⚠ **RGA interleaves the head runs — through the shipping decision core.**
Four head-anchored elements (`anchor = -1` for all), no tombstones: the
merged document is `[3, 2, 1, 0]` — Y2, X2, Y1, X1, the two runs strictly
alternated; neither replica's pair `{0,2}` / `{1,3}` is even adjacent. This
is `Sequence.interleaving_anomaly` re-witnessed against `linearizeK`, the
function the compiled kernel actually runs. -/
theorem rga_head_runs_interleave :
    (linearizeK #[-1, -1, -1, -1] #[false, false, false, false]).toList
        = [3, 2, 1, 0]
    ∧ clustered [0, 2]
        (linearizeK #[-1, -1, -1, -1] #[false, false, false, false]).toList
        = false
    ∧ clustered [1, 3]
        (linearizeK #[-1, -1, -1, -1] #[false, false, false, false]).toList
        = false := by
  decide

/-- Each replica's *local* document under RGA (its own two elements, both
head-anchored, in its own dense encoding): `[1, 0]` — second keystroke first,
exactly what its author saw. The runs are contiguous on every screen; only
the merge destroys them. -/
theorem rga_head_run_local :
    (linearizeK #[-1, -1] #[false, false]).toList = [1, 0] := by
  decide

/-- The merged head-insert state, Fugue-style: `0` and `1` sit at the root
(the sibling contest between the two *runs*), and each replica's second
keystroke is a **left child of its first** — the run is a descent chain, not
a sibling pair. -/
def headRunsOrigin : Array Int := #[-1, -1, 0, 1]

/-- Sides for `headRunsOrigin`: root elements as right children of the
sentinel, run successors as left children (head insertion goes before). -/
def headRunsSide : Array Bool := #[true, true, false, false]

/-- **Fugue keeps the head runs contiguous — the other half of the contrast.**
The same intent as `rga_head_runs_interleave`, same ids, and the merged
document is `[2, 0, 3, 1]`: X's run `[2, 0]` intact, then Y's run `[3, 1]`
intact, each reading exactly as on its author's screen
(`fugue_head_run_local`). The sibling contest (`0` vs `1` at the root,
resolved by id) decided only which *run* comes first. -/
theorem fugue_head_runs_stay_contiguous :
    fugueOrder headRunsOrigin headRunsSide = [2, 0, 3, 1]
    ∧ clustered [0, 2] (fugueOrder headRunsOrigin headRunsSide) = true
    ∧ clustered [1, 3] (fugueOrder headRunsOrigin headRunsSide) = true := by
  decide

/-- Each replica's local document under Fugue (first element at the root,
second its left child): `[1, 0]` — **identical to the RGA local read**
(`rga_head_run_local`). The two designs agree on every single screen; they
part ways only at the merge. -/
theorem fugue_head_run_local :
    fugueOrder #[-1, 0] #[true, false] = [1, 0] := by
  decide

/-- The forward-typing variant under Fugue: each run a chain of **right**
children off its own first element (`0 → 2`, `1 → 3`, typing left-to-right).
Merged: `[0, 2, 1, 3]` — runs contiguous, first-writer-first under the
ascending arbitration. -/
theorem fugue_forward_runs_stay_contiguous :
    fugueOrder #[-1, -1, 0, 1] #[true, true, true, true] = [0, 2, 1, 3]
    ∧ clustered [0, 2]
        (fugueOrder #[-1, -1, 0, 1] #[true, true, true, true]) = true
    ∧ clustered [1, 3]
        (fugueOrder #[-1, -1, 0, 1] #[true, true, true, true]) = true := by
  decide

/-- The forward-typing intent under RGA (`Sequence.run_order_by_id` in kernel
encoding — the anchor array is the same `#[-1, -1, 0, 1]`, side-blind):
`[1, 3, 0, 2]`. Contiguous *by luck of this witness* — RGA only interleaves
the reverse-typed runs — but newest-run-first, an order neither user chose.
The contrast pair above is the head-insert case precisely because that is
where RGA's contiguity breaks and Fugue's does not. -/
theorem rga_forward_runs_arbitrated :
    (linearizeK #[-1, -1, 0, 1] #[false, false, false, false]).toList
        = [1, 3, 0, 2]
    ∧ clustered [0, 2]
        (linearizeK #[-1, -1, 0, 1] #[false, false, false, false]).toList
        = true
    ∧ clustered [1, 3]
        (linearizeK #[-1, -1, 0, 1] #[false, false, false, false]).toList
        = true := by
  decide

/-! ## §3. Infix toolkit

`List.IsInfix` (`l₁ <:+: l₂`, core) is contiguity itself: `∃ s t,
s ++ l₁ ++ t = l₂`. Note `Sublist` would NOT do — a sublist may scatter, and
scattering is exactly the anomaly. Four small constructors, DIY because core
stops at `trans`/`mem`. -/

private theorem infix_flatMap {f : Nat → List Nat} :
    ∀ {cs : List Nat} {c : Nat}, c ∈ cs → f c <:+: cs.flatMap f := by
  intro cs
  induction cs with
  | nil => intro c hc; cases hc
  | cons c₀ cs ih =>
    intro c hc
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨[], cs.flatMap f, by simp⟩
    · obtain ⟨s, t, hst⟩ := ih hc'
      exact ⟨f c₀ ++ s, t, by rw [← hst]; simp [List.append_assoc]⟩

private theorem infix_append_of_left {l pre post : List Nat}
    (h : l <:+: pre) : l <:+: pre ++ post := by
  obtain ⟨s, t, rfl⟩ := h
  exact ⟨s, t ++ post, by simp [List.append_assoc]⟩

private theorem infix_append_of_right {l pre post : List Nat}
    (h : l <:+: post) : l <:+: pre ++ post := by
  obtain ⟨s, t, rfl⟩ := h
  exact ⟨pre ++ s, t, by simp [List.append_assoc]⟩

private theorem infix_cons {l t : List Nat} {a : Nat} (h : l <:+: t) :
    l <:+: a :: t := by
  obtain ⟨s, u, rfl⟩ := h
  exact ⟨a :: s, u, rfl⟩

/-! ## §4. Descent: subtree blocks sit contiguously inside their ancestors

The structural heart of non-interleaving: one child's whole emission is an
*infix* of its parent's — it cannot straddle the parent's own position or a
sibling's block. Composed down a `ChainK` (imported; origin edges are
side-blind) this places every subtree as one contiguous block of the
document, with the fuel bookkeeping `n + 1 - depth` at each step. -/

/-- A child's subtree block is an infix of the emission below its origin. -/
theorem subF_infix_emitAt {b : Bool} {p : Int} {c : Nat}
    (hc : c ∈ childrenF origin side b p) (fuel : Nat) :
    subF origin side fuel c <:+: emitAtF origin side fuel p := by
  unfold emitAtF
  cases b with
  | false => exact infix_append_of_left (infix_flatMap hc)
  | true => exact infix_append_of_right (infix_flatMap hc)

/-- A child's subtree block is an infix of its parent's subtree block: it
lands wholly inside the left half or wholly inside the right half — never
across the parent's own position. -/
theorem subF_infix_step {b : Bool} {c c' : Nat}
    (hc' : c' ∈ childrenF origin side b (c : Int)) (fuel : Nat) :
    subF origin side fuel c' <:+: subF origin side (fuel + 1) c := by
  cases b with
  | false =>
    simp only [subF]
    exact infix_append_of_left (infix_flatMap hc')
  | true =>
    simp only [subF]
    exact infix_append_of_right (infix_cons (infix_flatMap hc'))

private theorem chain_subF_infix_aux {p : Int} {i : Nat} {l : List Nat}
    (h : ChainK origin p i l) :
    ∀ (c : Nat), p = (c : Int) → ∀ fuel, l.length ≤ fuel →
      subF origin side (fuel - l.length) i <:+: subF origin side fuel c := by
  induction h with
  | @child p j hj ha =>
    intro c hp fuel hf
    subst hp
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hmem : j ∈ childrenF origin side (sideAt side j) (c : Int) :=
        mem_childrenF.mpr ⟨hj, ha, rfl⟩
      simpa [Nat.succ_sub_succ] using subF_infix_step hmem fuel
  | @step p cc j l hc ha htail ih =>
    intro c hp fuel hf
    subst hp
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hlen : l.length ≤ fuel := by
        simp only [List.length_cons] at hf; omega
      have h1 := ih cc rfl fuel hlen
      have hmem : cc ∈ childrenF origin side (sideAt side cc) (c : Int) :=
        mem_childrenF.mpr ⟨hc, ha, rfl⟩
      have h2 := subF_infix_step hmem fuel
      have harith : (fuel + 1) - (cc :: l).length = fuel - l.length := by
        simp [List.length_cons, Nat.succ_sub_succ]
      rw [harith]
      exact h1.trans h2

/-- **Root descent**: an element with a root chain of length `d ≤ n` receives
fuel `n + 1 - d`, and its whole subtree block sits contiguously — as an infix
— inside the document order. -/
theorem chainRoot_subF_infix {i : Nat} {l : List Nat}
    (h : ChainK origin (-1) i l) (hl : l.length ≤ origin.size) :
    subF origin side (origin.size + 1 - l.length) i
      <:+: fugueOrder origin side := by
  cases h with
  | child hi ha =>
    have hmem : i ∈ childrenF origin side (sideAt side i) (-1) :=
      mem_childrenF.mpr ⟨hi, ha, rfl⟩
    simpa [fugueOrder, Nat.add_sub_cancel]
      using subF_infix_emitAt hmem origin.size
  | @step _ c i' l' hc ha htail =>
    have hlen : l'.length ≤ origin.size := by
      simp only [List.length_cons] at hl; omega
    have h1 := chain_subF_infix_aux (side := side) htail c rfl origin.size hlen
    have hmem : c ∈ childrenF origin side (sideAt side c) (-1) :=
      mem_childrenF.mpr ⟨hc, ha, rfl⟩
    have h2 := subF_infix_emitAt hmem origin.size
    have harith : origin.size + 1 - (c :: l').length
        = origin.size - l'.length := by
      simp [List.length_cons, Nat.succ_sub_succ]
    rw [harith]
    simp only [fugueOrder]
    exact h1.trans h2

/-- A node heads its own subtree block (any positive fuel). -/
theorem self_mem_subF {fuel : Nat} (hf : 0 < fuel) (c : Nat) :
    c ∈ subF origin side fuel c := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [subF]
    exact List.mem_append.mpr (.inr List.mem_cons_self)

/-- **Completeness**: under `SeqKernel.WFK` — the exact hypothesis the Rust
encoder establishes for the shipping kernel, imported unchanged — every
in-range element appears in the Fugue order. Rides `chain_to_root` and the
`ChainK.length_le` pigeonhole verbatim; the side array never enters. -/
theorem fugueOrder_mem {r : Nat → Nat} (hwf : WFK r origin) {i : Nat}
    (hi : i < origin.size) : i ∈ fugueOrder origin side := by
  obtain ⟨l, hl⟩ := chain_to_root hwf i hi
  have hlen := hl.length_le hwf.grounded
  exact (chainRoot_subF_infix hl hlen).mem (self_mem_subF (by omega) i)

/-! ## §5. Runs are contiguous: the general theorem at this scale -/

/-- `Clan origin side c l` — the subtree of `c` is exactly a single-child
descent chain, and `l` is its in-order emission (the run in document order).
This is the formal shape of **a replica's uninterrupted run**: each
keystroke a child of the previous one (left = typed before it, right = typed
after it), with nothing else ever inserted inside. The hypothesis is
load-bearing and must be: a run someone typed *into* should split. -/
inductive Clan (origin : Array Int) (side : Array Bool) :
    Nat → List Nat → Prop where
  /-- A childless element: the run's last keystroke. -/
  | leaf {c : Nat}
      (hl : childrenF origin side false (c : Int) = [])
      (hr : childrenF origin side true (c : Int) = []) :
      Clan origin side c [c]
  /-- The run continues with one left child (its successor was typed before
  it — head insertion): the successor's whole emission precedes `c`. -/
  | left {c c' : Nat} {l : List Nat}
      (hl : childrenF origin side false (c : Int) = [c'])
      (hr : childrenF origin side true (c : Int) = [])
      (htail : Clan origin side c' l) :
      Clan origin side c (l ++ [c])
  /-- The run continues with one right child (its successor was typed after
  it — forward typing): the successor's whole emission follows `c`. -/
  | right {c c' : Nat} {l : List Nat}
      (hl : childrenF origin side false (c : Int) = [])
      (hr : childrenF origin side true (c : Int) = [c'])
      (htail : Clan origin side c' l) :
      Clan origin side c (c :: l)

theorem Clan.length_pos {c : Nat} {l : List Nat}
    (h : Clan origin side c l) : 0 < l.length := by
  cases h <;> simp

/-- A clan's emission is *exactly* its run list, at any adequate fuel: the
subtree computes to the run, nothing more, nothing less. -/
theorem Clan.subF_eq {c : Nat} {l : List Nat} (h : Clan origin side c l) :
    ∀ {fuel : Nat}, l.length ≤ fuel → subF origin side fuel c = l := by
  induction h with
  | @leaf c hl hr =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel => simp [subF, hl, hr]
  | @left c c' l hl hr htail ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hlen : l.length ≤ fuel := by
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hf
        omega
      simp [subF, hl, hr, ih hlen]
  | @right c c' l hl hr htail ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hlen : l.length ≤ fuel := by
        simp only [List.length_cons] at hf; omega
      simp [subF, hl, hr, ih hlen]

/-- Root chain + clan together fit inside the element count: the combined
descent (root to `c`, then down the run) is one `ChainK`, and grounded chains
obey the `ChainK.length_le` pigeonhole. This is what pays the fuel bill. -/
theorem Clan.chain_bound {r : Nat → Nat} (hgr : GroundedAnchors r origin)
    {c : Nat} {l : List Nat} (h : Clan origin side c l) :
    ∀ {lc : List Nat}, ChainK origin (-1) c lc →
      lc.length + l.length ≤ origin.size + 1 := by
  induction h with
  | @leaf c hl hr =>
    intro lc hlc
    have := hlc.length_le hgr
    simp only [List.length_cons, List.length_nil]
    omega
  | @left c c' l hl hr htail ih =>
    intro lc hlc
    have hc' : c' ∈ childrenF origin side false (c : Int) := by
      rw [hl]; exact List.mem_singleton.mpr rfl
    obtain ⟨hsz, ha, -⟩ := mem_childrenF.mp hc'
    have hb := ih (hlc.extend hsz ha)
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hb ⊢
    omega
  | @right c c' l hl hr htail ih =>
    intro lc hlc
    have hc' : c' ∈ childrenF origin side true (c : Int) := by
      rw [hr]; exact List.mem_singleton.mpr rfl
    obtain ⟨hsz, ha, -⟩ := mem_childrenF.mp hc'
    have hb := ih (hlc.extend hsz ha)
    simp only [List.length_append, List.length_cons, List.length_nil]
      at hb ⊢
    omega

/-- **Run contiguity — the general theorem at this scale.** In ANY grounded
state — any number of other elements, hanging anywhere else in the tree — a
run that is a maximal single-child descent chain (`Clan`) reachable from the
root appears in the Fugue order as one contiguous infix, in exactly its own
document order. Sibling arbitration can place whole runs relative to each
other; it cannot reach inside one. Under RGA-style anchoring the head-insert
run is not a chain but a sibling family, and `rga_head_runs_interleave` shows
what arbitration then does to it. -/
theorem run_contiguous {r : Nat → Nat} (hgr : GroundedAnchors r origin)
    {c : Nat} {lc l : List Nat} (hlc : ChainK origin (-1) c lc)
    (hcl : Clan origin side c l) : l <:+: fugueOrder origin side := by
  have hb := hcl.chain_bound hgr hlc
  have hpos := hcl.length_pos
  have hlcn : lc.length ≤ origin.size := by omega
  have hinf := chainRoot_subF_infix (side := side) hlc hlcn
  have heq := hcl.subF_eq
    (fuel := origin.size + 1 - lc.length) (by omega)
  rw [heq] at hinf
  exact hinf

/-- `run_contiguous` under the kernel's own well-formedness package: any
in-range clan head is root-reachable (`chain_to_root`), so its run is a
contiguous infix of the document. -/
theorem run_contiguous_of_wfk {r : Nat → Nat} (hwf : WFK r origin)
    {c : Nat} (hc : c < origin.size) {l : List Nat}
    (hcl : Clan origin side c l) : l <:+: fugueOrder origin side := by
  obtain ⟨lc, hlc⟩ := chain_to_root hwf c hc
  exact run_contiguous hwf.grounded hlc hcl

/-! ### The general theorem fires on the concrete witness

Guard against a theorem that is true and never inhabited: the head-insert
contrast state instantiates every hypothesis, and the decide-computed
contiguity of §2 falls out of `run_contiguous` as well. -/

/-- The merged head-insert state is `WFK` with rank = index (the dense order
here is creation-ordered, so `SeqKernel.wfk_of_index_ordered` applies). -/
theorem headRuns_wfk : WFK (fun i => i) headRunsOrigin :=
  wfk_of_index_ordered (by decide)

/-- X's run is a clan: `2` is the sole (left) child of `0`, and childless. -/
theorem headRunsX_clan : Clan headRunsOrigin headRunsSide 0 [2, 0] :=
  .left (by decide) (by decide) (.leaf (by decide) (by decide))

/-- Y's run is a clan: `3` is the sole (left) child of `1`, and childless. -/
theorem headRunsY_clan : Clan headRunsOrigin headRunsSide 1 [3, 1] :=
  .left (by decide) (by decide) (.leaf (by decide) (by decide))

/-- Both runs' contiguity in the merged document, derived from the general
theorem rather than computed — the witness that `run_contiguous`'s
hypotheses are satisfiable exactly where the anomaly lives. -/
theorem head_runs_contiguous_by_the_theorem :
    [2, 0] <:+: fugueOrder headRunsOrigin headRunsSide
    ∧ [3, 1] <:+: fugueOrder headRunsOrigin headRunsSide :=
  ⟨run_contiguous_of_wfk headRuns_wfk (by decide) headRunsX_clan,
   run_contiguous_of_wfk headRuns_wfk (by decide) headRunsY_clan⟩

/-! ## §6. Duplicate-freedom of the in-order walk

`SeqKernel` §7's sibling-subtree disjointness is a pure *origin-edge*
argument — `not_belowK_sibling` and `belowK_sibling_disjoint` never look at a
side bit — so it is imported and reused, not re-proved. What is new is the
counting for the in-order shape `left ++ c :: right`: a node's two child lists
concatenate into one duplicate-free family of siblings, and the node itself
cannot recur inside its own subtree (rank strictly increases downward).

This is what upgrades the contiguity results below from bare `IsInfix` to the
clustering the anomaly is stated with: an infix says the run occurs
contiguously *somewhere*, and only duplicate-freedom rules out a second,
scattered occurrence. -/

/-- Whatever a subtree emits is its own head or genuinely below it (`BelowK`
is `SeqKernel`'s origin-edge relation, side-blind) — for every input, any
fuel. -/
theorem subF_below :
    ∀ fuel (c j : Nat), j ∈ subF origin side fuel c →
      j = c ∨ BelowK origin ((c : Int)) j := by
  intro fuel
  induction fuel with
  | zero => intro c j h; simp [subF] at h
  | succ fuel ih =>
    intro c j h
    simp only [subF, List.mem_append, List.mem_cons] at h
    have hstep : ∀ {b : Bool} {c' : Nat}, c' ∈ childrenF origin side b (c : Int) →
        j ∈ subF origin side fuel c' → BelowK origin ((c : Int)) j := by
      intro b c' hc' hj
      obtain ⟨hsz, ha, -⟩ := mem_childrenF.mp hc'
      rcases ih c' j hj with rfl | ⟨l, hl⟩
      · exact ⟨[j], .child hsz ha⟩
      · exact ⟨c' :: l, .step hsz ha hl⟩
    rcases h with h | h | h
    · obtain ⟨c', hc', hj⟩ := List.mem_flatMap.mp h
      exact .inr (hstep hc' hj)
    · exact .inl h
    · obtain ⟨c', hc', hj⟩ := List.mem_flatMap.mp h
      exact .inr (hstep hc' hj)

/-- The two child lists of one node concatenated: `kidsF` is the whole
same-origin sibling family, left children first. -/
def kidsF (origin : Array Int) (side : Array Bool) (p : Int) : List Nat :=
  childrenF origin side false p ++ childrenF origin side true p

theorem mem_kidsF {p : Int} {c : Nat} :
    c ∈ kidsF origin side p ↔ c < origin.size ∧ anchorAt origin c = p := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h' | h' <;>
      exact ⟨(mem_childrenF.mp h').1, (mem_childrenF.mp h').2.1⟩
  · intro ⟨h1, h2⟩
    cases hs : sideAt side c with
    | false => exact List.mem_append.mpr (.inl (mem_childrenF.mpr ⟨h1, h2, hs⟩))
    | true => exact List.mem_append.mpr (.inr (mem_childrenF.mpr ⟨h1, h2, hs⟩))

/-- The sibling family is duplicate-free: each side's list is a filtered
range, and no element can read `false` and `true` at once. -/
theorem kidsF_nodup (p : Int) : (kidsF origin side p).Nodup := by
  have hfil : ∀ b : Bool, (childrenF origin side b p).Nodup := fun b =>
    List.Sublist.nodup List.filter_sublist List.nodup_range
  refine List.nodup_append.mpr ⟨hfil false, hfil true, ?_⟩
  intro a ha b hb hab
  subst hab
  have h1 := (mem_childrenF.mp ha).2.2
  have h2 := (mem_childrenF.mp hb).2.2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- The in-order emission below one origin value, as one flatMap over the
whole sibling family — the node's own position drops out, so counting sees a
single family of disjoint subtrees. -/
theorem emitAtF_eq_kids_flatMap (fuel : Nat) (p : Int) :
    emitAtF origin side fuel p = (kidsF origin side p).flatMap
      (subF origin side fuel) := by
  simp [emitAtF, kidsF, List.flatMap_append]

private theorem count_flatMap_le_one_F {r : Nat → Nat}
    (hgr : GroundedAnchors r origin) {fuel : Nat} {p : Int}
    (ih : ∀ (c' j : Nat), (subF origin side fuel c').count j ≤ 1) :
    ∀ cs : List Nat, cs.Nodup →
      (∀ c ∈ cs, c < origin.size ∧ anchorAt origin c = p) → ∀ j,
      (cs.flatMap (subF origin side fuel)).count j ≤ 1 := by
  intro cs hnodup hanchor
  apply ListProofs.flatMap_count_le_one_of_nodup_of_pairwise_disjoint
    (subF origin side fuel) hnodup
  · intro c _ j
    exact ih c j
  · intro c hc c' hc' hcc' j hj hj'
    have h1 := subF_below (side := side) fuel c j hj
    have h2 := subF_below (side := side) fuel c' j hj'
    obtain ⟨hca_sz, hca⟩ := hanchor c hc
    obtain ⟨hc'a_sz, hc'a⟩ := hanchor c' hc'
    rcases h1 with rfl | hb1
    · rcases h2 with rfl | hb2
      · exact hcc' rfl
      · exact not_belowK_sibling hgr hca hc'a hb2
    · rcases h2 with rfl | hb2
      · exact not_belowK_sibling hgr hc'a hca hb1
      · exact belowK_sibling_disjoint hgr hca_sz hca hc'a_sz hc'a hcc' j hb1 hb2

/-- Every id is emitted at most once by a subtree, at any fuel, under
groundedness alone. -/
theorem subF_count_le_one {r : Nat → Nat} (hgr : GroundedAnchors r origin) :
    ∀ fuel (c j : Nat), (subF origin side fuel c).count j ≤ 1 := by
  intro fuel
  induction fuel with
  | zero => intro c j; simp [subF]
  | succ fuel ih =>
    intro c j
    have hfam : (subF origin side (fuel + 1) c).count j
        = ((kidsF origin side (c : Int)).flatMap (subF origin side fuel)).count j
          + (if c = j then 1 else 0) := by
      simp only [subF, kidsF, List.count_append, List.flatMap_append,
        List.count_cons, beq_iff_eq]
      omega
    have hfl := count_flatMap_le_one_F (side := side) hgr ih
      (kidsF origin side (c : Int)) (kidsF_nodup _) (fun c' hc' => mem_kidsF.mp hc') j
    by_cases hjc : c = j
    · subst hjc
      have hzero : ((kidsF origin side (c : Int)).flatMap
          (subF origin side fuel)).count c = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro hmem
        obtain ⟨c', hc'mem, hjc'⟩ := List.mem_flatMap.mp hmem
        obtain ⟨hsz, ha⟩ := mem_kidsF.mp hc'mem
        have hbelow : BelowK origin ((c : Int)) c := by
          rcases subF_below (side := side) fuel c' c hjc' with rfl | ⟨l, hl⟩
          · exact ⟨[c], .child hsz ha⟩
          · exact ⟨c' :: l, .step hsz ha hl⟩
        have := hbelow.rank_lt hgr (by omega)
        simp only [Int.toNat_natCast] at this
        omega
      rw [hfam, hzero]
      simp
    · rw [hfam]
      simp only [hjc, if_false]
      omega

/-- **The Fugue document order is duplicate-free**, under groundedness alone —
`SeqKernel` §7's rank argument transferred to the in-order walk. -/
theorem fugueOrder_nodup {r : Nat → Nat} (hgr : GroundedAnchors r origin) :
    (fugueOrder origin side).Nodup := by
  have hcount : ∀ j, (fugueOrder origin side).count j ≤ 1 := by
    intro j
    rw [fugueOrder, emitAtF_eq_kids_flatMap]
    exact count_flatMap_le_one_F (side := side) hgr
      (subF_count_le_one hgr origin.size) (kidsF origin side (-1))
      (kidsF_nodup _) (fun c hc => mem_kidsF.mp hc) j
  exact List.nodup_iff_count.mpr hcount

/-! ## §7. What "interleaved" means, and contiguity in that language

Kleppmann–Gomes–Mulligan–Beresford's clause 1(d) (PaPoC'19 §2.1) rules out
exactly this pattern: the document reads an element of one concurrent
insertion set, then an element of the other, then the first set again. `<+`
(`List.Sublist`) says "these three appear in this order, anything else
possibly between", which is the pattern verbatim. `Splits l xs y` is that
pattern for a single foreign element `y`; the general theorem below denies it
for every `y` outside the run, which is stronger than denying it only for the
rival run's elements. -/

open scoped List -- `<+` (`List.Sublist`) is scoped notation in core

/-- **The interleaving pattern**: somewhere in `l`, an element of `xs`, then
`y`, then an element of `xs` again — `y` sits strictly inside the run. -/
def Splits (l xs : List Nat) (y : Nat) : Prop :=
  ∃ a ∈ xs, ∃ b ∈ xs, [a, y, b] <+ l

/-- A three-element pattern whose leading element is absent from the left half
of an append lies wholly in the right half. -/
private theorem triple_sublist_right {a y b : Nat} {L R : List Nat}
    (h : [a, y, b] <+ L ++ R) (ha : a ∉ L) : [a, y, b] <+ R := by
  obtain ⟨l₁, l₂, heq, h₁, h₂⟩ := List.sublist_append_iff.mp h
  cases l₁ with
  | nil => simpa [heq] using h₂
  | cons c cs =>
    exfalso
    have hc : a = c := by
      simp only [List.cons_append, List.cons.injEq] at heq
      exact heq.1
    exact ha (hc ▸ h₁.mem List.mem_cons_self)

/-- **Contiguity is exactly non-interleaving.** A run occupying one contiguous
block of a duplicate-free document cannot be split: nothing outside the run
appears between two of its elements. Both hypotheses are supplied by §5–§6 for
`fugueOrder` (`run_contiguous` and `fugueOrder_nodup`), so this is the bridge
from "the run is an infix" to the paper's clause. -/
theorem not_splits_of_infix {l xs : List Nat} (hinf : xs <:+: l)
    (hn : l.Nodup) {y : Nat} (hy : y ∉ xs) : ¬ Splits l xs y := by
  obtain ⟨s, t, rfl⟩ := hinf
  rw [List.append_assoc] at hn
  rintro ⟨a, ha, b, hb, hsub⟩
  rw [List.append_assoc] at hsub
  obtain ⟨-, hxt, hsx⟩ := List.nodup_append.mp hn
  obtain ⟨-, -, hxst⟩ := List.nodup_append.mp hxt
  have ha_s : a ∉ s := fun hmem =>
    hsx a hmem a (List.mem_append_left _ ha) rfl
  have hb_t : b ∉ t.reverse := fun hmem =>
    hxst b hb b (List.mem_reverse.mp hmem) rfl
  have step1 : [a, y, b] <+ xs ++ t := triple_sublist_right hsub ha_s
  have step2 : [b, y, a] <+ t.reverse ++ xs.reverse := by
    simpa [List.reverse_append] using step1.reverse
  have step3 : [b, y, a] <+ xs.reverse := triple_sublist_right step2 hb_t
  exact hy (List.mem_reverse.mp (step3.mem (by simp)))

/-- **Kleppmann et al.'s clause 1(d), in its literal disjunctive form**: two
disjoint runs, each a contiguous block of a duplicate-free document, land one
wholly before the other — "either all X insertions appear before all Y
insertions in the document, or vice versa, but they are never interleaved".
`[a, b] <+ l` says `a` occurs before `b`. Both runs must be inhabited, since
the disjunction is about where their elements sit. -/
theorem runs_ordered_of_infix {l xs ys : List Nat} {a₀ b₀ : Nat}
    (hx : xs <:+: l) (hy : ys <:+: l) (hn : l.Nodup)
    (hdisj : ∀ a ∈ xs, a ∉ ys) (ha₀ : a₀ ∈ xs) (hb₀ : b₀ ∈ ys) :
    (∀ a ∈ xs, ∀ b ∈ ys, [a, b] <+ l) ∨ (∀ b ∈ ys, ∀ a ∈ xs, [b, a] <+ l) := by
  obtain ⟨s, t, rfl⟩ := hx
  rw [List.append_assoc] at hn hy ⊢
  have hmem : ∀ b ∈ ys, b ∈ s ∨ b ∈ t := by
    intro b hb
    have hbl : b ∈ s ++ (xs ++ t) := List.Sublist.mem hb hy.sublist
    rcases List.mem_append.mp hbl with h | h
    · exact .inl h
    · rcases List.mem_append.mp h with h' | h'
      · exact absurd hb (hdisj b h')
      · exact .inr h'
  have hsplit : ∀ b ∈ ys, ∀ b' ∈ ys, b ∈ s → b' ∈ t → False := by
    intro b hb b' hb' hbs hb't
    refine not_splits_of_infix hy hn (hdisj a₀ ha₀) ⟨b, hb, b', hb', ?_⟩
    exact List.Sublist.append (List.singleton_sublist.mpr hbs)
      (List.Sublist.append (List.singleton_sublist.mpr ha₀)
        (List.singleton_sublist.mpr hb't))
  rcases hmem b₀ hb₀ with h0 | h0
  · refine .inr (fun b hb a ha => ?_)
    have hbs : b ∈ s := (hmem b hb).resolve_right (fun ht => hsplit b₀ hb₀ b hb h0 ht)
    exact List.Sublist.append (List.singleton_sublist.mpr hbs)
      ((List.singleton_sublist.mpr ha).trans (List.sublist_append_left _ _))
  · refine .inl (fun a ha b hb => ?_)
    have hbt : b ∈ t := (hmem b hb).resolve_left (fun hs => hsplit b hb b₀ hb₀ hs h0)
    exact (List.Sublist.append (List.singleton_sublist.mpr ha)
      (List.singleton_sublist.mpr hbt)).trans (List.sublist_append_right _ _)

private theorem dropWhile_append_of_all {p : Bool → Bool} :
    ∀ {l₁ : List Bool}, (∀ b ∈ l₁, p b = true) → ∀ l₂ : List Bool,
      (l₁ ++ l₂).dropWhile p = l₂.dropWhile p := by
  intro l₁
  induction l₁ with
  | nil => intro _ l₂; simp
  | cons a t ih =>
    intro h l₂
    rw [List.cons_append, List.dropWhile_cons_of_pos (by simp [h a List.mem_cons_self])]
    exact ih (fun b hb => h b (List.mem_cons_of_mem a hb)) l₂

private theorem dropWhile_of_all_pos {p : Bool → Bool} {l : List Bool}
    (h : ∀ b ∈ l, p b = true) : l.dropWhile p = [] := by
  simpa using dropWhile_append_of_all h []

private theorem dropWhile_of_head_neg {p : Bool → Bool} :
    ∀ {l : List Bool}, (∀ b ∈ l, p b = false) → l.dropWhile p = l := by
  intro l
  cases l with
  | nil => intro _; simp
  | cons a t =>
    intro h
    exact List.dropWhile_cons_of_neg (by simp [h a List.mem_cons_self])

/-- **Infix + duplicate-freedom ⇒ clustered.** The Bool test of §2 reads
`false* true* false*` on the membership mask, which is precisely what a
contiguous block in a duplicate-free list produces. This is what lets the
general theorem below conclude in the same vocabulary the concrete contrast
pair of §2 was computed in. -/
theorem clustered_of_infix_of_nodup {xs l : List Nat} (hinf : xs <:+: l)
    (hn : l.Nodup) : clustered xs l = true := by
  obtain ⟨s, t, rfl⟩ := hinf
  rw [List.append_assoc] at hn ⊢
  obtain ⟨-, hxt, hsx⟩ := List.nodup_append.mp hn
  obtain ⟨-, -, hxst⟩ := List.nodup_append.mp hxt
  have hs : ∀ b ∈ s.map (fun i => xs.contains i), b = false := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    simp only [List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun hix => hsx i hi i (List.mem_append_left _ hix) rfl
  have ht : ∀ b ∈ t.map (fun i => xs.contains i), b = false := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    simp only [List.contains_eq_mem, decide_eq_false_iff_not]
    exact fun hix => hxst i hix i hi rfl
  have hx : ∀ b ∈ xs.map (fun i => xs.contains i), b = true := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    simpa using hi
  have hT : (t.map (fun i => xs.contains i)).dropWhile (fun b => b)
      = t.map (fun i => xs.contains i) :=
    dropWhile_of_head_neg (fun b hb => by simp [ht b hb])
  have hTall : ((t.map (fun i => xs.contains i)).all (fun b => !b)) = true :=
    List.all_eq_true.mpr (fun b hb => by simp [ht b hb])
  simp only [clustered, List.map_append]
  rw [dropWhile_append_of_all (fun b hb => by simp [hs b hb])]
  cases hxs : xs.map (fun i => xs.contains i) with
  | nil =>
    rw [List.nil_append, dropWhile_of_all_pos
      (l := t.map (fun i => xs.contains i)) (fun b hb => by simp [ht b hb])]
    simp
  | cons c cs =>
    have hcs : ∀ b ∈ c :: cs, b = true := fun b hb => hx b (by rw [hxs]; exact hb)
    rw [List.cons_append,
      List.dropWhile_cons_of_neg (by simp [hcs c List.mem_cons_self]),
      ← List.cons_append,
      dropWhile_append_of_all (fun b hb => by simp [hcs b hb]), hT, hTall]

/-! ## §8. The insertion model: operations, replica state, merge

Everything above decides an order on a *state*. This section says where the
states come from: an operation, a replica's set of them, and the merge. The
substrate is a grow-only set — `merge` is union, `apply` only ever adds — so
the CRDT properties are the three below (`merge_assoc`, `docOrder_merge_self`,
`docOrder_merge_comm`), not an extra assumption.

An operation carries what Fugue's insert path decides: the new element's id,
its origin, and which side of that origin it hangs on. A replica materializes
its id space into the two word arrays of §1 and reads the document with
`fugueOrder`; `rgaDoc` reads the *same* operations RGA-style (side-blind,
`SeqKernel.linearizeK`), which is what makes §10's contrast a comparison of
two readings of one editing history rather than two unrelated states. -/

/-- **An insertion operation**: create element `id` as a child of `origin`
(`-1` = the root sentinel) on side `side` (`true` = right, `false` = left).
Ids are minted by the replica and never reused — `Concurrent` below says so
explicitly rather than assuming it. -/
structure InsOp where
  /-- The new element's id, which is also its index in the materialized
  arrays of §1. -/
  id : Nat
  /-- The origin the new element hangs from: `-1` for the root sentinel,
  otherwise the id of an element the replica had already received. -/
  origin : Int
  /-- Which side of the origin: `true` = right child, `false` = left child. -/
  side : Bool
deriving DecidableEq, Repr

/-- **A replica's state**: the set of insertions it has applied. Grow-only —
this is the whole CRDT substrate, and `merge` below is its join. -/
abbrev OpSet := List InsOp

/-- The operation governing element `i` — the *first* op with that id, so a
re-delivered operation is a no-op at the document level (first-writer-wins on
an id, which for immutable insertions means idempotence). -/
def lookup (s : OpSet) (i : Nat) : Option InsOp :=
  s.find? (fun op => op.id == i)

/-- The origin element `i` was inserted at, `-1` if no op mentions `i` —
the junk-degradation discipline of `SeqKernel.anchorAt`, made total. -/
def originOf (s : OpSet) (i : Nat) : Int :=
  (lookup s i).elim (-1) InsOp.origin

/-- The side element `i` hangs on, `true` if no op mentions `i` (matching
`sideAt`'s out-of-range default). -/
def sideOf (s : OpSet) (i : Nat) : Bool :=
  (lookup s i).elim true InsOp.side

/-- Materialize the origin word array over the id space `0 .. n-1`. -/
def originsOf (n : Nat) (s : OpSet) : Array Int :=
  ((List.range n).map (originOf s)).toArray

/-- Materialize the side word array over the id space `0 .. n-1`. -/
def sidesOf (n : Nat) (s : OpSet) : Array Bool :=
  ((List.range n).map (sideOf s)).toArray

/-- **The document a replica reads**: materialize its op set, then run the
Fugue order of §1. -/
def docOrder (n : Nat) (s : OpSet) : List Nat :=
  fugueOrder (originsOf n s) (sidesOf n s)

/-- **The same operations read RGA-style**: `SeqKernel.linearizeK` on the same
materialized origins, side-blind, no tombstones. -/
def rgaDoc (n : Nat) (s : OpSet) : List Nat :=
  (linearizeK (originsOf n s) #[]).toList

/-- Applying one operation: add it to the set. -/
def apply (s : OpSet) (op : InsOp) : OpSet := s ++ [op]

/-- Applying a batch, in delivery order. -/
def applyAll (s : OpSet) (ops : List InsOp) : OpSet := ops.foldl apply s

/-- **The merge**: the grow-only union of two replicas' operation sets. -/
def merge (s t : OpSet) : OpSet := s ++ t

theorem applyAll_eq_merge : ∀ (ops : List InsOp) (s : OpSet),
    applyAll s ops = merge s ops := by
  intro ops
  induction ops with
  | nil => intro s; simp [applyAll, merge]
  | cons op ops ih =>
    intro s
    simp only [applyAll, List.foldl_cons] at *
    rw [ih (apply s op)]
    simp [apply, merge]

theorem merge_assoc (s t u : OpSet) : merge (merge s t) u = merge s (merge t u) := by
  simp [merge, List.append_assoc]

/-! ### Materialization -/

@[simp] theorem size_originsOf (n : Nat) (s : OpSet) : (originsOf n s).size = n := by
  simp [originsOf]

@[simp] theorem size_sidesOf (n : Nat) (s : OpSet) : (sidesOf n s).size = n := by
  simp [sidesOf]

theorem anchorAt_originsOf {n i : Nat} {s : OpSet} (hi : i < n) :
    anchorAt (originsOf n s) i = originOf s i := by
  have h : (originsOf n s)[i]? = some (originOf s i) := by
    simp [originsOf, hi]
  simp [anchorAt, Array.getD_eq_getD_getElem?, h]

theorem sideAt_sidesOf {n i : Nat} {s : OpSet} (hi : i < n) :
    sideAt (sidesOf n s) i = sideOf s i := by
  have h : (sidesOf n s)[i]? = some (sideOf s i) := by
    simp [sidesOf, hi]
  simp [sideAt, Array.getD_eq_getD_getElem?, h]

/-- The child lists of a materialized state, in the model's own vocabulary. -/
theorem childrenF_of_ops {n : Nat} {s : OpSet} (b : Bool) (p : Int) :
    childrenF (originsOf n s) (sidesOf n s) b p
      = (List.range n).filter (fun i => originOf s i == p && sideOf s i == b) := by
  unfold childrenF
  rw [size_originsOf]
  refine List.filter_congr (fun i hi => ?_)
  rw [anchorAt_originsOf (List.mem_range.mp hi), sideAt_sidesOf (List.mem_range.mp hi)]

private theorem filter_range_eq_nil {n : Nat} {p : Nat → Bool}
    (h : ∀ i, i < n → p i = false) : (List.range n).filter p = [] :=
  List.filter_eq_nil_iff.mpr (fun a ha => by simp [h a (List.mem_range.mp ha)])

private theorem filter_range_eq_singleton {p : Nat → Bool} {x : Nat}
    (hpx : p x = true) : ∀ n, x < n → (∀ i, i < n → p i = true → i = x) →
      (List.range n).filter p = [x] := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hxn huniq
    rw [List.range_succ, List.filter_append]
    by_cases hxe : x = n
    · subst hxe
      have h1 : (List.range x).filter p = [] :=
        filter_range_eq_nil (fun i hi => by
          cases hpi : p i with
          | false => rfl
          | true => exact absurd (huniq i (by omega) hpi) (by omega))
      simp [h1, hpx]
    · have hxlt : x < n := by omega
      have h2 : (List.range n).filter p = [x] :=
        ih hxlt (fun i hi hpi => huniq i (by omega) hpi)
      have h3 : p n = false := by
        cases hpn : p n with
        | false => rfl
        | true => exact absurd (huniq n (by omega) hpn).symm hxe
      simp [h2, h3]

/-! ### Lookup -/

theorem lookup_mem {s : OpSet} {i : Nat} {op : InsOp} (h : lookup s i = some op) :
    op ∈ s ∧ op.id = i := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem lookup_append_of_left_miss {s t : OpSet} {i : Nat}
    (h : ∀ op ∈ s, op.id ≠ i) : lookup (s ++ t) i = lookup t i := by
  have hnone : s.find? (fun op => op.id == i) = none :=
    List.find?_eq_none.mpr (fun a ha => by simpa using h a ha)
  simp [lookup, List.find?_append, hnone]

theorem lookup_cons_hit {s : OpSet} {op : InsOp} :
    lookup (op :: s) op.id = some op := by
  simp [lookup]

theorem lookup_cons_miss {s : OpSet} {op : InsOp} {i : Nat} (h : op.id ≠ i) :
    lookup (op :: s) i = lookup s i := by
  simp [lookup, h]

/-! ### The merge is a CRDT join at the document level -/

/-- Two op sets agree wherever their id spaces overlap. Disjoint id spaces —
what `Concurrent` below requires of distinct replicas — is the usual way this
holds; re-delivery of the same operation is the other. -/
def Agree (s t : OpSet) : Prop :=
  ∀ op ∈ s, ∀ op' ∈ t, op.id = op'.id → op = op'

theorem lookup_merge_comm {s t : OpSet} (h : Agree s t) (i : Nat) :
    lookup (merge s t) i = lookup (merge t s) i := by
  simp only [merge, lookup, List.find?_append]
  cases hs : s.find? (fun op => op.id == i) with
  | none => cases ht : t.find? (fun op => op.id == i) <;> simp
  | some a =>
    cases ht : t.find? (fun op => op.id == i) with
    | none => simp
    | some b =>
      have ha := lookup_mem (s := s) (i := i) hs
      have hb := lookup_mem (s := t) (i := i) ht
      simp [h a ha.1 b hb.1 (by rw [ha.2, hb.2])]

/-- **The merge commutes** at the document level: two replicas that have
received the same operations read the same document whichever order they
merged in. With `docOrder_merge_self` and `merge_assoc`, this is the grow-only
set's join laws, at the document level. -/
theorem docOrder_merge_comm {n : Nat} {s t : OpSet} (h : Agree s t) :
    docOrder n (merge s t) = docOrder n (merge t s) := by
  have hlk := lookup_merge_comm h
  have ho : originsOf n (merge s t) = originsOf n (merge t s) := by
    simp only [originsOf]
    congr 1
    exact List.map_congr_left (fun i _ => by simp only [originOf, hlk i])
  have hsd : sidesOf n (merge s t) = sidesOf n (merge t s) := by
    simp only [sidesOf]
    congr 1
    exact List.map_congr_left (fun i _ => by simp only [sideOf, hlk i])
  simp [docOrder, ho, hsd]

/-- **The merge is idempotent** at the document level: re-merging what a
replica already has changes nothing. -/
theorem docOrder_merge_self {n : Nat} (s : OpSet) :
    docOrder n (merge s s) = docOrder n s := by
  have hlk : ∀ i, lookup (merge s s) i = lookup s i := by
    intro i
    simp only [merge, lookup, List.find?_append]
    cases hs : s.find? (fun op => op.id == i) <;> simp
  have ho : originsOf n (merge s s) = originsOf n s := by
    simp only [originsOf]
    congr 1
    exact List.map_congr_left (fun i _ => by simp only [originOf, hlk i])
  have hsd : sidesOf n (merge s s) = sidesOf n s := by
    simp only [sidesOf]
    congr 1
    exact List.map_congr_left (fun i _ => by simp only [sideOf, hlk i])
  simp [docOrder, ho, hsd]

/-! ## §9. The chain rule, and the general non-interleaving theorem

**The chain rule is Fugue's insert path, at this scale.** A replica typing an
uninterrupted run does not anchor every keystroke to the same place: the first
keystroke lands at the insertion point it chose, and every later one hangs off
*the character it just typed* — left if it is typing backwards (each new
character before the last), right if forwards. So a run is a chain of
descendants, and that is the whole reason the runs of two replicas cannot
interleave: a rival's run hangs off a different node, and a sibling contest
between whole subtrees cannot reach inside either one.

`Concurrent` below says what "concurrent" means operationally, and says it as
hypotheses that are *checkable of a generated state* rather than as an
assumption about the tree shape: distinct replicas mint distinct ids, the
common ancestor predates both runs, and — the load-bearing one — **neither
replica's operations can name an element it never received**. -/

/-- **A run, generated by the chain rule.** `runOps o b₀ b ids` is the
operation list of one uninterrupted run typed in the order `ids`: the first
keystroke origins at the insertion point `(o, b₀)` the replica chose in the
document it could see, and each later keystroke origins at its predecessor on
the typing side `b` (`false` = each new character goes *before* the last —
the back-to-front typing that is RGA's worst case; `true` = forward typing). -/
def runOps (o : Int) (b₀ b : Bool) : List Nat → OpSet
  | [] => []
  | i :: is => ⟨i, o, b₀⟩ :: runOps (i : Int) b b is

/-- **The run as its author reads it.** Typed forwards, the document order is
the typing order; typed backwards, each new character precedes the last, so
the document order is the reverse. -/
def runDoc (b : Bool) (ids : List Nat) : List Nat :=
  if b then ids else ids.reverse

@[simp] theorem mem_runDoc {b : Bool} {ids : List Nat} {x : Nat} :
    x ∈ runDoc b ids ↔ x ∈ ids := by
  cases b <;> simp [runDoc]

theorem runOps_id_mem {b : Bool} : ∀ (ids : List Nat) (o : Int) (b₀ : Bool)
    (op : InsOp), op ∈ runOps o b₀ b ids → op.id ∈ ids := by
  intro ids
  induction ids with
  | nil => intro o b₀ op h; simp [runOps] at h
  | cons i is ih =>
    intro o b₀ op h
    rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem i (ih (i : Int) b op h')

/-- Every origin a run mentions is its insertion point or one of its own
elements — the run anchors nowhere else, which is what makes it possible to
say that a *concurrent* run anchors nowhere inside this one. -/
theorem runOps_origin_mem {b : Bool} : ∀ (ids : List Nat) (o : Int) (b₀ : Bool)
    (op : InsOp), op ∈ runOps o b₀ b ids →
      op.origin = o ∨ ∃ k ∈ ids, op.origin = (k : Int) := by
  intro ids
  induction ids with
  | nil => intro o b₀ op h; simp [runOps] at h
  | cons i is ih =>
    intro o b₀ op h
    rcases List.mem_cons.mp h with rfl | h'
    · exact .inl rfl
    · rcases ih (i : Int) b op h' with hEq | ⟨k, hk, hEq⟩
      · exact .inr ⟨i, List.mem_cons_self, hEq⟩
      · exact .inr ⟨k, List.mem_cons_of_mem i hk, hEq⟩

/-- The only element that can origin at a run's head is the run's own next
keystroke — because the common ancestor predates the run, the concurrent
replica never received it, and the run itself is a chain. This is the whole
concurrency argument, and it is where `Concurrent`'s hypotheses are spent. -/
private theorem run_origin_at_head {b : Bool} {rest : List Nat}
    {i : Nat} {o : Int} {b₀ : Bool} {pre post : OpSet}
    (hnd : (i :: rest).Nodup)
    (hpt : ∀ j ∈ i :: rest, o ≠ (j : Int))
    (hpre : ∀ op ∈ pre, ∀ j ∈ i :: rest, op.origin ≠ (j : Int))
    (hpost : ∀ op ∈ post, ∀ j ∈ i :: rest, op.origin ≠ (j : Int))
    {j : Nat}
    (hj : originOf (pre ++ (runOps o b₀ b (i :: rest) ++ post)) j = (i : Int)) :
    (∃ rest', rest = j :: rest')
      ∧ sideOf (pre ++ (runOps o b₀ b (i :: rest) ++ post)) j = b := by
  have hnotroot : ((i : Int)) ≠ -1 := by omega
  cases hlk : lookup (pre ++ (runOps o b₀ b (i :: rest) ++ post)) j with
  | none => rw [originOf, hlk] at hj; exact absurd hj.symm hnotroot
  | some op =>
    obtain ⟨hmem, hid⟩ := lookup_mem hlk
    have horg : op.origin = (i : Int) := by rw [originOf, hlk] at hj; exact hj
    have hin : op ∈ runOps o b₀ b (i :: rest) := by
      rcases List.mem_append.mp hmem with h1 | h1
      · exact absurd horg (hpre op h1 i List.mem_cons_self)
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact h2
        · exact absurd horg (hpost op h2 i List.mem_cons_self)
    have hkey : (∃ rest', rest = op.id :: rest') ∧ op.side = b := by
      rcases List.mem_cons.mp hin with rfl | h'
      · exact absurd horg (hpt i List.mem_cons_self)
      · cases rest with
        | nil => simp [runOps] at h'
        | cons c rest'' =>
          rcases List.mem_cons.mp h' with rfl | h''
          · exact ⟨⟨rest'', rfl⟩, rfl⟩
          · exfalso
            rcases runOps_origin_mem rest'' (c : Int) b op h'' with hEq | ⟨k, hk, hEq⟩
            · rw [horg] at hEq
              exact (List.nodup_cons.mp hnd).1 (by
                have : i = c := by omega
                exact this ▸ List.mem_cons_self)
            · rw [horg] at hEq
              exact (List.nodup_cons.mp hnd).1 (by
                have : i = k := by omega
                exact this ▸ List.mem_cons_of_mem c hk)
    refine ⟨hid ▸ hkey.1, ?_⟩
    rw [sideOf, hlk]
    exact hkey.2

/-- The run's second keystroke really is governed by the chain op — the
positive half of `run_origin_at_head`, and where id freshness is spent (an
ancestor op reusing the id would shadow the run's own). -/
private theorem run_lookup_succ {b : Bool} {rest' : List Nat} {i c : Nat}
    {o : Int} {b₀ : Bool} {pre post : OpSet}
    (hnd : (i :: c :: rest').Nodup)
    (hpid : ∀ op ∈ pre, op.id ∉ (i :: c :: rest')) :
    lookup (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) c
      = some ⟨c, (i : Int), b⟩ := by
  have hic : i ≠ c := (List.nodup_cons.mp hnd).1 ∘ (· ▸ List.mem_cons_self)
  rw [lookup_append_of_left_miss
    (fun op hop => fun hEq => hpid op hop (hEq ▸ List.mem_cons_of_mem i List.mem_cons_self))]
  show lookup ((⟨i, o, b₀⟩ :: runOps (i : Int) b b (c :: rest')) ++ post) c = _
  rw [List.cons_append, lookup_cons_miss (by exact hic)]
  show lookup ((⟨c, (i : Int), b⟩ :: runOps (c : Int) b b rest') ++ post) c = _
  rw [List.cons_append]
  exact lookup_cons_hit

/-- **A run generated by the chain rule is a `Clan` of the merged state.**
Every hypothesis is about the *operations* — nobody assumes the tree shape;
the shape is derived. `Clan` then feeds §5's `run_contiguous`. -/
private theorem clan_of_runOps {n : Nat} {b : Bool} :
    ∀ (rest : List Nat) (i : Nat) (o : Int) (b₀ : Bool) (pre post : OpSet),
      (i :: rest).Nodup →
      (∀ j ∈ i :: rest, j < n) →
      (∀ j ∈ i :: rest, o ≠ (j : Int)) →
      (∀ op ∈ pre, op.id ∉ (i :: rest)) →
      (∀ op ∈ pre, ∀ j ∈ i :: rest, op.origin ≠ (j : Int)) →
      (∀ op ∈ post, ∀ j ∈ i :: rest, op.origin ≠ (j : Int)) →
      Clan (originsOf n (pre ++ (runOps o b₀ b (i :: rest) ++ post)))
        (sidesOf n (pre ++ (runOps o b₀ b (i :: rest) ++ post)))
        i (runDoc b (i :: rest)) := by
  intro rest
  induction rest with
  | nil =>
    intro i o b₀ pre post hnd hsp hpt hpid hpre hpost
    have hempty : ∀ β : Bool,
        childrenF (originsOf n (pre ++ (runOps o b₀ b [i] ++ post)))
          (sidesOf n (pre ++ (runOps o b₀ b [i] ++ post))) β (i : Int) = [] := by
      intro β
      rw [childrenF_of_ops]
      refine filter_range_eq_nil (fun j _ => ?_)
      have hne : originOf (pre ++ (runOps o b₀ b [i] ++ post)) j ≠ (i : Int) := by
        intro hEq
        obtain ⟨⟨rest', hrest'⟩, -⟩ := run_origin_at_head hnd hpt hpre hpost hEq
        exact absurd hrest' (by simp)
      simp [hne]
    have : runDoc b [i] = [i] := by cases b <;> simp [runDoc]
    rw [this]
    exact .leaf (hempty false) (hempty true)
  | cons c rest' ih =>
    intro i o b₀ pre post hnd hsp hpt hpid hpre hpost
    have hnd' : (c :: rest').Nodup := (List.nodup_cons.mp hnd).2
    have hic : i ≠ c := (List.nodup_cons.mp hnd).1 ∘ (· ▸ List.mem_cons_self)
    -- the merged state, split two ways: this run's head belongs to the prefix
    -- of the tail's own decomposition
    have hset : pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)
        = (pre ++ [⟨i, o, b₀⟩]) ++ (runOps (i : Int) b b (c :: rest') ++ post) := by
      show pre ++ ((⟨i, o, b₀⟩ :: runOps (i : Int) b b (c :: rest')) ++ post) = _
      simp [List.append_assoc]
    have hlkc := run_lookup_succ (b := b) (o := o) (b₀ := b₀) (post := post) hnd hpid
    have horgc : originOf (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) c
        = (i : Int) := by rw [originOf, hlkc]; rfl
    have hsidec : sideOf (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) c = b := by
      rw [sideOf, hlkc]; rfl
    -- children of the head: exactly the next keystroke, on the typing side
    have hchild : ∀ β : Bool,
        childrenF (originsOf n (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)))
          (sidesOf n (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)))
          β (i : Int) = if β = b then [c] else [] := by
      intro β
      rw [childrenF_of_ops]
      by_cases hβ : β = b
      · rw [if_pos hβ, hβ]
        refine filter_range_eq_singleton (by simp [horgc, hsidec]) n
          (hsp c (List.mem_cons_of_mem i List.mem_cons_self)) (fun j _ hpj => ?_)
        have hEq : originOf (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) j
            = (i : Int) := by
          have := (Bool.and_eq_true _ _).mp hpj
          simpa using this.1
        obtain ⟨⟨rest'', hrest''⟩, -⟩ := run_origin_at_head hnd hpt hpre hpost hEq
        exact (List.cons.injEq .. ▸ hrest'').1.symm
      · rw [if_neg hβ]
        refine filter_range_eq_nil (fun j _ => ?_)
        cases hpj : (originOf (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) j
            == (i : Int) && sideOf (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) j == β) with
        | false => rfl
        | true =>
          exfalso
          have hpair := (Bool.and_eq_true _ _).mp hpj
          have hEq : originOf (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) j
              = (i : Int) := by simpa using hpair.1
          have hsd : sideOf (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)) j = β := by
            simpa using hpair.2
          obtain ⟨-, hb⟩ := run_origin_at_head hnd hpt hpre hpost hEq
          exact hβ (by rw [← hsd, hb])
    -- the tail is a run in its own right, with this run's head in its prefix
    have htail : Clan (originsOf n (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)))
        (sidesOf n (pre ++ (runOps o b₀ b (i :: c :: rest') ++ post)))
        c (runDoc b (c :: rest')) := by
      rw [hset]
      refine ih c (i : Int) b (pre ++ [⟨i, o, b₀⟩]) post hnd'
        (fun j hj => hsp j (List.mem_cons_of_mem i hj))
        (fun j hj => by
          have : i ≠ j := fun hEq => (List.nodup_cons.mp hnd).1 (hEq ▸ hj)
          omega)
        (fun op hop => ?_) (fun op hop => ?_) (fun op hop => ?_)
      · rcases List.mem_append.mp hop with h1 | h1
        · exact fun hj => hpid op h1 (List.mem_cons_of_mem i hj)
        · rw [List.mem_singleton.mp h1]
          exact (List.nodup_cons.mp hnd).1
      · rcases List.mem_append.mp hop with h1 | h1
        · exact fun j hj => hpre op h1 j (List.mem_cons_of_mem i hj)
        · rw [List.mem_singleton.mp h1]
          exact fun j hj => hpt j (List.mem_cons_of_mem i hj)
      · exact fun j hj => hpost op hop j (List.mem_cons_of_mem i hj)
    cases b with
    | false =>
      have hrd : runDoc false (i :: c :: rest') = runDoc false (c :: rest') ++ [i] := by
        simp [runDoc]
      rw [hrd]
      exact .left (by simpa using hchild false) (by simpa using hchild true) htail
    | true =>
      have hrd : runDoc true (i :: c :: rest') = i :: runDoc true (c :: rest') := by
        simp [runDoc]
      rw [hrd]
      exact .right (by simpa using hchild false) (by simpa using hchild true) htail

/-- **Two concurrent editing sessions over a common ancestor.** Every field is
a fact about the *operations*, checkable of a generated history:

* the ids of a run are distinct and inside the id space;
* the two replicas mint disjoint ids, and the common ancestor uses neither
  replica's (`freshX`/`freshY`);
* the ancestor predates both runs, so none of its operations can name a run
  element (`ancestorBlindX`/`ancestorBlindY`);
* a session's insertion point is not one of its own new elements
  (`pointX`/`pointY`) — it is a place in the document it started from;
* and the one that *is* concurrency: **a session's insertion point is not one
  of the other session's elements** (`concurrentX`/`concurrentY`) — a replica
  cannot anchor to an element it has never received. Drop this and the two
  sessions are sequential, one having seen the other, and nothing below
  should hold. -/
structure Concurrent (n : Nat) (base : OpSet) (oX : Int) (b₀X bX : Bool)
    (idsX : List Nat) (oY : Int) (b₀Y bY : Bool) (idsY : List Nat) : Prop where
  /-- X's keystrokes have distinct ids. -/
  nodupX : idsX.Nodup
  /-- Y's keystrokes have distinct ids. -/
  nodupY : idsY.Nodup
  /-- X's ids lie in the id space. -/
  spaceX : ∀ i ∈ idsX, i < n
  /-- Y's ids lie in the id space. -/
  spaceY : ∀ i ∈ idsY, i < n
  /-- The two replicas mint disjoint ids. -/
  disjoint : ∀ i ∈ idsX, i ∉ idsY
  /-- The ancestor does not already use one of X's new ids. -/
  freshX : ∀ op ∈ base, op.id ∉ idsX
  /-- The ancestor does not already use one of Y's new ids. -/
  freshY : ∀ op ∈ base, op.id ∉ idsY
  /-- The ancestor predates X's run: none of its ops anchors to one. -/
  ancestorBlindX : ∀ op ∈ base, ∀ i ∈ idsX, op.origin ≠ (i : Int)
  /-- The ancestor predates Y's run: none of its ops anchors to one. -/
  ancestorBlindY : ∀ op ∈ base, ∀ i ∈ idsY, op.origin ≠ (i : Int)
  /-- X's insertion point is not inside X's own run. -/
  pointX : ∀ i ∈ idsX, oX ≠ (i : Int)
  /-- Y's insertion point is not inside Y's own run. -/
  pointY : ∀ i ∈ idsY, oY ≠ (i : Int)
  /-- **Concurrency**: X never saw Y's elements, so it cannot anchor to one. -/
  concurrentX : ∀ i ∈ idsY, oX ≠ (i : Int)
  /-- **Concurrency**: Y never saw X's elements, so it cannot anchor to one. -/
  concurrentY : ∀ i ∈ idsX, oY ≠ (i : Int)

/-- The merged history: the common ancestor, joined with each replica's run.
`merge` is the grow-only union of §8, so this is the state both replicas reach
once they exchange operations (`docOrder_merge_comm`: in either order). -/
def mergedRuns (base : OpSet) (oX : Int) (b₀X bX : Bool) (idsX : List Nat)
    (oY : Int) (b₀Y bY : Bool) (idsY : List Nat) : OpSet :=
  merge (merge base (runOps oX b₀X bX idsX)) (runOps oY b₀Y bY idsY)

/-- Ids are minted above their origin's (creation order) — then the
materialized forest is well-formed with rank = index, and no separate rank
argument is needed. -/
def CreationOrdered (s : OpSet) : Prop :=
  ∀ op ∈ s, -1 ≤ op.origin ∧ op.origin < (op.id : Int)

theorem wfk_of_creation_ordered {n : Nat} {s : OpSet} (h : CreationOrdered s) :
    WFK (fun i => i) (originsOf n s) := by
  refine wfk_of_index_ordered (fun i hi => ?_)
  rw [size_originsOf] at hi
  rw [anchorAt_originsOf hi]
  cases hlk : lookup s i with
  | none =>
    have hne : originOf s i = -1 := by simp [originOf, hlk]
    rw [hne]
    exact ⟨by omega, by omega⟩
  | some op =>
    obtain ⟨hmem, hid⟩ := lookup_mem hlk
    obtain ⟨h1, h2⟩ := h op hmem
    rw [originOf, hlk]
    exact ⟨h1, by rw [← hid]; exact h2⟩

/-- **The general theorem: concurrent runs never interleave.** For *any* two
runs generated by the chain rule from a common ancestor — any lengths, any
insertion points, either typing direction, any number of other elements in the
ancestor — the merged Fugue document keeps each run in one contiguous block,
in exactly the order its author typed it (`<:+:`); each run is `clustered`;
and no element of the *other run* falls between two elements of a run
(`Splits`, Kleppmann et al.'s clause 1(d) for a single intruding element).
Nothing outside a run can, in fact, and `not_splits_of_infix` applied to the
same infix says so for every foreign element; the rival's is what the anomaly
is about, so that is what this statement names.

The concrete pair of §2 sampled this statement at two runs of two elements;
here it is for all of them. The only hypotheses are `Concurrent` — facts about
the *operations* — and the well-formedness `SeqKernel`'s Rust encoder already
establishes (`wfk_of_creation_ordered` discharges it whenever ids are minted
in creation order). -/
theorem fugue_runs_never_interleave {r : Nat → Nat} {n : Nat} {base : OpSet}
    {oX oY : Int} {b₀X bX b₀Y bY : Bool} {iX iY : Nat} {restX restY : List Nat}
    {S : OpSet}
    (hS : S = mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY))
    (hc : Concurrent n base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY))
    (hwf : WFK r (originsOf n S)) :
    runDoc bX (iX :: restX) <:+: docOrder n S
    ∧ runDoc bY (iY :: restY) <:+: docOrder n S
    ∧ clustered (runDoc bX (iX :: restX)) (docOrder n S) = true
    ∧ clustered (runDoc bY (iY :: restY)) (docOrder n S) = true
    ∧ (∀ y ∈ iY :: restY, ¬ Splits (docOrder n S) (runDoc bX (iX :: restX)) y)
    ∧ (∀ x ∈ iX :: restX, ¬ Splits (docOrder n S) (runDoc bY (iY :: restY)) x) := by
  subst hS
  have hXblind : ∀ op ∈ runOps oY b₀Y bY (iY :: restY), ∀ j ∈ iX :: restX,
      op.origin ≠ (j : Int) := by
    intro op hop j hj
    rcases runOps_origin_mem (b := bY) (iY :: restY) oY b₀Y op hop with hEq | ⟨k, hk, hEq⟩
    · rw [hEq]; exact hc.concurrentY j hj
    · rw [hEq]
      intro hcon
      have hkj : j = k := by omega
      exact hc.disjoint j hj (hkj ▸ hk)
  have hYblind : ∀ op ∈ base ++ runOps oX b₀X bX (iX :: restX), ∀ j ∈ iY :: restY,
      op.origin ≠ (j : Int) := by
    intro op hop j hj
    rcases List.mem_append.mp hop with h1 | h1
    · exact hc.ancestorBlindY op h1 j hj
    · rcases runOps_origin_mem (b := bX) (iX :: restX) oX b₀X op h1 with hEq | ⟨k, hk, hEq⟩
      · rw [hEq]; exact hc.concurrentX j hj
      · rw [hEq]
        intro hcon
        have hkj : k = j := by omega
        exact hc.disjoint k hk (hkj ▸ hj)
  have hYfresh : ∀ op ∈ base ++ runOps oX b₀X bX (iX :: restX), op.id ∉ iY :: restY := by
    intro op hop
    rcases List.mem_append.mp hop with h1 | h1
    · exact hc.freshY op h1
    · exact hc.disjoint op.id (runOps_id_mem (b := bX) (iX :: restX) oX b₀X op h1)
  have hSX : mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY)
      = base ++ (runOps oX b₀X bX (iX :: restX) ++ runOps oY b₀Y bY (iY :: restY)) := by
    simp [mergedRuns, merge, List.append_assoc]
  have hSY : mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY)
      = (base ++ runOps oX b₀X bX (iX :: restX)) ++ (runOps oY b₀Y bY (iY :: restY) ++ []) := by
    simp [mergedRuns, merge]
  have hclanX : Clan
      (originsOf n (mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY)))
      (sidesOf n (mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY)))
      iX (runDoc bX (iX :: restX)) := by
    rw [hSX]
    exact clan_of_runOps restX iX oX b₀X base (runOps oY b₀Y bY (iY :: restY))
      hc.nodupX hc.spaceX hc.pointX hc.freshX hc.ancestorBlindX hXblind
  have hclanY : Clan
      (originsOf n (mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY)))
      (sidesOf n (mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY)))
      iY (runDoc bY (iY :: restY)) := by
    rw [hSY]
    exact clan_of_runOps restY iY oY b₀Y (base ++ runOps oX b₀X bX (iX :: restX)) []
      hc.nodupY hc.spaceY hc.pointY hYfresh hYblind (by simp)
  have hnd : (docOrder n
      (mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY))).Nodup :=
    fugueOrder_nodup (side := sidesOf n _) hwf.grounded
  have hinfX := run_contiguous_of_wfk hwf
    (by rw [size_originsOf]; exact hc.spaceX iX List.mem_cons_self) hclanX
  have hinfY := run_contiguous_of_wfk hwf
    (by rw [size_originsOf]; exact hc.spaceY iY List.mem_cons_self) hclanY
  refine ⟨hinfX, hinfY, clustered_of_infix_of_nodup hinfX hnd,
    clustered_of_infix_of_nodup hinfY hnd, ?_, ?_⟩
  · intro y hy
    exact not_splits_of_infix hinfX hnd
      (fun hmem => hc.disjoint y (mem_runDoc.mp hmem) hy)
  · intro x hx
    exact not_splits_of_infix hinfY hnd
      (fun hmem => hc.disjoint x hx (mem_runDoc.mp hmem))

/-- `fugue_runs_never_interleave` with the well-formedness discharged from the
model itself: ids minted in creation order (the dense-index discipline of §2)
need no separate rank. -/
theorem fugue_runs_never_interleave_creation_ordered {n : Nat} {base : OpSet}
    {oX oY : Int} {b₀X bX b₀Y bY : Bool} {iX iY : Nat} {restX restY : List Nat}
    {S : OpSet}
    (hS : S = mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY))
    (hc : Concurrent n base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY))
    (hco : CreationOrdered S) :
    runDoc bX (iX :: restX) <:+: docOrder n S
    ∧ runDoc bY (iY :: restY) <:+: docOrder n S
    ∧ clustered (runDoc bX (iX :: restX)) (docOrder n S) = true
    ∧ clustered (runDoc bY (iY :: restY)) (docOrder n S) = true
    ∧ (∀ y ∈ iY :: restY, ¬ Splits (docOrder n S) (runDoc bX (iX :: restX)) y)
    ∧ (∀ x ∈ iX :: restX, ¬ Splits (docOrder n S) (runDoc bY (iY :: restY)) x) :=
  fugue_runs_never_interleave hS hc (wfk_of_creation_ordered hco)

/-- **Clause 1(d) for a generated history, literally.** Kleppmann et al.'s
revised specification (PaPoC'19 §2.1) demands of two concurrent insertion sets
that "either all X insertions appear before all Y insertions in the document,
or vice versa, but they are never interleaved". That is this disjunction, and
under the chain rule the Fugue order satisfies it. -/
theorem fugue_runs_in_one_order {r : Nat → Nat} {n : Nat} {base : OpSet}
    {oX oY : Int} {b₀X bX b₀Y bY : Bool} {iX iY : Nat} {restX restY : List Nat}
    {S : OpSet}
    (hS : S = mergedRuns base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY))
    (hc : Concurrent n base oX b₀X bX (iX :: restX) oY b₀Y bY (iY :: restY))
    (hwf : WFK r (originsOf n S)) :
    (∀ a ∈ iX :: restX, ∀ b ∈ iY :: restY, [a, b] <+ docOrder n S)
    ∨ (∀ b ∈ iY :: restY, ∀ a ∈ iX :: restX, [b, a] <+ docOrder n S) := by
  obtain ⟨hinfX, hinfY, -, -, -, -⟩ := fugue_runs_never_interleave hS hc hwf
  have hnd : (docOrder n S).Nodup :=
    fugueOrder_nodup (side := sidesOf n S) hwf.grounded
  rcases runs_ordered_of_infix (a₀ := iX) (b₀ := iY) hinfX hinfY hnd
    (fun a ha hb => hc.disjoint a (mem_runDoc.mp ha) (mem_runDoc.mp hb))
    (mem_runDoc.mpr List.mem_cons_self) (mem_runDoc.mpr List.mem_cons_self) with h | h
  · exact .inl (fun a ha b hb => h a (mem_runDoc.mpr ha) b (mem_runDoc.mpr hb))
  · exact .inr (fun b hb a ha => h b (mem_runDoc.mpr hb) a (mem_runDoc.mpr ha))

/-! ## §10. The RGA contrast, in the same model

The same editing intent, encoded the way RGA encodes it. The difference is in
the *insert path*, and it is the whole design difference: RGA anchors an
insertion to the character that **precedes** it in the document, so a run
typed back-to-front anchors every keystroke to the same element — a family of
siblings. Fugue anchors to the character the user **just typed**, with a side,
so the same run is a chain of descendants. `fanOps` is the first path;
`runOps` above is the second; `rgaDoc` and `docOrder` read the results.

What §2 computed on four elements is proved here for any two id sets that
straddle: whenever one replica has an id below and an id above one of the
other's — which is exactly what interleaved logical clocks produce — the
merged RGA document reads X, then Y, then X again. That is `Splits`, the same
predicate the Fugue theorem denies. -/

/-- **RGA's encoding of a back-to-front run**: every keystroke anchored to the
same element (the character before the insertion point), because that element
is the predecessor of each new character at the moment it is typed. The side
word is never read by `linearizeK`; it is `false` here only to have a value. -/
def fanOps (o : Int) : List Nat → OpSet
  | [] => []
  | i :: is => ⟨i, o, false⟩ :: fanOps o is

theorem fanOps_origin : ∀ (ids : List Nat) (o : Int) (op : InsOp),
    op ∈ fanOps o ids → op.origin = o := by
  intro ids
  induction ids with
  | nil => intro o op h; simp [fanOps] at h
  | cons i is ih =>
    intro o op h
    rcases List.mem_cons.mp h with rfl | h'
    · rfl
    · exact ih o op h'

theorem originOf_of_all_root {s : OpSet} (h : ∀ op ∈ s, op.origin = -1) (i : Nat) :
    originOf s i = -1 := by
  cases hlk : lookup s i with
  | none => simp [originOf, hlk]
  | some op => rw [originOf, hlk]; exact h op (lookup_mem hlk).1

private theorem emitK_flat_nil {A : Array Int}
    (h : ∀ i, i < A.size → anchorAt A i = -1) (c : Nat) :
    ∀ fuel, emitK A fuel (c : Int) = [] := by
  intro fuel
  have hkids : childrenK A (c : Int) = [] := by
    refine List.filter_eq_nil_iff.mpr (fun a ha => ?_)
    have hlt : a < A.size := List.mem_range.mp (List.mem_reverse.mp ha)
    simp [h a hlt]
  cases fuel with
  | zero => rfl
  | succ fuel => simp [emitK, hkids]

private theorem flatMap_singleton_of {f : Nat → List Nat} :
    ∀ {l : List Nat}, (∀ c ∈ l, f c = [c]) → l.flatMap f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    rw [List.flatMap_cons, h a List.mem_cons_self,
      ih (fun c hc => h c (List.mem_cons_of_mem a hc))]
    rfl

/-- **A flat forest reads in descending id order.** When every element is
anchored at the root — the paper's §3 worst case, all characters anchored to
the head of the document — RGA's document is pure timestamp arbitration and
nothing else. -/
theorem rga_flat_doc {n : Nat} {s : OpSet} (h : ∀ i, i < n → originOf s i = -1) :
    rgaDoc n s = (List.range n).reverse := by
  have hA : ∀ i, i < (originsOf n s).size → anchorAt (originsOf n s) i = -1 := by
    intro i hi
    rw [size_originsOf] at hi
    rw [anchorAt_originsOf hi]
    exact h i hi
  have hemit : emitAll (originsOf n s) = (List.range n).reverse := by
    unfold emitAll
    rw [size_originsOf]
    cases n with
    | zero => simp [emitK]
    | succ m =>
      have hchild : childrenK (originsOf (m + 1) s) (-1) = (List.range (m + 1)).reverse := by
        unfold childrenK
        rw [size_originsOf]
        refine List.filter_eq_self.mpr (fun a ha => ?_)
        have hlt : a < m + 1 := List.mem_range.mp (List.mem_reverse.mp ha)
        simp [anchorAt_originsOf hlt, h a hlt]
      rw [emitK, hchild]
      exact flatMap_singleton_of (fun c _ => by rw [emitK_flat_nil hA c])
  simp only [rgaDoc, linearizeK, List.toList_toArray, hemit]
  exact List.filter_eq_self.mpr (fun a _ => by simp)

private theorem pair_sublist_range {a y : Nat} :
    ∀ n, a < y → y < n → [a, y] <+ List.range n := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ m ih =>
    intro hay hyn
    rw [List.range_succ]
    by_cases hy : y = m
    · subst hy
      have h1 : ([a] : List Nat) <+ List.range y :=
        List.singleton_sublist.mpr (List.mem_range.mpr hay)
      exact h1.append (List.Sublist.refl [y])
    · exact (ih hay (by omega)).trans (List.sublist_append_left _ _)

private theorem triple_sublist_range {a y b : Nat} :
    ∀ n, a < y → y < b → b < n → [a, y, b] <+ List.range n := by
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ m ih =>
    intro hay hyb hbn
    rw [List.range_succ]
    by_cases hb : b = m
    · subst hb
      exact (pair_sublist_range b hay hyb).append (List.Sublist.refl [b])
    · exact (ih hay hyb (by omega)).trans (List.sublist_append_left _ _)

/-- ⚠ **RGA interleaves — generally, not on a witness.** In a flat forest,
any three ids `x₁ < y < x₂` appear in the merged document as `x₂`, then `y`,
then `x₁`. Read with `x₁, x₂` one replica's and `y` the other's: a foreign
character lands strictly inside the run. -/
theorem rga_flat_interleaves {n : Nat} {s : OpSet} {x₁ y x₂ : Nat}
    (hflat : ∀ i, i < n → originOf s i = -1)
    (h1 : x₁ < y) (h2 : y < x₂) (h3 : x₂ < n) :
    [x₂, y, x₁] <+ rgaDoc n s := by
  rw [rga_flat_doc hflat]
  simpa using (triple_sublist_range n h1 h2 h3).reverse

/-- ⚠ **The RGA anomaly, in §7's vocabulary and generally.** Two replicas each
type a run at the head of the shared document, RGA-style (`fanOps`); if their
ids straddle — X has one below and one above an id of Y's, which is what
concurrent clocks give — then some element of Y sits strictly inside X's run:
`X`'s run is `Splits`. This is the exact predicate
`fugue_runs_never_interleave` denies for the same intent under the chain
rule. -/
theorem rga_head_runs_interleave_general {n : Nat} {idsX idsY : List Nat}
    {x₁ y x₂ : Nat} (hx₁ : x₁ ∈ idsX) (hx₂ : x₂ ∈ idsX) (hy : y ∈ idsY)
    (h1 : x₁ < y) (h2 : y < x₂) (h3 : x₂ < n) :
    ∃ z ∈ idsY, Splits (rgaDoc n (merge (fanOps (-1) idsX) (fanOps (-1) idsY))) idsX z := by
  have hflat : ∀ i, i < n →
      originOf (merge (fanOps (-1) idsX) (fanOps (-1) idsY)) i = -1 := by
    intro i _
    refine originOf_of_all_root (fun op hop => ?_) i
    rcases List.mem_append.mp hop with h | h
    · exact fanOps_origin idsX (-1) op h
    · exact fanOps_origin idsY (-1) op h
  exact ⟨y, hy, x₂, hx₂, x₁, hx₁, rga_flat_interleaves hflat h1 h2 h3⟩

/-! ## §11. The §2 witness, re-derived from the operations

Guard against a general theorem nobody can instantiate: the head-insert
scenario of §2 is *generated* here by the chain rule, `Concurrent` is
discharged by `decide` on it, and the arrays §2 wrote by hand fall out of the
model — so `fugue_head_runs_stay_contiguous` is now a corollary of the general
theorem rather than a separate computation. -/

/-- Replica X's operations: type `0`, then `2` before it. The first keystroke
lands right of the root sentinel; the second is a **left child of the first**,
because it was typed before it. -/
def headOpsX : OpSet := runOps (-1) true false [0, 2]

/-- Replica Y's operations, concurrently: `1`, then `3` before it. -/
def headOpsY : OpSet := runOps (-1) true false [1, 3]

/-- The merged history of the two concurrent sessions, over the empty
ancestor. -/
def headMerged : OpSet := mergedRuns [] (-1) true false [0, 2] (-1) true false [1, 3]

/-- **The generated history materializes to §2's hand-written arrays.** The
`headRunsOrigin`/`headRunsSide` of §2 are not an independent encoding of the
scenario — they are what the chain rule emits. -/
theorem headMerged_materializes :
    originsOf 4 headMerged = headRunsOrigin ∧ sidesOf 4 headMerged = headRunsSide := by
  constructor <;> decide

theorem headMerged_docOrder :
    docOrder 4 headMerged = fugueOrder headRunsOrigin headRunsSide := by
  rw [docOrder, headMerged_materializes.1, headMerged_materializes.2]

/-- The scenario satisfies `Concurrent`: disjoint ids, an empty ancestor, and
neither session's insertion point is the other's element (both typed at the
root sentinel, having seen nothing of each other). -/
theorem headMerged_concurrent :
    Concurrent 4 [] (-1) true false [0, 2] (-1) true false [1, 3] := by
  constructor <;> decide

theorem headMerged_creation_ordered : CreationOrdered headMerged := by
  unfold CreationOrdered
  decide

/-- **§2's contrast, delivered by the general theorem.** Each run is a
contiguous block of the merged document, clustered, and neither replica's
characters fall inside the other's run — computed nowhere, derived from
`fugue_runs_never_interleave` applied to the generated history. -/
theorem head_runs_contiguous_by_the_operational_theorem :
    [2, 0] <:+: fugueOrder headRunsOrigin headRunsSide
    ∧ [3, 1] <:+: fugueOrder headRunsOrigin headRunsSide
    ∧ clustered [2, 0] (fugueOrder headRunsOrigin headRunsSide) = true
    ∧ clustered [3, 1] (fugueOrder headRunsOrigin headRunsSide) = true
    ∧ (∀ y ∈ [1, 3], ¬ Splits (fugueOrder headRunsOrigin headRunsSide) [2, 0] y)
    ∧ (∀ x ∈ [0, 2], ¬ Splits (fugueOrder headRunsOrigin headRunsSide) [3, 1] x) := by
  have h := fugue_runs_never_interleave_creation_ordered (n := 4) (base := [])
    (S := headMerged) rfl headMerged_concurrent headMerged_creation_ordered
  rw [headMerged_docOrder] at h
  have hX : runDoc false [0, 2] = [2, 0] := by decide
  have hY : runDoc false [1, 3] = [3, 1] := by decide
  rw [hX, hY] at h
  exact h

/-! ### The refusal has a witness on the other side

`¬ Splits` is only a claim if `Splits` can hold. It can: the *same* editing
intent, RGA-encoded (each keystroke anchored to its predecessor, so the run is
a fan), makes it true — and true by the general RGA theorem, not by a separate
computation. This is the §2 contrast with both halves now generated from
operations. -/

/-- The §2 head-insert intent under RGA's insert path: four keystrokes, all
anchored at the head. Materializes to §2's `#[-1, -1, -1, -1]`. -/
def headFan : OpSet := merge (fanOps (-1) [0, 2]) (fanOps (-1) [1, 3])

theorem headFan_materializes : originsOf 4 headFan = #[-1, -1, -1, -1] := by decide

/-- ⚠ The merged RGA document of the generated history: `[3, 2, 1, 0]`, the
two runs strictly alternated — `rga_head_runs_interleave` of §2, now read off
the operations rather than a hand-written array. -/
theorem headFan_rgaDoc : rgaDoc 4 headFan = [3, 2, 1, 0] := by decide

/-- ⚠ **The predicate the Fugue theorem denies is satisfiable**: under RGA's
encoding of the same intent, an element of Y's run does sit inside X's. From
`rga_head_runs_interleave_general`, so the general RGA statement is exercised
too. -/
theorem headFan_run_is_split : ∃ z ∈ [1, 3], Splits (rgaDoc 4 headFan) [0, 2] z :=
  rga_head_runs_interleave_general (n := 4) (idsX := [0, 2]) (idsY := [1, 3])
    (x₁ := 0) (y := 1) (x₂ := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-! ### The concurrency hypothesis is load-bearing

A hypothesis nobody can violate is decoration. This one can be violated, and
when it is the conclusion fails: a replica that has *received* the other's run
may anchor inside it, and then the run splits — as it must, because the second
user typed there on purpose. -/

/-- Replica X types `0`, then `1` before it. A second replica, **having seen
that run**, inserts `2` inside it (left of `0`, i.e. between `1` and `0`) —
which `Concurrent.concurrentY` forbids and which a real editor does all the
time. -/
def typedIntoRun : OpSet := merge (runOps (-1) true false [0, 1]) [⟨2, 0, false⟩]

/-- ⚠ **The run splits, exactly as it should.** X's run reads `[1, 0]` on its
author's screen and `1, 2, 0` in the merged document: `Splits` holds and the
run is not an infix. So `fugue_runs_never_interleave`'s concurrency hypothesis
is doing work — drop it and the theorem is false — and no contiguity is
claimed for a run somebody typed into. -/
theorem typed_into_run_splits :
    docOrder 3 typedIntoRun = [1, 2, 0]
    ∧ Splits (docOrder 3 typedIntoRun) (runDoc false [0, 1]) 2
    ∧ ¬ (runDoc false [0, 1] <:+: docOrder 3 typedIntoRun) := by
  have hdoc : docOrder 3 typedIntoRun = [1, 2, 0] := by decide
  have hsplit : Splits (docOrder 3 typedIntoRun) (runDoc false [0, 1]) 2 := by
    refine ⟨1, by decide, 0, by decide, ?_⟩
    rw [hdoc]
    exact List.Sublist.refl _
  refine ⟨hdoc, hsplit, fun hinf => ?_⟩
  exact not_splits_of_infix hinf (by rw [hdoc]; simp) (by decide) hsplit

/-! ### Past the sampled pair: three keystrokes each, over a non-empty ancestor

§2's contrast pair is two runs of two over an empty document, because that is
what a `decide` could be read off. The general theorem has no such limit; this
instance exercises it where the old witness could not go — a common ancestor
with an element in it, both sessions anchored to *that element*, runs of three,
typed forwards. -/

/-- The common ancestor both replicas start from: one element, `0`, at the
root sentinel. -/
def longBase : OpSet := [⟨0, -1, true⟩]

/-- X types `1`, `3`, `5` forwards after element `0`; Y concurrently types
`2`, `4`, `6` after the same element. Ids interleave, as concurrent clocks
give. -/
def longMerged : OpSet := mergedRuns longBase 0 true true [1, 3, 5] 0 true true [2, 4, 6]

theorem longMerged_concurrent :
    Concurrent 7 longBase 0 true true [1, 3, 5] 0 true true [2, 4, 6] := by
  constructor <;> decide

theorem longMerged_creation_ordered : CreationOrdered longMerged := by
  unfold CreationOrdered
  decide

/-- **The general theorem on runs of three over a non-empty ancestor**: both
runs contiguous, clustered, and neither session's characters inside the
other's run — none of it computed. -/
theorem long_runs_never_interleave :
    runDoc true [1, 3, 5] <:+: docOrder 7 longMerged
    ∧ runDoc true [2, 4, 6] <:+: docOrder 7 longMerged
    ∧ clustered (runDoc true [1, 3, 5]) (docOrder 7 longMerged) = true
    ∧ clustered (runDoc true [2, 4, 6]) (docOrder 7 longMerged) = true
    ∧ (∀ y ∈ [2, 4, 6], ¬ Splits (docOrder 7 longMerged) (runDoc true [1, 3, 5]) y)
    ∧ (∀ x ∈ [1, 3, 5], ¬ Splits (docOrder 7 longMerged) (runDoc true [2, 4, 6]) x) :=
  fugue_runs_never_interleave_creation_ordered rfl longMerged_concurrent
    longMerged_creation_ordered

theorem long_runs_in_one_order :
    (∀ a ∈ [1, 3, 5], ∀ b ∈ [2, 4, 6], [a, b] <+ docOrder 7 longMerged)
    ∨ (∀ b ∈ [2, 4, 6], ∀ a ∈ [1, 3, 5], [b, a] <+ docOrder 7 longMerged) :=
  fugue_runs_in_one_order rfl longMerged_concurrent
    (wfk_of_creation_ordered longMerged_creation_ordered)

/-- What that document actually reads: `0`, then X's run whole, then Y's run
whole. The sibling contest at element `0` decided which run comes first and
nothing else. -/
theorem long_docOrder : docOrder 7 longMerged = [0, 1, 3, 5, 2, 4, 6] := by decide

/-- ⚠ **The same intent, RGA-encoded, at length three.** RGA anchors each
keystroke to its predecessor character, so both runs are fans off element `0`
(`fanOps`) — and the merged document alternates them character by character.
Neither run is clustered. This is the contrast of §2 at a length the old
witness never reached, on the same editing intent as
`long_runs_never_interleave`. -/
theorem long_rga_interleaves :
    rgaDoc 7 (merge (merge longBase (fanOps 0 [1, 3, 5])) (fanOps 0 [2, 4, 6]))
        = [0, 6, 5, 4, 3, 2, 1]
    ∧ clustered [1, 3, 5]
        (rgaDoc 7 (merge (merge longBase (fanOps 0 [1, 3, 5])) (fanOps 0 [2, 4, 6])))
        = false
    ∧ clustered [2, 4, 6]
        (rgaDoc 7 (merge (merge longBase (fanOps 0 [1, 3, 5])) (fanOps 0 [2, 4, 6])))
        = false := by
  decide

end Uwueave.Fugue
