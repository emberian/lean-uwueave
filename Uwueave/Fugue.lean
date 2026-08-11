/-
# Uwueave.Fugue — a Fugue-style order decision, and the non-interleaving contrast

JOB 8 (GROKJOB.md). `Uwueave/Sequence.lean` proves the interleaving anomaly
(Kleppmann–Gomes–Mulligan–Beresford, PaPoC 2019) *against* the RGA order, and
`Uwueave/SeqKernel.lean` ships that order as the kernel's decision core with
no-interleaving as an explicit non-claim. This file builds the design that
targets exactly that anomaly — Fugue (Weidner–Kleppmann, "The Art of the
Fugue") — at this repo's miniature scale, and proves the contrast in both
directions on the same editing intent.

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

## Non-claims — the honest boundary

  * **Fugue's maximal-non-interleaving theorem (Weidner–Kleppmann) is NOT
    proved.** Their statement quantifies over concurrent editing histories;
    this file has no model of operations, concurrency, or insertion at all —
    only tree *states* and the order decision on them, exactly as
    `Sequence.lean` models RGA states and not RGA's insert path.
  * **The insertion algorithm is not formalized.** Real Fugue chooses each
    new node's (origin, side) from a (leftOrigin, rightOrigin) pair at insert
    time; that placement logic is what guarantees runs *are* single-child
    chains. Here the chains are hypotheses (`Clan`) or concrete witnesses,
    not consequences of an insert function.
  * **`run_contiguous`'s hypothesis is load-bearing and must be.** `Clan c l`
    says the run's subtree is exactly the run — nothing was ever inserted
    into its interior. A run somebody typed into SHOULD split; no contiguity
    is claimed (or wanted) for that case. What the theorem rules out is
    interleaving caused by *arbitration between runs*, which is the anomaly.
  * **Duplicate-freedom is not re-proved for the in-order walk.** SeqKernel's
    §7 rank argument (sibling-subtree disjointness) is side-blind and should
    transfer; that is undone work, not a theorem of this file. Same for the
    ancestor-precedes family and the tombstone output filter (not modeled
    here at all — `fugueOrder` has no deleted array).
  * **This is a pure order-theory module beside the kernel, not in it.** The
    export surface still has exactly one symbol (`uwueave_seq_kernel`), which
    still runs `linearizeK`. Adopting this order would mean: one more word
    array (side bits) in SEQ FORMAT, an in-order `emitK` twin, and in-order
    re-proofs of the §7/§8 theorems — an ordinary flag-day rebuild, listed
    here so the distance is measured, not hidden.

Groundedness, chains, and completeness machinery are `SeqKernel`'s own
(`ChainK`, `GroundedAnchors`, `WFK`, `chain_to_root`), imported and reused —
the side array is invisible to origin-edge descent, so not one of those
proofs is duplicated.
-/
import Uwueave.SeqKernel

namespace Uwueave.Fugue

open Uwueave.SeqKernel (anchorAt linearizeK ChainK GroundedAnchors BelowK WFK
  chain_to_root wfk_of_index_ordered)

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

end Uwueave.Fugue
