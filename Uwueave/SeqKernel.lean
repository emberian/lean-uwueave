/-
# Uwueave.SeqKernel — the executable sequence-CRDT kernel (RGA with tombstones).

THIS IS LEAN-AUTHORED SEMANTICS COMPILED TO C. The Rust crate does not
implement the linearization; it marshals bytes to `uwueave_seq_kernel` (the
`@[export]` below), which lake compiles to C alongside every other module
here, and `build.rs` links into the crate. Rust's remaining jobs are the
deliberately dumb ones: storage, hashing, tombstone flags, IO
(`rust/src/seq.rs`). `Uwueave/Sequence.lean` is the abstract model this kernel
executes: RGA-style anchored insertion, extended with the one thing the model
names as future work — tombstoned deletion.

## The contract — SEQ FORMAT v1

Input `ByteArray`, little-endian 64-bit words:

```
word 0            : n — element count
words 1 .. 1+n    : anchor[i] as i64   (-1 = root; 0 ≤ a < n = inserted after
                    element a; anything else is junk and the element is simply
                    never emitted — see "junk degradation" below)
words 1+n .. 1+2n : deleted[i] as u64  (0 = visible; any nonzero = tombstoned)
```

Elements arrive in **id-sorted dense index order**: the Rust side content-
addresses each element (`blake3(anchor ‖ contents)`, `rust/src/seq.rs`) and
sends index `i` for the `i`-th smallest id. The index order therefore IS the
sibling-arbitration order — the kernel never sees an id, only the order.

Output `ByteArray`:

```
word 0            : k — visible element count
words 1 .. 1+k    : the visible linearization, element indices as u64, in
                    document order
```

Semantics: depth-first from the root, children of each anchor visited in
**descending index order** — the RGA tie-break rule, "newest first", except
that here "newest" means *highest id*, which is pure arbitration and not
recency or intention (`Uwueave.Sequence.run_order_by_id` is exactly this
point). Tombstoned elements are excluded from the output but **not** from the
traversal: a deleted element keeps its position in the forest and its
descendants keep theirs — the classic RGA tombstone rule, and here it is by
construction: the traversal (`emitK`) does not take the tombstone array at
all; only the final output filter does.

Junk degradation: the traversal is total for *any* input (fuel-totalized,
`Exec.chainHits` discipline). An element whose anchor word is out of range or
below `-1` is never anyone's child and is silently absent from the output;
malformed input degrades to junk output, never to non-termination or a crash.
The completeness theorem (`linearizeK_mem`) is correspondingly conditional on
well-formed anchors (`WFK` below) — the shape the Rust encoder establishes
and asserts, exactly as `movelog.rs` asserts `GroundedBase`.

## Claim discipline

By construction (no proof debt): `seqReplay` is literally
`encodeVisible ∘ linearizeK ∘ (decodeAnchors, decodeDeleted)` — a composition,
not a re-implementation. The decision layer is the named pure function
`linearizeK`; every theorem below is about the function the shipping kernel
runs.

**Proved, in this file** (axioms ⊆ `{propext, Classical.choice, Quot.sound}`;
no `sorry`/`native_decide`/`#guard`):

  * `linearizeK_mem` — completeness: under `WFK` (anchors in range and some
    rank strictly descending along anchor edges — the grounded discipline of
    `Acyclicity.lean`, supplied by the Rust side's creation rank), every
    in-range, non-tombstoned element appears in the output.
  * `emitK_count_le_one` / `linearizeK_nodup` — no element is emitted twice,
    under groundedness alone (anchor uniqueness is structural here: the anchor
    array is a function, the cryptographic discharge of `Sequence.lean`'s
    `UniqueAnchor` hypothesis made literal).
  * `linearizeK_ancestor_precedes` — every *visible strict ancestor* of a
    visible element precedes it in the output; `linearizeK_anchor_precedes` is
    the direct-anchor corollary. When an element's direct anchor is
    tombstoned, the ancestor form still places the element after its nearest
    visible ancestor.
  * `linearizeK_sublist_emitAll` — tombstones act on the output only: the
    visible linearization is a sublist of the full document order, so a delete
    can never reorder, duplicate, or reveal surviving elements.
  * `wfk_of_index_ordered` — the creation-ordered special case: if the dense
    order itself satisfies `anchor < index` (`Sequence.lean`'s `anchor < id`
    discipline), `WFK` holds with rank = index. The shipping Rust order is
    content-hash order, which is *not* creation order, so the Rust side
    supplies the creation rank explicitly instead.

**Determinism / SEC framing.** `linearizeK` is a pure function, so the kernel
is deterministic by construction; the replicated substrate is the grow-only
element set with tombstone-OR (Rust side), whose merge-stability is
`Sequence.wf_iconfluent` territory, and the linearization is a derived view in
exactly the sense of `Move.derived_view_sec` / `Sequence.sequence_view_sec`:
replicas that hold the same element set hand this kernel the same bytes (the
dense order is id-sorted, replica-independent) and get the same document.

## Non-claims — read before building a text editor on this

  * **No-interleaving is NOT provided.** `Sequence.lean`'s
    `interleaving_anomaly` governs this kernel too: concurrent runs inserted
    at the same anchor come out arbitrated by id and can strictly alternate.
    Fugue (Weidner–Kleppmann), which targets exactly that anomaly, is cited,
    not implemented.
  * **Intention preservation is not formalized** — `run_order_by_id`'s
    caveat applies verbatim: sibling order is id arbitration no user chose.
  * **No garbage collection.** Tombstones accumulate forever; this file
    implements deletion's semantics, not its storage economics.
  * **The input codec is not proved.** Unlike `Exec.lean` (whose request
    codec round-trips by `ExecRefine` §8 and is differentially checked from
    Rust), this kernel has no Lean-side canonical request encoder and no
    canonicality checker — the Rust marshaller's agreement with the layout
    above is test evidence only. The export surface stays at exactly one
    symbol by design; growing a checker is future work, not a hidden feature.
  * **Everything downstream of the C backend is trusted**, as everywhere in
    this library.
-/
import Uwueave.Exec
import Uwueave.ExecRefine

namespace Uwueave.SeqKernel

open Uwueave.Exec (getWord toI pushWord length_le_of_nodup_of_lt)

/-! ## §1. The decision core -/

/-- The anchor word of element `i`: `-1` = root. Out-of-range reads degrade to
`-1` (total; such indices are never emitted anyway, since the traversal only
ranges over `anchor.size`). -/
def anchorAt (anchor : Array Int) (i : Nat) : Int :=
  anchor.getD i (-1)

/-- The children of anchor value `p` (`-1` = root, otherwise an element
index), in **descending index order** — the RGA rule with the id order as the
tie-break: the highest id sits closest to its anchor. Pure arbitration
(`Uwueave.Sequence.run_order_by_id`), not recency. -/
def childrenK (anchor : Array Int) (p : Int) : List Nat :=
  ((List.range anchor.size).reverse).filter (fun i => anchorAt anchor i == p)

/-- Depth-first emission below one anchor value, fuel-totalized (the
`Exec.chainHits` discipline): for each child, highest index first, emit the
child and then its whole subtree. Tombstones are invisible here **by
construction** — this function does not take the tombstone array — which is
what keeps deleted elements anchorable. -/
def emitK (anchor : Array Int) : Nat → Int → List Nat
  | 0, _ => []
  | fuel + 1, p =>
    (childrenK anchor p).flatMap (fun c => c :: emitK anchor fuel ((c : Int)))

/-- The full document order (tombstones included): depth-first from the root
with fuel `n`. Fuel `n` is adequate for every root-reachable element under
groundedness — `ChainK.length_le` bounds every anchor chain by pigeonhole,
and `ChainK.mem_emitK` turns the bound into membership. -/
def emitAll (anchor : Array Int) : List Nat :=
  emitK anchor anchor.size (-1)

/-- **The pure decision core**: the visible linearization — the document
order with tombstoned elements filtered out of the *output only* (they keep
their position in the forest, so their descendants and later anchorings are
unaffected: the classic RGA tombstone rule). -/
def linearizeK (anchor : Array Int) (deleted : Array Bool) : Array Nat :=
  ((emitAll anchor).filter (fun i => !(deleted.getD i false))).toArray

/-! ## §2. The byte layer — decode, encode, entry point

Same style as `Exec.lean`: totalized word reads (`Exec.getWord` is `0` out of
range), so malformed input degrades to junk output, never to a crash. -/

/-- Decode words `1 .. 1+n` as the anchor array (`n` = word 0). -/
def decodeAnchors (input : ByteArray) : Array Int :=
  let n := (getWord input 0).toNat
  (Array.range n).map (fun i => toI (getWord input (1 + i)))

/-- Decode words `1+n .. 1+2n` as the tombstone array: any nonzero word is a
tombstone (the Rust encoder only sends `0`/`1`; the decode totalizes the
rest). -/
def decodeDeleted (input : ByteArray) : Array Bool :=
  let n := (getWord input 0).toNat
  (Array.range n).map (fun i => getWord input (1 + n + i) != 0)

/-- Encode the visible linearization: its length, then one word per index. -/
def encodeVisible (v : Array Nat) : ByteArray :=
  v.foldl (fun b i => pushWord b (UInt64.ofNat i))
    (pushWord ByteArray.empty (UInt64.ofNat v.size))

/-- The replay: literally decode → `linearizeK` → encode. The byte layer's
agreement with the decision layer is **by construction** — this is a
composition, not a re-implementation. -/
def seqReplay (input : ByteArray) : ByteArray :=
  encodeVisible (linearizeK (decodeAnchors input) (decodeDeleted input))

/-- The C entry point. Owned `ByteArray` in, owned `ByteArray` out. -/
@[export uwueave_seq_kernel]
def seqKernel (input : ByteArray) : ByteArray :=
  seqReplay input

/-! ## §3. Children and emission: basic structure -/

theorem mem_childrenK {anchor : Array Int} {p : Int} {c : Nat} :
    c ∈ childrenK anchor p ↔ c < anchor.size ∧ anchorAt anchor c = p := by
  simp [childrenK, List.mem_filter, List.mem_reverse, List.mem_range,
    beq_iff_eq]

theorem childrenK_nodup (anchor : Array Int) (p : Int) :
    (childrenK anchor p).Nodup :=
  List.Sublist.nodup List.filter_sublist
    ((List.reverse_perm (List.range anchor.size)).symm.nodup List.nodup_range)

/-- Everything emitted is below the size bound — for *every* input, junk
included. -/
theorem emitK_lt {anchor : Array Int} :
    ∀ fuel p j, j ∈ emitK anchor fuel p → j < anchor.size := by
  intro fuel
  induction fuel with
  | zero => intro p j h; simp [emitK] at h
  | succ fuel ih =>
    intro p j h
    simp only [emitK] at h
    obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp h
    have hcn : c < anchor.size := (mem_childrenK.mp hc).1
    cases hj with
    | head => exact hcn
    | tail _ hj => exact ih _ j hj

/-! ## §4. Anchor chains

`ChainK anchor p i l`: the elements stepped through descending from anchor
value `p` to element `i` — top child first, `i` last. This is `Sequence.lean`'s
`Below`, with the chain explicit so its *length* can pay for fuel and its
*ranks* can pay for duplicate-freedom. -/

/-- An anchor chain from anchor value `p` down to element `i`. -/
inductive ChainK (anchor : Array Int) : Int → Nat → List Nat → Prop where
  | child {p : Int} {i : Nat} (hi : i < anchor.size)
      (ha : anchorAt anchor i = p) : ChainK anchor p i [i]
  | step {p : Int} {c i : Nat} {l : List Nat} (hc : c < anchor.size)
      (ha : anchorAt anchor c = p) (h : ChainK anchor ((c : Int)) i l) :
      ChainK anchor p i (c :: l)

/-- `i` lies strictly inside the subtree hanging off anchor value `p`. -/
def BelowK (anchor : Array Int) (p : Int) (i : Nat) : Prop :=
  ∃ l, ChainK anchor p i l

theorem ChainK.length_pos {anchor : Array Int} {p : Int} {i : Nat}
    {l : List Nat} (h : ChainK anchor p i l) : 0 < l.length := by
  cases h <;> simp

theorem ChainK.endpoint_lt {anchor : Array Int} {p : Int} {i : Nat}
    {l : List Nat} (h : ChainK anchor p i l) : i < anchor.size := by
  induction h with
  | child hi _ => exact hi
  | step _ _ _ ih => exact ih

theorem ChainK.endpoint_mem {anchor : Array Int} {p : Int} {i : Nat}
    {l : List Nat} (h : ChainK anchor p i l) : i ∈ l := by
  induction h with
  | child _ _ => exact List.mem_singleton.mpr rfl
  | step _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem ChainK.sizes {anchor : Array Int} {p : Int} {i : Nat} {l : List Nat}
    (h : ChainK anchor p i l) : ∀ x ∈ l, x < anchor.size := by
  induction h with
  | child hi _ =>
    intro x hx
    rw [List.mem_singleton] at hx
    exact hx ▸ hi
  | step hc _ _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hc
    · exact ih x hx'

/-- Concatenating chains: `p ⇝ g` then `g ⇝ i` is `p ⇝ i`. -/
theorem ChainK.append {anchor : Array Int} {p : Int} {g : Nat}
    {lg : List Nat} (hg : ChainK anchor p g lg) :
    ∀ {li : List Nat} {i : Nat}, ChainK anchor ((g : Int)) i li →
      ChainK anchor p i (lg ++ li) := by
  induction hg with
  | child hm ha => intro li i hi; exact .step hm ha hi
  | step hc ha _ ih => intro li i hi; exact .step hc ha (ih hi)

/-- Append one child step at the bottom of a chain. -/
theorem ChainK.extend {anchor : Array Int} {p : Int} {m : Nat}
    {l : List Nat} (h : ChainK anchor p m l) :
    ∀ {i : Nat}, i < anchor.size → anchorAt anchor i = (m : Int) →
      ChainK anchor p i (l ++ [i]) := by
  induction h with
  | child hm ham => intro i hi ha; exact .step hm ham (.child hi ha)
  | step hc hac _ ih => intro i hi ha; exact .step hc hac (ih hi ha)

/-- **Fuel adequacy, chain-length form**: fuel covering the chain's length
emits the chain's endpoint. No well-formedness hypothesis — a chain is its
own witness. -/
theorem ChainK.mem_emitK {anchor : Array Int} {p : Int} {i : Nat}
    {l : List Nat} (h : ChainK anchor p i l) :
    ∀ fuel, l.length ≤ fuel → i ∈ emitK anchor fuel p := by
  induction h with
  | child hi ha =>
    intro fuel hf
    cases fuel with
    | zero => simp only [List.length_cons, List.length_nil] at hf; omega
    | succ fuel =>
      simp only [emitK]
      exact List.mem_flatMap.mpr
        ⟨_, mem_childrenK.mpr ⟨hi, ha⟩, List.mem_cons_self⟩
  | step hc ha _ ih =>
    intro fuel hf
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      simp only [List.length_cons] at hf
      simp only [emitK]
      exact List.mem_flatMap.mpr
        ⟨_, mem_childrenK.mpr ⟨hc, ha⟩,
         List.mem_cons_of_mem _ (ih fuel (by omega))⟩

/-- Whatever the emission emits below `p` really is below `p` — for every
input, any fuel. -/
theorem emitK_below {anchor : Array Int} :
    ∀ fuel (p : Int) (j : Nat), j ∈ emitK anchor fuel p → BelowK anchor p j := by
  intro fuel
  induction fuel with
  | zero => intro p j h; simp [emitK] at h
  | succ fuel ih =>
    intro p j h
    simp only [emitK] at h
    obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp h
    obtain ⟨hcs, hca⟩ := mem_childrenK.mp hc
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact ⟨[j], .child hcs hca⟩
    · obtain ⟨l, hl⟩ := ih ((c : Int)) j hj'
      exact ⟨c :: l, .step hcs hca hl⟩

/-- Anything in the chunk a child `c` contributes is `c` itself or below it. -/
theorem chunk_mem_belowK {anchor : Array Int} {fuel c j : Nat}
    (h : j ∈ c :: emitK anchor fuel ((c : Int))) :
    j = c ∨ BelowK anchor ((c : Int)) j := by
  rcases List.mem_cons.mp h with rfl | h'
  · exact .inl rfl
  · exact .inr (emitK_below fuel _ j h')

/-! ## §5. Groundedness: rank descent along anchor edges

The Rust encoder's dense order is *content-hash* order, which is not creation
order — an element's anchor may well carry a larger index. What the encoder
*does* have is `Exec.GroundedBase`'s shape: a creation rank (anchors must
exist before the elements anchored to them) that strictly descends along
every anchor edge. Everything below assumes exactly that and nothing about
the index order. -/

/-- Some rank strictly descends along every present anchor edge — the
`Exec.GroundedBase` shape for this kernel. Out of range, `anchorAt` is `-1`
and the hypothesis is vacuous. `rust/src/seq.rs` asserts this at encode time
(rank = creation rank), exactly as `movelog.rs` asserts `GroundedBase`. -/
def GroundedAnchors (r : Nat → Nat) (anchor : Array Int) : Prop :=
  ∀ i : Nat, 0 ≤ anchorAt anchor i → r (anchorAt anchor i).toNat < r i

/-- Along a chain, rank strictly increases downward — and a nonneg anchor
value ranks strictly below everything on the chain. -/
theorem ChainK.rank_facts {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {p : Int} {i : Nat} {l : List Nat}
    (h : ChainK anchor p i l) :
    (∀ x ∈ l, 0 ≤ p → r p.toNat < r x)
      ∧ l.Pairwise (fun a b => r a < r b) := by
  induction h with
  | child hi ha =>
    refine ⟨?_, .cons (by intro b hb; simp at hb) .nil⟩
    intro x hx hp
    rw [List.mem_singleton] at hx
    subst hx
    have h0 : 0 ≤ anchorAt anchor x := by rw [ha]; exact hp
    have hg := hgr x h0
    rw [ha] at hg
    exact hg
  | @step p c i l hc ha _ ih =>
    obtain ⟨ihead, ipair⟩ := ih
    have hcx : ∀ x ∈ l, r c < r x := by
      intro x hx
      have := ihead x hx (by omega)
      simpa using this
    have hpc : 0 ≤ p → r p.toNat < r c := by
      intro hp
      have h0 : 0 ≤ anchorAt anchor c := by rw [ha]; exact hp
      have hg := hgr c h0
      rw [ha] at hg
      exact hg
    refine ⟨?_, .cons hcx ipair⟩
    intro x hx hp
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hpc hp
    · exact Nat.lt_trans (hpc hp) (hcx x hx')

/-- On a grounded forest, chains visit no element twice. -/
theorem ChainK.nodup {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {p : Int} {i : Nat} {l : List Nat}
    (h : ChainK anchor p i l) : l.Nodup :=
  (h.rank_facts hgr).2.imp fun hlt he => absurd (he ▸ hlt) (Nat.lt_irrefl _)

/-- **The pigeonhole bound**: on a grounded forest every chain is no longer
than the element count — distinct in-range indices cannot exceed `n`
(`Exec.length_le_of_nodup_of_lt`, `ExecRefine` §3). This is what makes the
literal fuel `n` in `emitAll` adequate. -/
theorem ChainK.length_le {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {p : Int} {i : Nat} {l : List Nat}
    (h : ChainK anchor p i l) : l.length ≤ anchor.size :=
  length_le_of_nodup_of_lt (h.nodup hgr) h.sizes

/-- Below-ness transports rank: a nonneg anchor value ranks strictly below
everything in its subtree. -/
theorem BelowK.rank_lt {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {p : Int} {i : Nat}
    (h : BelowK anchor p i) (hp : 0 ≤ p) : r p.toNat < r i := by
  obtain ⟨l, hl⟩ := h
  exact (hl.rank_facts hgr).1 i hl.endpoint_mem hp

/-- Invert the bottom of a chain: the endpoint's anchor is `p` itself, or an
element still strictly below `p`. -/
theorem ChainK.endpoint_anchor {anchor : Array Int} {p : Int} {i : Nat}
    {l : List Nat} (h : ChainK anchor p i l) :
    anchorAt anchor i = p
      ∨ ∃ m : Nat, m < anchor.size ∧ anchorAt anchor i = (m : Int)
          ∧ BelowK anchor p m := by
  induction h with
  | child _ ha => exact .inl ha
  | @step p c i l hc ha _ ih =>
    rcases ih with he | ⟨m, hm, hma, ⟨lm, hlm⟩⟩
    · exact .inr ⟨c, hc, he, ⟨[c], .child hc ha⟩⟩
    · exact .inr ⟨m, hm, hma, ⟨c :: lm, .step hc ha hlm⟩⟩

/-! ## §6. Well-formed anchors, and completeness -/

/-- **Well-formed anchors** — the hypothesis the Rust encoder establishes:
every anchor word is the root sentinel `-1` or an in-range index, and some
rank strictly descends along anchor edges. Note the *index order* is left
completely free: the shipping dense order is content-hash order, and the rank
is the Rust side's creation rank. -/
structure WFK (r : Nat → Nat) (anchor : Array Int) : Prop where
  in_range : ∀ i : Nat, i < anchor.size →
    -1 ≤ anchorAt anchor i ∧ anchorAt anchor i < (anchor.size : Int)
  grounded : GroundedAnchors r anchor

/-- The creation-ordered special case (`Sequence.lean`'s `anchor < id`
discipline, `Acyclicity.lean`'s rank = id): a dense order that is itself
creation order satisfies `WFK` with rank = index. The shipping Rust order is
content-hash order, which is **not** creation order — it supplies the
creation rank explicitly instead. -/
theorem wfk_of_index_ordered {anchor : Array Int}
    (h : ∀ i : Nat, i < anchor.size →
      -1 ≤ anchorAt anchor i ∧ anchorAt anchor i < (i : Int)) :
    WFK (fun i => i) anchor := by
  refine ⟨fun i hi => ?_, fun i h0 => ?_⟩
  · obtain ⟨h1, h2⟩ := h i hi
    exact ⟨h1, by omega⟩
  · by_cases hi : i < anchor.size
    · obtain ⟨-, h2⟩ := h i hi
      omega
    · exfalso
      have : anchorAt anchor i = -1 := by
        unfold anchorAt
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
        rfl
      omega

/-- On a well-formed forest every in-range element has a chain from the root:
follow anchors upward; rank strictly decreases, so the walk terminates at the
sentinel. -/
theorem chain_to_root {r : Nat → Nat} {anchor : Array Int} (hwf : WFK r anchor) :
    ∀ i, i < anchor.size → BelowK anchor (-1) i := by
  have key : ∀ k i, r i < k → i < anchor.size → BelowK anchor (-1) i := by
    intro k
    induction k with
    | zero => intro i h _; omega
    | succ k ih =>
      intro i hik hi
      obtain ⟨hlo, hhi⟩ := hwf.in_range i hi
      by_cases ha : anchorAt anchor i = -1
      · exact ⟨[i], .child hi ha⟩
      · have h0 : 0 ≤ anchorAt anchor i := by omega
        have hrank := hwf.grounded i h0
        obtain ⟨l, hl⟩ := ih (anchorAt anchor i).toNat (by omega) (by omega)
        exact ⟨l ++ [i], hl.extend hi (by omega)⟩
  exact fun i hi => key (r i + 1) i (Nat.lt_succ_self _) hi

/-- Completeness of the document order: every in-range element appears. -/
theorem emitAll_mem {r : Nat → Nat} {anchor : Array Int} (hwf : WFK r anchor)
    {i : Nat} (hi : i < anchor.size) : i ∈ emitAll anchor := by
  obtain ⟨l, hl⟩ := chain_to_root hwf i hi
  exact hl.mem_emitK anchor.size (hl.length_le hwf.grounded)

/-- **Completeness (membership)**: under `WFK`, every in-range element that is
not tombstoned appears in the visible linearization. Junk inputs (anchors out
of range, `deleted` shorter than `n`) simply fall outside the hypotheses and
degrade to omission, never to a crash. -/
theorem linearizeK_mem {r : Nat → Nat} {anchor : Array Int}
    {deleted : Array Bool} (hwf : WFK r anchor) {i : Nat}
    (hi : i < anchor.size) (hvis : deleted.getD i false = false) :
    i ∈ (linearizeK anchor deleted).toList := by
  simp only [linearizeK, List.toList_toArray]
  exact List.mem_filter.mpr ⟨emitAll_mem hwf hi, by simp [hvis]⟩

/-! ## §7. No duplicates

`Sequence.lean` needed `UniqueAnchor` as an extra hypothesis because its
state was a *set* of `(id, anchor)` pairs; here the anchor array is a
function, so anchor uniqueness is structural — the cryptographic discharge
(id = hash(anchor, contents), `rust/src/seq.rs`) made literal. What remains
is the sibling-subtree disjointness argument, run on ranks instead of id
order. -/

/-- One sibling's subtree cannot contain another sibling. (No size
hypotheses needed — the rank argument alone carries it.) -/
theorem not_belowK_sibling {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {p : Int} {c c' : Nat}
    (hac : anchorAt anchor c = p) (hac' : anchorAt anchor c' = p) :
    ¬ BelowK anchor ((c' : Int)) c := by
  intro hb
  obtain ⟨l, hl⟩ := hb
  rcases hl.endpoint_anchor with ha1 | ⟨m, hm, hma, hbm⟩
  · -- c's own anchor is c' — then c' is anchored to itself, against rank
    have hpc : p = (c' : Int) := by rw [← hac, ha1]
    have h0 : 0 ≤ anchorAt anchor c' := by rw [hac', hpc]; omega
    have hg := hgr c' h0
    rw [hac', hpc] at hg
    simp only [Int.toNat_natCast] at hg
    omega
  · -- c's anchor is some m strictly below c' — but m is also p, above c'
    have hpm : p = (m : Int) := by rw [← hac, hma]
    have h1 : r c' < r m := by
      have := hbm.rank_lt hgr (by omega)
      simpa using this
    have h2 : r m < r c' := by
      have h0 : 0 ≤ anchorAt anchor c' := by rw [hac', hpm]; omega
      have hg := hgr c' h0
      rw [hac', hpm] at hg
      simpa using hg
    omega

/-- Subtrees of distinct siblings are disjoint: walk both witnesses up from
`j`; the anchor array forces the walks to coincide until they would have to
cross between siblings, which `not_belowK_sibling` forbids. Recursion is on
the rank of `j` — each step moves to `j`'s anchor, which ranks strictly
lower. -/
theorem belowK_sibling_disjoint {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {p : Int} {c c' : Nat}
    (hc : c < anchor.size) (hac : anchorAt anchor c = p)
    (hc' : c' < anchor.size) (hac' : anchorAt anchor c' = p) (hne : c ≠ c')
    (j : Nat) (hj : BelowK anchor ((c : Int)) j)
    (hj' : BelowK anchor ((c' : Int)) j) : False := by
  obtain ⟨l, hl⟩ := hj
  obtain ⟨l', hl'⟩ := hj'
  rcases hl.endpoint_anchor with ha1 | ⟨m, hm, hma, hbm⟩
  · rcases hl'.endpoint_anchor with ha2 | ⟨m', hm', hma', hbm'⟩
    · -- j is anchored to both c and c' directly: c = c'
      rw [ha1] at ha2
      exact hne (by omega)
    · -- j anchored to c, and to some m' below c': m' = c crosses siblings
      have hmc : m' = c := by rw [ha1] at hma'; omega
      subst hmc
      exact not_belowK_sibling hgr hac hac' hbm'
  · rcases hl'.endpoint_anchor with ha2 | ⟨m', hm', hma', hbm'⟩
    · have hmc : m = c' := by rw [ha2] at hma; omega
      subst hmc
      exact not_belowK_sibling hgr hac' hac hbm
    · -- both step through j's (unique) anchor: recurse on it
      have hmm : m' = m := by rw [hma] at hma'; omega
      subst hmm
      have hrmj : r m' < r j := by
        have h0 : 0 ≤ anchorAt anchor j := by rw [hma]; omega
        have hg := hgr j h0
        rw [hma] at hg
        simpa using hg
      exact belowK_sibling_disjoint hgr hc hac hc' hac' hne m' hbm hbm'
termination_by r j
decreasing_by exact hrmj

/-- A single child chunk emits any given id at most once: the head cannot
recur in its own subtree (rank strictly increases downward), and the subtree
is covered by the fuel induction hypothesis. -/
private theorem count_chunk_le_one_K {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {fuel : Nat}
    (ih : ∀ (p : Int) (j : Nat), (emitK anchor fuel p).count j ≤ 1)
    (c j : Nat) : (c :: emitK anchor fuel ((c : Int))).count j ≤ 1 := by
  rw [List.count_cons]
  by_cases hjc : c = j
  · subst hjc
    have hzero : (emitK anchor fuel ((c : Int))).count c = 0 := by
      apply List.count_eq_zero_of_not_mem
      intro hmem
      have := (emitK_below fuel _ c hmem).rank_lt hgr (by omega)
      simp only [Int.toNat_natCast] at this
      omega
    simp [hzero]
  · simp [hjc]
    exact ih _ j

/-- The flatMap over a duplicate-free list of same-anchor children emits any
given id at most once: chunks of distinct siblings are disjoint
(`belowK_sibling_disjoint`), so at most one chunk can mention `j`, and that
chunk mentions it at most once (`count_chunk_le_one_K`). -/
private theorem count_flatMap_le_one_K {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) {fuel : Nat} {p : Int}
    (ih : ∀ (p' : Int) (j : Nat), (emitK anchor fuel p').count j ≤ 1) :
    ∀ cs : List Nat, cs.Nodup →
      (∀ c ∈ cs, c < anchor.size ∧ anchorAt anchor c = p) → ∀ j,
      (cs.flatMap (fun c => c :: emitK anchor fuel ((c : Int)))).count j ≤ 1 := by
  intro cs
  induction cs with
  | nil => intro _ _ j; simp
  | cons c cs ihcs =>
    intro hnodup hanchor j
    rw [List.flatMap_cons, List.count_append]
    obtain ⟨hcnotin, hnodup'⟩ := List.nodup_cons.mp hnodup
    have hrest := ihcs hnodup'
      (fun c' hc' => hanchor c' (List.mem_cons_of_mem c hc')) j
    have hchunk := count_chunk_le_one_K hgr ih c j
    by_cases hz : (cs.flatMap (fun c => c :: emitK anchor fuel ((c : Int)))).count j = 0
    · omega
    · have hmem : j ∈ cs.flatMap (fun c => c :: emitK anchor fuel ((c : Int))) :=
        List.count_pos_iff.mp (by omega)
      obtain ⟨c', hc'in, hjc'⟩ := List.mem_flatMap.mp hmem
      have hnot : j ∉ c :: emitK anchor fuel ((c : Int)) := by
        intro hjc
        have h1 := chunk_mem_belowK hjc
        have h2 := chunk_mem_belowK hjc'
        have hcc' : c ≠ c' := fun h => hcnotin (h.symm ▸ hc'in)
        obtain ⟨hca_sz, hca⟩ := hanchor c List.mem_cons_self
        obtain ⟨hc'a_sz, hc'a⟩ := hanchor c' (List.mem_cons_of_mem c hc'in)
        rcases h1 with rfl | hb1
        · rcases h2 with rfl | hb2
          · exact hcc' rfl
          · exact not_belowK_sibling hgr hca hc'a hb2
        · rcases h2 with rfl | hb2
          · exact not_belowK_sibling hgr hc'a hca hb1
          · exact belowK_sibling_disjoint hgr hca_sz hca hc'a_sz hc'a hcc' j hb1 hb2
      rw [List.count_eq_zero_of_not_mem hnot]
      omega

/-- Every id is emitted at most once, from any anchor, at any fuel — under
groundedness alone. -/
theorem emitK_count_le_one {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) :
    ∀ fuel (p : Int) (j : Nat), (emitK anchor fuel p).count j ≤ 1 := by
  intro fuel
  induction fuel with
  | zero => intro p j; simp [emitK]
  | succ fuel ih =>
    intro p j
    simp only [emitK]
    exact count_flatMap_le_one_K hgr ih (childrenK anchor p)
      (childrenK_nodup anchor p) (fun c hc => mem_childrenK.mp hc) j

private theorem nodup_of_count_le_one :
    ∀ {l : List Nat}, (∀ j, l.count j ≤ 1) → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
    intro h
    rw [List.nodup_cons]
    refine ⟨fun hmem => ?_, ih fun j => ?_⟩
    · have h1 := h a
      rw [List.count_cons] at h1
      have h2 : 0 < t.count a := List.count_pos_iff.mpr hmem
      simp at h1
      omega
    · have := h j
      rw [List.count_cons] at this
      split at this <;> omega

/-- The full document order is duplicate-free on a grounded forest. -/
theorem emitAll_nodup {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) : (emitAll anchor).Nodup :=
  nodup_of_count_le_one fun j => emitK_count_le_one hgr anchor.size (-1) j

/-- **No duplicates**: no element appears twice in the visible linearization,
under groundedness alone (no in-range hypothesis needed — junk elements are
simply never emitted). -/
theorem linearizeK_nodup {r : Nat → Nat} {anchor : Array Int}
    (hgr : GroundedAnchors r anchor) (deleted : Array Bool) :
    (linearizeK anchor deleted).toList.Nodup := by
  simp only [linearizeK, List.toList_toArray]
  exact List.Sublist.nodup List.filter_sublist (emitAll_nodup hgr)

/-! ## §8. Ancestors precede, and tombstones only filter -/

private theorem sublist_flatMap_of_mem {α β : Type} (f : α → List β) :
    ∀ (cs : List α) (c : α), c ∈ cs → (f c).Sublist (cs.flatMap f) := by
  intro cs
  induction cs with
  | nil => intro c hc; cases hc
  | cons c' cs ihcs =>
    intro c hc
    rw [List.flatMap_cons]
    cases hc with
    | head => exact List.sublist_append_left _ _
    | tail _ hc => exact (ihcs c hc).trans (List.sublist_append_right _ _)

/-- Inside any emission that reaches `g`, the element `g` is emitted and
everything below it follows it: `[g, i]` is a subsequence whenever the fuel
covers the concatenated chain. -/
theorem ChainK.ancestor_sublist {anchor : Array Int} {lg : List Nat} {p : Int}
    {g : Nat} (hg : ChainK anchor p g lg) :
    ∀ (li : List Nat) (i : Nat), ChainK anchor ((g : Int)) i li →
      ∀ fuel, lg.length + li.length ≤ fuel →
      [g, i].Sublist (emitK anchor fuel p) := by
  induction hg with
  | @child p g hm ha =>
    intro li i hi fuel hf
    cases fuel with
    | zero => simp only [List.length_cons, List.length_nil] at hf; omega
    | succ fuel =>
      simp only [emitK]
      have himem : i ∈ emitK anchor fuel ((g : Int)) := by
        apply hi.mem_emitK
        simp only [List.length_cons, List.length_nil] at hf
        omega
      exact ((List.singleton_sublist.mpr himem).cons_cons g).trans
        (sublist_flatMap_of_mem (fun c => c :: emitK anchor fuel ((c : Int)))
          (childrenK anchor p) g (mem_childrenK.mpr ⟨hm, ha⟩))
  | @step p c g l hc ha _ ih =>
    intro li i hi fuel hf
    cases fuel with
    | zero => simp only [List.length_cons] at hf; omega
    | succ fuel =>
      simp only [emitK]
      have hsub := ih li i hi fuel
        (by simp only [List.length_cons] at hf ⊢; omega)
      exact (hsub.cons _).trans
        (sublist_flatMap_of_mem (fun c => c :: emitK anchor fuel ((c : Int)))
          (childrenK anchor p) c (mem_childrenK.mpr ⟨hc, ha⟩))

/-- **Ancestor-precedes**: any *visible strict ancestor* `g` of a visible
element `i` appears before `i` in the visible linearization — `[g, i]` is an
order-preserving (not necessarily contiguous) subsequence of the output. In
particular, a visible element whose direct anchor is tombstoned still sits
after its nearest visible ancestor. -/
theorem linearizeK_ancestor_precedes {r : Nat → Nat} {anchor : Array Int}
    {deleted : Array Bool} (hwf : WFK r anchor) {g i : Nat}
    (hb : BelowK anchor ((g : Int)) i) (hg : g < anchor.size)
    (hvg : deleted.getD g false = false) (hvi : deleted.getD i false = false) :
    [g, i].Sublist (linearizeK anchor deleted).toList := by
  obtain ⟨lg, hlg⟩ := chain_to_root hwf g hg
  obtain ⟨li, hli⟩ := hb
  have hlen : lg.length + li.length ≤ anchor.size := by
    have := (hlg.append hli).length_le hwf.grounded
    simpa [List.length_append] using this
  have hsub : [g, i].Sublist (emitAll anchor) :=
    hlg.ancestor_sublist li i hli anchor.size hlen
  have hfil : [g, i].filter (fun x => !(deleted.getD x false)) = [g, i] := by
    simp [List.filter, hvg, hvi]
  simp only [linearizeK, List.toList_toArray]
  have := hsub.filter (fun x => !(deleted.getD x false))
  rw [hfil] at this
  exact this

/-- **Anchor-precedes (direct corollary)**: a visible element's direct
anchor, when itself visible, appears somewhere before it. -/
theorem linearizeK_anchor_precedes {r : Nat → Nat} {anchor : Array Int}
    {deleted : Array Bool} (hwf : WFK r anchor) {i a : Nat}
    (hi : i < anchor.size) (ha : anchorAt anchor i = (a : Int))
    (hva : deleted.getD a false = false) (hvi : deleted.getD i false = false) :
    [a, i].Sublist (linearizeK anchor deleted).toList := by
  have hasz : a < anchor.size := by
    have := (hwf.in_range i hi).2
    omega
  exact linearizeK_ancestor_precedes hwf ⟨[i], .child hi ha⟩ hasz hva hvi

/-- **Tombstones act on the output only**: the visible linearization is a
sublist of the full document order, for *every* input — so deleting elements
can never reorder, duplicate, or newly reveal the survivors; it only removes
occurrences. (`emitK` cannot even read the tombstones: it does not take
them.) -/
theorem linearizeK_sublist_emitAll (anchor : Array Int) (deleted : Array Bool) :
    (linearizeK anchor deleted).toList.Sublist (emitAll anchor) := by
  simp only [linearizeK, List.toList_toArray]
  exact List.filter_sublist ..

end Uwueave.SeqKernel
