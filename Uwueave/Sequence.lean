/-
# Uwueave.Sequence — RGA-style anchored text, as a derived view. Including the anomaly.

A collaborative *text* is the CRDT everyone actually wants, and it is where the
gap between "converges" and "does what the user meant" is widest. This file
builds the smallest honest miniature of the standard design — RGA-style
**anchored insertion** — on the substrate the rest of the library already
proved out, and then proves *both* sides of it:

  * the good side: the replicated state is a grow-only set, its well-formedness
    invariant is I-confluent (the `grounded_iconfluent` argument again), and the
    visible text is a deterministic derived view (`derived_view_sec` applies
    verbatim, instantiated here as `sequence_view_sec`) in which every present
    element appears, exactly once under a stated hypothesis, with its anchor
    always somewhere before it;
  * the bad side, as named theorems: the merged order is decided by **id
    arbitration, not user intention**, and concurrently inserted runs can come
    out **interleaved** (`interleaving_anomaly` — the anomaly of Kleppmann,
    Gomes, Mulligan & Beresford, "Interleaving anomalies in collaborative text
    editors", PaPoC 2019; PDF at
    `/Users/ember/paperbin/uweave/kleppmann-interleaving-anomalies.pdf`).

## The construction

Elements are ids drawn from `Nat`, bounded by an explicit `n` threaded through
everything. **Id `0` is reserved as the root sentinel**: it denotes "the start
of the document", is never itself an element, and the well-formedness invariant
makes that structural (an element's anchor is strictly smaller than its id, so
`(0, a)` present would need `a < 0`). The replicated state is

    `GSet (Nat × Nat)` — the pair `(i, a)` means "element `i` was inserted
    after anchor `a`" (`a = 0`: at the start of the document).

Insertion only: the state is grow-only, and **deletion is not modeled** —
tombstones are future work, not a hidden feature.

`WF n s` (the invariant): every present pair has `id < n`, `anchor < id`, and
the anchor is the sentinel or itself a present element. `anchor < id` is the
creation-order discipline of `Acyclicity.lean`: ids are creation-stamped (in a
content-addressed system, hash-derived), so an anchor is strictly older than
the element anchored to it — the anchor graph is *grounded* with rank = id, and
`wf_iconfluent` is the same per-element argument as `grounded_iconfluent`.

`linearize n s`: depth-first from the root, children of each anchor in
**descending id order** — the RGA rule, newest insertion closest to its anchor.
Totality is by fuel: along any anchor chain ids strictly increase and stay
below `n`, so a chain has length at most `n` and fuel `n` suffices
(`below_mem` makes the sufficiency a theorem, not a comment).

## What is proved

  * `wf_iconfluent` — `WF n` survives every merge (general).
  * `sequence_view_sec` — the linearization is a derived view in the sense of
    `Move.derived_view_sec`: delta order and redelivery are unobservable, and
    the view is bounded by `n` at every replica (general).
  * `linearize_mem` — every present element appears in the linearization
    (general, `WF` only).
  * `linearize_count_one` — every present element appears **exactly once**
    (general, but under `WF` *plus* `UniqueAnchor`: no id inserted with two
    anchors. That extra hypothesis is honest load-bearing: it is **not**
    I-confluent in this model (`wf_unique_anchor_not_iconfluent`), and without
    it a well-formed merge really does duplicate (`dup_id_appears_twice`). A
    content-addressed deployment discharges it *cryptographically* — id =
    hash(content, anchor) makes one id carry two anchors only via a hash
    collision — which is a premise about SHA-2, not a theorem here; the same
    discipline as the rank remark in `Acyclicity.lean`.)
  * `linearize_anchor_precedes` — an element's (non-root) anchor appears
    somewhere before it, stated as `[a, i].Sublist (linearize n s)` (general,
    `WF` only).
  * `interleaving_anomaly`, `run_order_by_id` — the honesty centerpiece; see
    §6.

## Non-claims — read before building a text editor on this

  * **No-interleaving is NOT provided.** `interleaving_anomaly` exhibits two
    replicas whose two-element runs are each contiguous locally and strictly
    alternated after merge. This construction converges; it does not promise
    the converged text reads sensibly.
  * **Intention preservation is not formalized** — not even stated. There is
    no model of "what the user meant" here, only of what the algorithm does;
    `run_order_by_id` shows the merged run order is decided by id comparison,
    which no user chose.
  * **Deletion is not modeled.** Grow-only. Real sequence CRDTs spend most of
    their complexity on tombstones and garbage collection.
  * **Exactly-once needs `UniqueAnchor`**, an assumption the lattice does not
    preserve (see above); membership and anchor-precedence do not.
  * **Real sequence CRDTs solve problems this miniature does not.** Loro, Yjs,
    Automerge/RGA descendants and especially Fugue (which targets exactly the
    interleaving anomaly proved here) handle deletion, rich positions, byte
    efficiency, and stronger ordering guarantees. This file is a lens for the
    *judgement* — which invariants of anchored text are coordination-free —
    not a competitor.
-/
import Uwueave.Move

namespace Uwueave.Sequence

open Uwueave Uwueave.Catalog

/-! ## §1. State and well-formedness -/

/-- The replicated state of the sequence: the grow-only set of insertions.
`(i, a)` present means "element `i` was inserted after anchor `a`"; anchor `0`
is the root sentinel (start of document). The `MergeState` instance is
inherited from `GSet` — union, nothing new to prove. -/
abbrev SeqState := GSet (Nat × Nat)

example : MergeState SeqState := inferInstance

/-- Well-formedness of a sequence state, relative to the id bound `n`: every
present insertion `(i, a)` has `i < n`, `a < i` (the creation-order
discipline — an anchor is strictly older than the element it anchors; rank =
id, exactly the grounded trick of `Acyclicity.lean`), and the anchor is the
root sentinel or itself present. Note `a < i` structurally excludes the
sentinel `0` from ever being an element: `(0, a)` present would need `a < 0`. -/
def WF (n : Nat) (s : SeqState) : Prop :=
  ∀ i a : Nat, s (i, a) = true →
    i < n ∧ a < i ∧ (a = 0 ∨ ∃ b, s (a, b) = true)

/-- **`WF n` is I-confluent** — anchored insertion needs no coordination. An
insertion of the union came from one replica; its bounds are per-element facts
(the `grounded_iconfluent` argument verbatim), and its anchor's presence is
monotone information, preserved by union (the `gset_monotone_iconfluent`
shape). -/
theorem wf_iconfluent (n : Nat) : IConfluent (S := SeqState) (WF n) := by
  intro x y hx hy i a hmem
  cases (Bool.or_eq_true _ _).mp hmem with
  | inl h =>
    obtain ⟨h1, h2, h3⟩ := hx i a h
    refine ⟨h1, h2, ?_⟩
    rcases h3 with h0 | ⟨b, hb⟩
    · exact Or.inl h0
    · refine Or.inr ⟨b, ?_⟩
      show (x (a, b) || y (a, b)) = true
      simp [hb]
  | inr h =>
    obtain ⟨h1, h2, h3⟩ := hy i a h
    refine ⟨h1, h2, ?_⟩
    rcases h3 with h0 | ⟨b, hb⟩
    · exact Or.inl h0
    · refine Or.inr ⟨b, ?_⟩
      show (x (a, b) || y (a, b)) = true
      simp [hb]

/-- No id is inserted with two different anchors. `linearize_count_one` needs
this; the model cannot enforce it (see `wf_unique_anchor_not_iconfluent`), a
content-addressed id scheme enforces it cryptographically. -/
def UniqueAnchor (s : SeqState) : Prop :=
  ∀ i a a', s (i, a) = true → s (i, a') = true → a = a'

/-- Replica X of the duplication pair: element 1 at the root, element 2
anchored to 1. -/
def dupX : SeqState := fun p => p == ((1 : Nat), (0 : Nat)) || p == ((2 : Nat), (1 : Nat))

/-- Replica Y of the duplication pair: element 2 at the root — the *same id*
as X's second insertion, with a different anchor. Content addressing would
forbid exactly this state pair (same id, different (content, anchor) preimage);
the model permits it. -/
def dupY : SeqState := fun p => p == ((2 : Nat), (0 : Nat))

theorem dupX_wf : WF 5 dupX := by
  intro i a h
  simp [dupX] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by omega, by omega, Or.inl rfl⟩
  · exact ⟨by omega, by omega, Or.inr ⟨0, by decide⟩⟩

theorem dupY_wf : WF 5 dupY := by
  intro i a h
  simp [dupY] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨by omega, by omega, Or.inl rfl⟩

theorem dupX_unique : UniqueAnchor dupX := by
  intro i a a' h h'
  simp [dupX] at h h'
  omega

theorem dupY_unique : UniqueAnchor dupY := by
  intro i a a' h h'
  simp [dupY] at h h'
  omega

/-- ⚠ **`WF ∧ UniqueAnchor` is NOT I-confluent.** `dupX` and `dupY` each
satisfy both; their union holds `(2, 1)` and `(2, 0)` — one id, two anchors.
This is why `linearize_count_one` carries `UniqueAnchor` as a hypothesis
rather than deriving it from `WF`: within the model the hypothesis is real,
and only a cryptographic id scheme (id = hash(content, anchor)) discharges it
globally. Compare `Catalog.gset_atMostOne_not_iconfluent` — per-id anchor
uniqueness is that ceiling invariant in sequence clothing. -/
theorem wf_unique_anchor_not_iconfluent :
    ¬ IConfluent (S := SeqState) (fun s => WF 5 s ∧ UniqueAnchor s) := by
  intro h
  obtain ⟨-, huniq⟩ := h dupX dupY ⟨dupX_wf, dupX_unique⟩ ⟨dupY_wf, dupY_unique⟩
  exact absurd (huniq 2 1 0 (by decide) (by decide)) (by decide)

/-! ## §2. The linearization — a deterministic derived view -/

/-- The children of anchor `a` present in `s`, in descending id order — the
RGA rule: the *newest* insertion sits closest to its anchor. -/
def children (n : Nat) (s : SeqState) (a : Nat) : List Nat :=
  ((List.range n).reverse).filter (fun i => s (i, a))

theorem mem_children {n : Nat} {s : SeqState} {a c : Nat} :
    c ∈ children n s a ↔ c < n ∧ s (c, a) = true := by
  simp [children, List.mem_filter, List.mem_reverse, List.mem_range]

theorem children_nodup (n : Nat) (s : SeqState) (a : Nat) :
    (children n s a).Nodup :=
  List.Sublist.nodup List.filter_sublist
    ((List.reverse_perm (List.range n)).symm.nodup List.nodup_range)

/-- Depth-first emission below one anchor: for each child (newest first), emit
the child, then its whole subtree. Totality is by fuel; `below_mem` proves
fuel `n` reaches everything, because ids strictly increase along anchor
chains. -/
def linearizeAux (n : Nat) (s : SeqState) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, a =>
    (children n s a).flatMap (fun c => c :: linearizeAux n s fuel c)

/-- The visible text (as a list of ids): depth-first from the root sentinel
with fuel `n`. A total, deterministic function of the state — the derived-view
pattern of `Move.lean`, instantiated in `sequence_view_sec`. -/
def linearize (n : Nat) (s : SeqState) : List Nat :=
  linearizeAux n s n 0

/-- Everything emitted is below the id bound — for *every* state, well-formed
or not; this is the invariant the interpreter enforces by construction, which
is what `derived_view_sec` asks of it. -/
theorem linearizeAux_lt {n : Nat} {s : SeqState} :
    ∀ fuel a j, j ∈ linearizeAux n s fuel a → j < n := by
  intro fuel
  induction fuel with
  | zero => intro a j h; simp [linearizeAux] at h
  | succ fuel ih =>
    intro a j h
    simp only [linearizeAux] at h
    obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp h
    have hcn : c < n := (mem_children.mp hc).1
    cases hj with
    | head => exact hcn
    | tail _ hj => exact ih c j hj

theorem linearize_lt {n : Nat} {s : SeqState} {j : Nat}
    (h : j ∈ linearize n s) : j < n :=
  linearizeAux_lt n 0 j h

/-- **The sequence is a derived view, with the pattern's full guarantee**:
deltas may arrive in either order or duplicated and the visible text is
identical, and the view is in-bounds at every point — `Move.derived_view_sec`
instantiated at `interp := linearize n`, not restated. Convergence of equal
states is the degenerate reading (a function of equal merges is equal); the
content here is that the *merge laws of the log* push through the
interpreter. -/
theorem sequence_view_sec (n : Nat) (base Δ₁ Δ₂ : SeqState) :
    linearize n ((base ⊔ Δ₁) ⊔ Δ₂) = linearize n ((base ⊔ Δ₂) ⊔ Δ₁)
    ∧ linearize n ((base ⊔ Δ₁) ⊔ Δ₁) = linearize n (base ⊔ Δ₁)
    ∧ ∀ j ∈ linearize n ((base ⊔ Δ₁) ⊔ Δ₂), j < n :=
  Move.derived_view_sec (linearize n) (fun v => ∀ j ∈ v, j < n)
    (fun _ _ hj => linearize_lt hj) base Δ₁ Δ₂

/-! ## §3. The subtree relation

`Below s a i`: element `i` sits strictly inside the subtree hanging off anchor
`a` — the transitive closure of "is a child of", built from the anchor side so
it peels the way the fuel recursion does. -/

/-- `i` is strictly below `a` in the anchor forest. -/
inductive Below (s : SeqState) : Nat → Nat → Prop where
  | child {a i : Nat} : s (i, a) = true → Below s a i
  | step {a c i : Nat} : s (c, a) = true → Below s c i → Below s a i

/-- Ids strictly increase downward through the anchor forest — `Below` is
grounded with rank = id, the `Acyclicity` argument again. -/
theorem Below.lt {n : Nat} {s : SeqState} (hwf : WF n s) {a i : Nat}
    (h : Below s a i) : a < i := by
  induction h with
  | child h => exact (hwf _ _ h).2.1
  | step h _ ih => exact Nat.lt_trans (hwf _ _ h).2.1 ih

/-- A nonempty subtree pins its anchor below the id bound. -/
theorem Below.anchor_lt_n {n : Nat} {s : SeqState} (hwf : WF n s) {a i : Nat}
    (h : Below s a i) : a < n := by
  cases h with
  | child h => have := hwf _ _ h; omega
  | step h _ => have := hwf _ _ h; omega

/-- Append one child step at the bottom of a `Below` chain. -/
theorem Below.extend {s : SeqState} {a m i : Nat}
    (h : Below s a m) (hi : s (i, m) = true) : Below s a i := by
  induction h with
  | child h => exact Below.step h (Below.child hi)
  | step h _ ih => exact Below.step h (ih hi)

/-- Invert the *bottom* of a `Below` chain: `i` has an anchor which is either
`a` itself or still strictly below `a`. -/
theorem Below.invert {s : SeqState} {a i : Nat} (h : Below s a i) :
    ∃ m, s (i, m) = true ∧ (m = a ∨ Below s a m) := by
  induction h with
  | child h => exact ⟨_, h, Or.inl rfl⟩
  | step h _ ih =>
    obtain ⟨m, hm, hcase⟩ := ih
    refine ⟨m, hm, Or.inr ?_⟩
    rcases hcase with rfl | hb
    · exact Below.child h
    · exact Below.step h hb

/-- On a well-formed state every present element is below the root: follow
anchors upward; each step strictly decreases the id, so the walk terminates at
the sentinel. -/
theorem below_root {n : Nat} {s : SeqState} (hwf : WF n s)
    (i a : Nat) (h : s (i, a) = true) : Below s 0 i := by
  obtain ⟨-, hlt, hroot | ⟨b, hb⟩⟩ := hwf i a h
  · exact hroot ▸ Below.child h
  · exact (below_root hwf a b hb).extend h
termination_by i
decreasing_by omega

/-- Soundness of the emission: whatever `linearizeAux` emits below `a` really
is below `a`. Holds for every state and any fuel. -/
theorem linearizeAux_below {n : Nat} {s : SeqState} :
    ∀ fuel a j, j ∈ linearizeAux n s fuel a → Below s a j := by
  intro fuel
  induction fuel with
  | zero => intro a j h; simp [linearizeAux] at h
  | succ fuel ih =>
    intro a j h
    simp only [linearizeAux] at h
    obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp h
    have hca : s (c, a) = true := (mem_children.mp hc).2
    cases hj with
    | head => exact Below.child hca
    | tail _ hj => exact Below.step hca (ih c j hj)

/-- Anything in the chunk a child `c` contributes is `c` itself or below it. -/
theorem chunk_mem_below {n : Nat} {s : SeqState} {fuel c j : Nat}
    (h : j ∈ c :: linearizeAux n s fuel c) : j = c ∨ Below s c j := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h => exact Or.inr (linearizeAux_below fuel c j h)

/-! ## §4. Completeness: present ⇒ emitted, and emitted once -/

/-- **The fuel argument, as a theorem**: with fuel at least `n - anchor`,
everything below the anchor is emitted. At fuel `0` the bound forces
`n ≤ anchor`, contradicting a nonempty subtree; at each descent the anchor
grows by at least one, so the bound regenerates. -/
theorem below_mem {n : Nat} {s : SeqState} (hwf : WF n s) :
    ∀ fuel anchor i, Below s anchor i → n - anchor ≤ fuel →
      i ∈ linearizeAux n s fuel anchor := by
  intro fuel
  induction fuel with
  | zero =>
    intro anchor i hb hfuel
    exact absurd (hb.anchor_lt_n hwf) (by omega)
  | succ fuel ih =>
    intro anchor i hb hfuel
    simp only [linearizeAux]
    cases hb with
    | child h =>
      exact List.mem_flatMap.mpr
        ⟨i, mem_children.mpr ⟨(hwf _ _ h).1, h⟩, List.mem_cons_self⟩
    | step hc hbelow =>
      refine List.mem_flatMap.mpr
        ⟨_, mem_children.mpr ⟨(hwf _ _ hc).1, hc⟩, List.mem_cons_of_mem _ ?_⟩
      apply ih _ i hbelow
      have := (hwf _ _ hc).2.1
      omega

/-- **Completeness (general, `WF` only)**: every present element appears in
the linearization. -/
theorem linearize_mem {n : Nat} {s : SeqState} (hwf : WF n s)
    {i a : Nat} (h : s (i, a) = true) : i ∈ linearize n s :=
  below_mem hwf n 0 i (below_root hwf i a h) (by omega)

/-- One sibling's subtree cannot contain another sibling (needs
`UniqueAnchor`: the trespasser's own anchor would have to be both `a` and
inside the other subtree). -/
theorem not_below_sibling {n : Nat} {s : SeqState} (hwf : WF n s)
    (huniq : UniqueAnchor s) {a c c' : Nat}
    (hc : s (c, a) = true) (hc' : s (c', a) = true) :
    ¬ Below s c' c := by
  intro hb
  obtain ⟨m, hm, hcase⟩ := hb.invert
  have hma : m = a := huniq c m a hm hc
  have hlt' := (hwf _ _ hc').2.1
  rcases hcase with hmc' | hbm
  · omega
  · have := hbm.lt hwf
    omega

/-- Subtrees of distinct siblings are disjoint (needs `UniqueAnchor`): walk
both witnesses up from `j`; unique anchoring forces the walks to coincide
until they would have to cross between siblings, which `not_below_sibling`
forbids. -/
theorem below_sibling_disjoint {n : Nat} {s : SeqState} (hwf : WF n s)
    (huniq : UniqueAnchor s) {a c c' : Nat}
    (hc : s (c, a) = true) (hc' : s (c', a) = true) (hne : c ≠ c')
    (j : Nat) (hj : Below s c j) (hj' : Below s c' j) : False := by
  obtain ⟨m, hm, hcase⟩ := hj.invert
  obtain ⟨m', hm', hcase'⟩ := hj'.invert
  have hmm : m = m' := huniq j m m' hm hm'
  subst hmm
  have hmj : m < j := (hwf _ _ hm).2.1
  rcases hcase with hmc | hbm
  · rcases hcase' with hmc' | hbm'
    · exact hne (hmc ▸ hmc')
    · exact not_below_sibling hwf huniq hc hc' (hmc ▸ hbm')
  · rcases hcase' with hmc' | hbm'
    · exact not_below_sibling hwf huniq hc' hc (hmc' ▸ hbm)
    · exact below_sibling_disjoint hwf huniq hc hc' hne m hbm hbm'
termination_by j
decreasing_by omega

/-- A single child chunk emits any given id at most once: the head cannot
recur in its own subtree (ids strictly increase downward), and the subtree is
covered by the fuel induction hypothesis. -/
private theorem count_chunk_le_one {n : Nat} {s : SeqState} (hwf : WF n s)
    {fuel : Nat} (ih : ∀ a j, (linearizeAux n s fuel a).count j ≤ 1)
    (c j : Nat) : (c :: linearizeAux n s fuel c).count j ≤ 1 := by
  rw [List.count_cons]
  by_cases hjc : c = j
  · subst hjc
    have hzero : (linearizeAux n s fuel c).count c = 0 := by
      apply List.count_eq_zero_of_not_mem
      intro hmem
      have := (linearizeAux_below fuel c c hmem).lt hwf
      omega
    simp [hzero]
  · simp [hjc]
    exact ih c j

/-- The flatMap over a duplicate-free list of same-anchor children emits any
given id at most once: chunks of distinct siblings are disjoint
(`below_sibling_disjoint`), so at most one chunk can mention `j`, and that
chunk mentions it at most once (`count_chunk_le_one`). -/
private theorem count_flatMap_le_one {n : Nat} {s : SeqState} (hwf : WF n s)
    (huniq : UniqueAnchor s) {fuel a : Nat}
    (ih : ∀ a' j, (linearizeAux n s fuel a').count j ≤ 1) :
    ∀ cs : List Nat, cs.Nodup → (∀ c ∈ cs, s (c, a) = true) → ∀ j,
      (cs.flatMap (fun c => c :: linearizeAux n s fuel c)).count j ≤ 1 := by
  intro cs
  induction cs with
  | nil => intro _ _ j; simp
  | cons c cs ihcs =>
    intro hnodup hanchor j
    rw [List.flatMap_cons, List.count_append]
    obtain ⟨hcnotin, hnodup'⟩ := List.nodup_cons.mp hnodup
    have hrest := ihcs hnodup'
      (fun c' hc' => hanchor c' (List.mem_cons_of_mem c hc')) j
    have hchunk := count_chunk_le_one hwf ih c j
    by_cases hz : (cs.flatMap (fun c => c :: linearizeAux n s fuel c)).count j = 0
    · omega
    · have hmem : j ∈ cs.flatMap (fun c => c :: linearizeAux n s fuel c) :=
        List.count_pos_iff.mp (by omega)
      obtain ⟨c', hc'in, hjc'⟩ := List.mem_flatMap.mp hmem
      have hnot : j ∉ c :: linearizeAux n s fuel c := by
        intro hjc
        have h1 := chunk_mem_below hjc
        have h2 := chunk_mem_below hjc'
        have hcc' : c ≠ c' := fun h => hcnotin (h.symm ▸ hc'in)
        have hca := hanchor c List.mem_cons_self
        have hc'a := hanchor c' (List.mem_cons_of_mem c hc'in)
        rcases h1 with rfl | hb1
        · rcases h2 with rfl | hb2
          · exact hcc' rfl
          · exact not_below_sibling hwf huniq hca hc'a hb2
        · rcases h2 with rfl | hb2
          · exact not_below_sibling hwf huniq hc'a hca hb1
          · exact below_sibling_disjoint hwf huniq hca hc'a hcc' j hb1 hb2
      rw [List.count_eq_zero_of_not_mem hnot]
      omega

/-- Every id is emitted at most once, from any anchor, at any fuel — the
duplicate-freedom half of exactly-once. -/
theorem linearizeAux_count_le_one {n : Nat} {s : SeqState} (hwf : WF n s)
    (huniq : UniqueAnchor s) :
    ∀ fuel a j, (linearizeAux n s fuel a).count j ≤ 1 := by
  intro fuel
  induction fuel with
  | zero => intro a j; simp [linearizeAux]
  | succ fuel ih =>
    intro a j
    simp only [linearizeAux]
    exact count_flatMap_le_one hwf huniq ih (children n s a)
      (children_nodup n s a) (fun c hc => (mem_children.mp hc).2) j

/-- **Exactly-once (general, under `WF` and `UniqueAnchor`)**: every present
element appears exactly once in the linearization. `UniqueAnchor` is genuinely
needed — see `dup_id_appears_twice` — and is itself not merge-stable
(`wf_unique_anchor_not_iconfluent`); a content-addressed id scheme supplies it
cryptographically, outside this model. -/
theorem linearize_count_one {n : Nat} {s : SeqState} (hwf : WF n s)
    (huniq : UniqueAnchor s) {i a : Nat} (h : s (i, a) = true) :
    (linearize n s).count i = 1 := by
  have h1 : 0 < (linearize n s).count i :=
    List.count_pos_iff.mpr (linearize_mem hwf h)
  have h2 : (linearize n s).count i ≤ 1 :=
    linearizeAux_count_le_one hwf huniq n 0 i
  omega

/-- ⚠ **Without `UniqueAnchor`, a well-formed merge duplicates.** The same
pair that refutes I-confluence of `WF ∧ UniqueAnchor` merges to a state that
is still `WF` (by `wf_iconfluent`) but linearizes element 2 *twice* — once
under each of its anchors. Duplication of visible text is the concrete cost of
losing anchor uniqueness. -/
theorem dup_id_appears_twice :
    WF 5 (dupX ⊔ dupY) ∧ linearize 5 (dupX ⊔ dupY) = [2, 1, 2] :=
  ⟨wf_iconfluent 5 dupX dupY dupX_wf dupY_wf, by decide⟩

/-! ## §5. The anchor appears before its element -/

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

/-- Inside any subtree emission that contains an element's anchor chain, the
anchor is emitted and the element follows it. -/
theorem below_anchor_sublist {n : Nat} {s : SeqState} (hwf : WF n s) :
    ∀ fuel anchor a i, n - anchor ≤ fuel → s (i, a) = true →
      Below s anchor a → [a, i].Sublist (linearizeAux n s fuel anchor) := by
  intro fuel
  induction fuel with
  | zero =>
    intro anchor a i hfuel _ hb
    exact absurd (hb.anchor_lt_n hwf) (by omega)
  | succ fuel ih =>
    intro anchor a i hfuel hia hb
    simp only [linearizeAux]
    cases hb with
    | child ha =>
      have hi : i ∈ linearizeAux n s fuel a := by
        apply below_mem hwf fuel a i (Below.child hia)
        have := (hwf _ _ ha).2.1
        omega
      exact ((List.singleton_sublist.mpr hi).cons_cons a).trans
        (sublist_flatMap_of_mem (fun c => c :: linearizeAux n s fuel c)
          (children n s anchor) a (mem_children.mpr ⟨(hwf _ _ ha).1, ha⟩))
    | step hc hbelow =>
      have hsub := ih _ a i (by have := (hwf _ _ hc).2.1; omega) hia hbelow
      exact (hsub.cons _).trans
        (sublist_flatMap_of_mem (fun c => c :: linearizeAux n s fuel c)
          (children n s anchor) _ (mem_children.mpr ⟨(hwf _ _ hc).1, hc⟩))

/-- **Anchor-precedes (general, `WF` only)**: an element's non-root anchor
appears somewhere before the element in the linearization —
`[a, i]` is an (order-preserving, not necessarily contiguous) subsequence of
the output. -/
theorem linearize_anchor_precedes {n : Nat} {s : SeqState} (hwf : WF n s)
    {i a : Nat} (h : s (i, a) = true) (ha : a ≠ 0) :
    [a, i].Sublist (linearize n s) := by
  obtain ⟨-, -, h0 | ⟨b, hb⟩⟩ := hwf i a h
  · exact absurd h0 ha
  · exact below_anchor_sublist hwf n 0 a i (by omega) h (below_root hwf a b hb)

/-! ## §6. The interleaving anomaly — the honesty centerpiece

Kleppmann–Gomes–Mulligan–Beresford, "Interleaving anomalies in collaborative
text editors" (PaPoC 2019;
`/Users/ember/paperbin/uweave/kleppmann-interleaving-anomalies.pdf`): a
convergent sequence CRDT can converge to a text neither user wrote. Two shapes
of it hold in this miniature, both proved by computing the actual merged
linearizations. -/

/-- Replica X of the head-insert pair: elements 1 and 3, both anchored at the
root — the "insert repeatedly at the top of the document" pattern (a bullet
list built top-down, a log written newest-first). Locally reads `[3, 1]`. -/
def headX : SeqState := fun p => p == ((1 : Nat), (0 : Nat)) || p == ((3 : Nat), (0 : Nat))

/-- Replica Y of the head-insert pair: elements 2 and 4, both at the root.
Locally reads `[4, 2]`. -/
def headY : SeqState := fun p => p == ((2 : Nat), (0 : Nat)) || p == ((4 : Nat), (0 : Nat))

theorem headX_wf : WF 5 headX := by
  intro i a h
  simp [headX] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by omega, by omega, Or.inl rfl⟩
  · exact ⟨by omega, by omega, Or.inl rfl⟩

theorem headY_wf : WF 5 headY := by
  intro i a h
  simp [headY] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by omega, by omega, Or.inl rfl⟩
  · exact ⟨by omega, by omega, Or.inl rfl⟩

/-- ⚠ **The interleaving anomaly, concretely.** Each replica's two-element run
is contiguous on its own screen (`[3, 1]` and `[4, 2]`); both replicas are
well-formed; the merge is well-formed (`wf_iconfluent`); and the merged
document is `[4, 3, 2, 1]` — the two runs **strictly alternated**, an order
neither user ever saw. Convergence held; the text is garbage. This is exactly
what the naive anchor order does *not* guarantee, and no theorem in this file
claims otherwise. -/
theorem interleaving_anomaly :
    WF 5 headX ∧ WF 5 headY ∧ WF 5 (headX ⊔ headY)
    ∧ linearize 5 headX = [3, 1]
    ∧ linearize 5 headY = [4, 2]
    ∧ linearize 5 (headX ⊔ headY) = [4, 3, 2, 1] :=
  ⟨headX_wf, headY_wf, wf_iconfluent 5 headX headY headX_wf headY_wf,
   by decide, by decide, by decide⟩

/-- The merged head-insert state keeps unique anchors (everything is anchored
at the root, each id once) … -/
theorem merged_head_unique : UniqueAnchor (headX ⊔ headY) := by
  intro i a a' h h'
  have h1 : (headX (i, a) || headY (i, a)) = true := h
  have h2 : (headX (i, a') || headY (i, a')) = true := h'
  simp [headX, headY] at h1 h2
  omega

/-- … so the general exactly-once theorem fires on the anomalous merge: every
element of the interleaved document appears exactly once. The anomaly is not a
bug in the machinery — every structural theorem holds *on* it; what fails is
only the unformalized thing, intention. -/
theorem merged_head_exactly_once {i a : Nat}
    (h : (headX ⊔ headY) (i, a) = true) :
    (linearize 5 (headX ⊔ headY)).count i = 1 :=
  linearize_count_one (wf_iconfluent 5 headX headY headX_wf headY_wf)
    merged_head_unique h

/-- Replica A of the run pair: the run "ab" — element 1 at the root, element 2
anchored to 1. Locally reads `[1, 2]`. -/
def runA : SeqState := fun p => p == ((1 : Nat), (0 : Nat)) || p == ((2 : Nat), (1 : Nat))

/-- Replica B of the run pair: the run "cd" — element 3 at the root, element 4
anchored to 3. Locally reads `[3, 4]`. -/
def runB : SeqState := fun p => p == ((3 : Nat), (0 : Nat)) || p == ((4 : Nat), (3 : Nat))

theorem runA_wf : WF 5 runA := by
  intro i a h
  simp [runA] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by omega, by omega, Or.inl rfl⟩
  · exact ⟨by omega, by omega, Or.inr ⟨0, by decide⟩⟩

theorem runB_wf : WF 5 runB := by
  intro i a h
  simp [runB] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by omega, by omega, Or.inl rfl⟩
  · exact ⟨by omega, by omega, Or.inr ⟨0, by decide⟩⟩

/-- ⚠ **Run order is id arbitration, not intention.** When each run is
anchored intra-run ("ab" as 1←2, "cd" as 3←4), this miniature happens to keep
each run contiguous — but the merged document is `[3, 4, 1, 2]`: the runs'
*relative order* is decided by comparing ids (3 > 1, newest run first),
which neither user chose and which reverses any reading in which A's text came
first. No general no-interleaving theorem is stated in this file, and
`interleaving_anomaly` shows none is available for the anchor order at large:
contiguity here is an artifact of this witness, not a guarantee. -/
theorem run_order_by_id :
    WF 5 runA ∧ WF 5 runB
    ∧ linearize 5 runA = [1, 2]
    ∧ linearize 5 runB = [3, 4]
    ∧ linearize 5 (runA ⊔ runB) = [3, 4, 1, 2] :=
  ⟨runA_wf, runB_wf, by decide, by decide, by decide⟩

end Uwueave.Sequence
