/-
# Uwueave.TextSummary — why a text CRDT ships its op set, as a theorem.

Every collaborative editor in the field replicates the **operations** and
derives the visible string from them. `rust/src/seq.rs` does it too: the crate
keeps a `BTreeMap` of content-addressed elements (union merge with
tombstone-OR), hands the dense id order to `SeqKernel.lean`'s
`uwueave_seq_kernel`, and computes `text()` fresh on every read. Nobody proves
why. The design is folklore — "you obviously cannot merge two strings" — and
folklore is exactly what this library exists to convert.

The tree now has the theory that answers it, built for counters and sets and
never pointed at text:

  * `JoinHom.lean`'s **fourth verdict** — is a computation incrementally
    mergeable *from its results*, or must it retain and replay source evidence?
    (`IncrementallyMergeable` against `RequiresEvidence`, characterised by
    `incrementallyMergeable_iff_resultDetermined`.)
  * `MinimalSummary.lean`'s **contextual equivalence** — the coarsest summary
    that still answers a query after every future merge, with a universal
    property (`ctxQuot_coarsest_sufficient`).

This file points both at the sequence view of `Sequence.lean` and the tombstoned
kernel shape of `SeqKernel.lean`. The answers:

  1. **Text is `needsEvidence`** (`text_verdict`), and the impossibility is over
     every combiner, not over a chosen one.
  2. **Tombstones are load-bearing** (`tombstones_are_load_bearing`,
     `no_gc_summary_sufficient`) — and their *content* is not
     (`tombstoned_content_never_read`), which is exactly the split shipping
     implementations make by instinct.
  3. **The verdict does not depend on the order policy**
     (`verdict_order_policy_invariant`): Fugue's non-interleaving order, run
     through `Fugue.docOrder` itself, disagrees with RGA about the merged
     document and agrees with it about the verdict.

## §2 — the rendered string cannot be gossiped

Two replicas type the same letter. One mints the id `1`, the other the id `3` —
ids are content-addressed, so *where* a character sits in the arbitration order
is decided by a hash, and two replicas typing `a` mint different elements. A
peer types `b` as id `2`, between them. Both replicas render `a`; the peer
renders `b`; the merges render **`ba`** and **`ab`**.

`no_text_merge_without_provenance` turns that into an impossibility quantified
over *every* `m : List Glyph → List Glyph → List Glyph`, in the shape of
`JoinHom.no_count_merge_without_provenance`: the two scenarios present the same
pair of rendered documents and have different merged documents, so no function
of the pair is exact. `text_not_incrementallyMergeable` is the verdict,
`text_not_joinHom` rules out **every** lattice structure on rendered documents,
and `witnesses_wf` records that all four states and both merges are `Sequence.WF`
— the failure is not manufactured out of junk states.

This is the interleaving anomaly (`Sequence.interleaving_anomaly`) read as an
information-theoretic fact rather than a usability one: the rendered string has
discarded the ids, and the ids are what the merge arbitrates on.

§2.1 asks whether the *identified* view escapes — the document order as element
ids, strictly more information than the glyphs. It does not
(`linearize_not_joinHom`), and the witness is a second phenomenon: a replica
holding an op whose anchor has not arrived shows the empty document and merges
differently from a replica that is genuinely empty. ⚠ That witness is
model-level: `rust/src/seq.rs::merge` refuses an incoming state that is not
anchor-closed (`SeqMergeError::NotAnchorClosed`), so the crate keeps this
particular state out. §2's witnesses need no such caveat.

## §3 — the tombstone question, answered both ways

`SeqKernel.linearizeK` is `(emitAll anchor).filter (fun i => !deleted[i])`: the
traversal never takes the tombstone array, so a deleted element keeps its place
in the anchor forest. `visible` here is that composition at the model's scale.
So: may a replica drop a tombstone?

**No, and by a reachable separation.** A replica that typed a letter and deleted
it renders the same empty document as a replica that never typed anything, and
an ordinary peer that still holds the element separates them: the first renders
`b`, the second renders `ab` — the deleted character resurrected
(`tombstones_are_load_bearing`; every state involved is well-formed and
anchor-closed, i.e. accepted by the shipping merge). `no_gc_summary_sufficient`
is the general form, shaped after
`MinimalSummary.no_count_derived_summary_sufficient`: **no summary computed from
the live elements is sufficient**, for any target type and any post-processing.
`tombstone_anchoring_separation` isolates the anchoring half — a bare child op
anchored to the deleted element, placed by the tombstoned replica and dropped by
the collected one — with the reachability caveat attached to it rather than to
the headline. `tombstone_identity_is_load_bearing` adds that *which* element was
tombstoned is consulted too.

**But the content may go.** `tombstoned_content_never_read` proves that any two
labellings agreeing off the tombstoned ids render every future merge
identically: once an id is tombstoned it can never be visible again, so the
character attached to it is dead weight. That is the one thing the coarsest
sufficient summary of a text replica may throw away, and it is precisely what
real implementations throw away — deleted characters, never position markers.

## §5 — what the quotient actually collapses

The op set is sufficient for free (`opset_sufficient`, i.e. `sufficient_id`).
`MinimalSummary` makes the sharper question askable: is it *wastefully*
sufficient? For membership the quotient was one bit; for an exact count it was
the whole carrier; for a threshold, five classes. For text, measured here:

  * `ctxEquiv_iff_agree_window` — states are contextually equivalent exactly
    when they agree on every **addressable** op (element and anchor both inside
    the id window). The converse needs no well-formedness or unique-parent
    premise: `saturatedExcept_observable` proves that even a maximally malformed
    multi-parent context exposes any omitted addressable edge.
  * `collapse_out_of_window` — so the quotient is **not** discrete: an element
    beyond the window, or one anchored beyond it, is invisible forever.
  * `addressable_op_observable` — the earlier concrete separation remains: for
    every op the well-formedness discipline admits, the state holding it is
    separated from the state holding nothing, by the root when the anchor is the
    root and by the context that delivers the anchor otherwise.
  * `no_op_is_globally_invisible` — every op is addressable at some bound, so
    the collapse is an artifact of a query that fixes `n`, which is
    `MinimalSummary`'s "one query at a time" boundary in concrete form.

**Text retains everything it can name.** It sits at the `card` pole of
`MinimalSummary` §5, not the threshold pole of §6 — and the practical reading is
that a text replica's coarsest sufficient summary is its op set, which is what
the crate ships.

## §4 — the architecture, and why it is not a preference

`text_architecture_is_forced` is the pair: `ReplicatesEvidence (text 5)` holds
for **every** interpreter with no hypothesis at all
(`JoinHom.evidence_architecture_is_free`), and `RequiresEvidence (text 5)` says
the alternative is impossible. `text_view_sec` is `Move.derived_view_sec` at the
glyphs the user sees — the same derived-view pattern as
`Sequence.sequence_view_sec` and `ExecRefine.kernel_derived_view_sec`, one view
further out. What is new is not the pattern but its *necessity*: the pattern is
used everywhere in this library because it is free, and here the alternative is
refuted, for the view the crate actually ships. And
`text_ctxQuot_fold_answers` records that the positive
half still holds — shipping contextual-equivalence classes and folding them
works, with no hypothesis, because the class map is always a join homomorphism.

## Honest boundary

  * **Content is a global labelling, not a field of the op.** ⟨TERMINAL for the
    refutations, ⟨UNDONE U-0142⟩ as a model⟩ `glyph : Nat → Glyph` is faithful exactly
    because ids are content-addressed in the crate (`blake3("uwueave.seq.v1" ‖
    anchor ‖ contents)`), so an id determines its character; what it drops is two
    ops disagreeing about one id's content, which the crate's identity scheme
    forbids as well. The cost is visible in `tombstoned_content_never_read`,
    which is therefore stated over *labellings* rather than as a `CtxEquiv`
    collapse: content is not in the carrier, so the quotient cannot be asked
    about it directly.
  * **This is the model, not the kernel.** ⟨UNDONE U-0143⟩ `visible` is
    `Sequence.linearize` plus an output filter — `linearizeK`'s shape, one line
    apart, and deliberately so — but there are no arrays, no byte codec, no
    `SeqKernel.WFK` rank discipline, and no storage economics. A separation
    proved here is a separation about the abstract model; the kernel's agreement
    with the model is `SeqKernel.lean`'s business and is by construction only
    where that file says so.
  * **Contexts are unrestricted, and causal stability is not modelled.**
    ⟨UNDONE U-0144⟩ `CtxEquiv`'s `∀ z` ranges over every state, including ones the
    shipping merge refuses. So `no_gc_summary_sufficient` proves garbage
    collection unsound **on local state alone**; it does not prove GC
    impossible. The real escape — knowing no future op can name the element
    (causal stability, Baquero–Almeida–Shoker's compaction condition) — is a
    restriction on the set of contexts, and nothing here provides or refutes
    one. Naming that as the missing hypothesis is the content of this bullet.
  * **The addressable window is exact.** ⟨TERMINAL⟩
    `ctxEquiv_iff_agree_window` proves the full claim: any two states differing
    at an addressable pair are contextually distinguishable. The proof audits
    the model's malformed corner rather than assuming it away — saturation
    violates both `WF` and `UniqueAnchor`, yet omitting one edge changes the
    traversal. Thus the quotient drops exactly pairs outside the fixed window.
  * **Fugue is entered through a wrapper.** ⟨UNDONE U-0145⟩ `Fugue.docOrder` is called
    for real, but `Fugue.OpSet` is a `List InsOp` merged by append — associative,
    not commutative, not idempotent, hence not a `MergeState` — so §6 uses
    `GSet InsOp` materialised in a canonical enumeration order, and filters the
    dense id space down to minted elements (`Fugue.lean` treats every in-range
    index as an element). The *verdict* transfers through
    `rendered_order_requiresEvidence`, which knows nothing about any of that;
    the *witness computation* depends on the wrapper.
  * **Small carriers.** ⟨TERMINAL for the refutations⟩ Three glyphs, bound `5`
    (RGA) and `4` (Fugue). The general results — `ctxEquiv_iff_agree_window`,
    `addressable_op_observable`, `tombstoned_content_never_read`,
    `rendered_order_requiresEvidence`, `text_view_sec` — carry no carrier
    assumption.
  * **No cost model, no representation, no classifier.** ⟨UNDONE U-0146⟩ Inherited
    verbatim from `JoinHom.lean` and `MinimalSummary.lean`: `IncrementallyMergeable`
    asks only that a combiner exist, `CtxQuot` is a partition with no bound on
    the bits a class takes, and the verdict is proved per computation by hand
    because there is no syntax to recurse over.
  * **Nothing here says RGA is the right order.** `Sequence.run_order_by_id`'s
    caveat stands: sibling order is arbitration no user chose. §6 is the
    statement that choosing better does not make the string shippable.

Literature: Kleppmann–Gomes–Mulligan–Beresford (PaPoC 2019) for the anomaly the
§2 witness is a miniature of; Weidner–Kleppmann's Fugue for §6's order;
Shapiro et al. for the requirement that a derived value be computed by a lattice
morphism — which §2 shows the rendered text cannot be; Baquero–Almeida–Shoker's
pure-op CRDTs for the PO-Log and for causal-stable compaction, the named
hypothesis §3's boundary is missing; and, through `MinimalSummary`, Myhill–Nerode
with merge-contexts in place of word suffixes. All in `docs/BIBLIOGRAPHY.md`.
-/
import Uwueave.MinimalSummary
import Uwueave.Sequence
import Uwueave.Fugue

namespace Uwueave.TextSummary

open Uwueave Uwueave.Catalog Uwueave.Sequence

/-! ## §1. The carrier: an op set, and the three views a replica could ship. -/

/-- A three-letter alphabet. Character content, at miniature scale. -/
inductive Glyph where
  /-- the letter `a` -/
  | a
  /-- the letter `b` -/
  | b
  /-- the letter `c` -/
  | c
  deriving DecidableEq, Repr

/-- The content of an element, as a function of its id. -/
def glyph : Nat → Glyph
  | 2 => .b
  | 4 => .c
  | _ => .a

/-- **The replicated state**: the grow-only set of insertions (`Sequence.SeqState`
— `(i, a)` means "element `i` was inserted after anchor `a`") paired with the
grow-only set of tombstoned ids. -/
abbrev TState := SeqState × GSet Nat

example : MergeState TState := inferInstance

/-- The op "insert element `i` after anchor `a`". -/
def ins (i a : Nat) : TState := (fun p => p == (i, a), fun _ => false)

/-- The op "delete element `i`" — a tombstone, never a removal. -/
def del (i : Nat) : TState := (fun _ => false, fun j => j == i)

/-- The empty replica. -/
def noOps : TState := (fun _ => false, fun _ => false)

/-- **The document order**, tombstones included. -/
def doc (n : Nat) (p : TState) : List Nat := linearize n p.1

/-- **The visible linearization**: the document order with tombstoned elements
filtered out of the output only. -/
def visible (n : Nat) (p : TState) : List Nat :=
  (doc n p).filter (fun i => !(p.2 i))

/-- **The rendered text** — what the user sees, and the thing an editor is
tempted to gossip. -/
def text (n : Nat) (p : TState) : List Glyph := (visible n p).map glyph

/-! ## §2. The rendered text is not shippable. -/

/-- The replica that typed `a`, minting the low id `1`. -/
def typedALow : TState := ins 1 0

/-- A different replica that typed the same letter `a`, minting the id `3`. -/
def typedAHigh : TState := ins 3 0

/-- The peer that typed `b`, minting the id `2` — between the two. -/
def typedBMid : TState := ins 2 0

theorem typedALow_text : text 5 typedALow = [Glyph.a] := by decide

theorem typedAHigh_text : text 5 typedAHigh = [Glyph.a] := by decide

theorem typedBMid_text : text 5 typedBMid = [Glyph.b] := by decide

theorem low_merge_text : text 5 (typedALow ⊔ typedBMid) = [Glyph.b, Glyph.a] := by decide

theorem high_merge_text : text 5 (typedAHigh ⊔ typedBMid) = [Glyph.a, Glyph.b] := by decide

theorem typedALow_wf : WF 5 typedALow.1 := by
  intro i a h
  simp [typedALow, ins] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨by omega, by omega, Or.inl rfl⟩

theorem typedAHigh_wf : WF 5 typedAHigh.1 := by
  intro i a h
  simp [typedAHigh, ins] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨by omega, by omega, Or.inl rfl⟩

theorem typedBMid_wf : WF 5 typedBMid.1 := by
  intro i a h
  simp [typedBMid, ins] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨by omega, by omega, Or.inl rfl⟩

/-- The witnesses are legal states, and so are their merges. -/
theorem witnesses_wf :
    WF 5 typedALow.1 ∧ WF 5 typedAHigh.1 ∧ WF 5 typedBMid.1
      ∧ WF 5 (typedALow ⊔ typedBMid).1 ∧ WF 5 (typedAHigh ⊔ typedBMid).1 :=
  ⟨typedALow_wf, typedAHigh_wf, typedBMid_wf,
   wf_iconfluent 5 _ _ typedALow_wf typedBMid_wf,
   wf_iconfluent 5 _ _ typedAHigh_wf typedBMid_wf⟩

/-- ⚠ **THE IMPOSSIBILITY. No combiner on rendered text is exact.** For *every*
candidate `m : List Glyph → List Glyph → List Glyph`, here are two scenarios
whose replicas render pairwise-identical text and whose merges render
differently, at least one of which `m` gets wrong. -/
theorem no_text_merge_without_provenance (m : List Glyph → List Glyph → List Glyph) :
    ∃ x₁ y₁ x₂ y₂ : TState,
      text 5 x₁ = text 5 x₂ ∧ text 5 y₁ = text 5 y₂
        ∧ text 5 (x₁ ⊔ y₁) ≠ text 5 (x₂ ⊔ y₂)
        ∧ ¬ (m (text 5 x₁) (text 5 y₁) = text 5 (x₁ ⊔ y₁)
              ∧ m (text 5 x₂) (text 5 y₂) = text 5 (x₂ ⊔ y₂)) := by
  refine ⟨typedALow, typedBMid, typedAHigh, typedBMid, by decide, rfl, by decide, ?_⟩
  intro hcon
  have h1 := hcon.1
  have h2 := hcon.2
  rw [show text 5 typedAHigh = text 5 typedALow from by decide] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- ⚠ **TEXT REQUIRES EVIDENCE.** The rendered view is not incrementally
mergeable: no binary combiner on the two rendered documents computes the merged
document. -/
theorem text_not_incrementallyMergeable : ¬ IncrementallyMergeable (text 5) := by
  intro h
  obtain ⟨m, hm⟩ := h
  obtain ⟨x₁, y₁, x₂, y₂, _, _, _, hbad⟩ := no_text_merge_without_provenance m
  exact hbad ⟨(hm x₁ y₁).symm, (hm x₂ y₂).symm⟩

/-- The same fact in the vocabulary the characterisation uses: the merged
rendered text is **not** a function of the two rendered texts. -/
theorem text_not_resultDetermined : ¬ ResultDetermined (text 5) :=
  fun h => text_not_incrementallyMergeable
    (incrementallyMergeable_of_resultDetermined h)

/-- ⚠ **No lattice on rendered documents makes rendering a join homomorphism** —
the quantifier ranges over every `MergeState` structure whatsoever on
`List Glyph`, so this is not a complaint about a particular choice of join. -/
theorem text_not_joinHom (inst : MergeState (List Glyph)) :
    ¬ @JoinHom TState (List Glyph) _ inst (text 5) :=
  fun h => text_not_incrementallyMergeable
    (@joinHom_incrementallyMergeable TState (List Glyph) _ inst _ h)

/-! ### §2.1 Even the id order is not shippable — the causally pending op.

The rendered text has forgotten the ids, and §2 turns that into an
impossibility. One might hope the *identified* view — the document order as a
list of element ids, strictly more information than the glyphs — escapes. It
does not, and the witness is a different phenomenon: an op whose anchor has not
arrived is invisible **now** and decisive **later**. -/

/-- A replica holding an op whose anchor has not arrived: element `3` was
inserted after element `2`, and element `2` is not here. Ordinary out-of-causal-
order delivery, and (deliberately) not `WF`: `Sequence.WF` demands the anchor be
present, which is exactly the condition a buffering replica is waiting for. -/
def pendingChild : SeqState := (ins 3 2).1

/-- The replica that has received nothing. -/
def emptyDoc : SeqState := noOps.1

/-- The context in which the missing anchor arrives. -/
def anchorArrives : SeqState := (ins 2 0).1

theorem pending_invisible : linearize 5 pendingChild = [] := by decide

theorem empty_invisible : linearize 5 emptyDoc = [] := by decide

theorem pending_merge : linearize 5 (pendingChild ⊔ anchorArrives) = [2, 3] := by decide

theorem empty_merge : linearize 5 (emptyDoc ⊔ anchorArrives) = [2] := by decide

/-- ⚠ **The merged document order is not a function of the two document
orders.** Two replicas display the empty document; one of them is holding a
pending op; the same delivery lands `[2, 3]` on one and `[2]` on the other. -/
theorem linearize_not_resultDetermined : ¬ ResultDetermined (linearize 5) := fun h =>
  absurd (h pendingChild anchorArrives emptyDoc anchorArrives (by decide) rfl) (by decide)

/-- ⚠ **The identified document order requires evidence too.** -/
theorem linearize_not_incrementallyMergeable : ¬ IncrementallyMergeable (linearize 5) :=
  fun h => linearize_not_resultDetermined (resultDetermined_of_incrementallyMergeable h)

/-- ⚠ **`Sequence.linearize` is not a join homomorphism** — for any lattice
whatsoever on document orders. This is the headline question asked of the
sequence view, answered in the negative in the strongest available form: not
"not for the obvious join", but "not for any join". -/
theorem linearize_not_joinHom (inst : MergeState (List Nat)) :
    ¬ @JoinHom SeqState (List Nat) _ inst (linearize 5) :=
  fun h => linearize_not_incrementallyMergeable
    (@joinHom_incrementallyMergeable SeqState (List Nat) _ inst _ h)

/-! ## §3. Tombstones are load-bearing — and their content is not.

`SeqKernel.linearizeK` is `(emitAll anchor).filter (fun i => !deleted[i])`: the
traversal never sees the tombstone array, so a deleted element keeps its place
in the anchor forest and stays anchorable. `visible` above is that composition
at this scale. The design question every text CRDT answers by folklore — *may a
replica drop a tombstone?* — is a contextual-equivalence question, and it has an
answer. -/

/-- A replica that typed `a` and then deleted it: one insertion, one tombstone.
Renders the empty document. -/
def deletedOne : TState := ins 1 0 ⊔ del 1

/-- A replica that never typed anything. Also renders the empty document. -/
def neverTyped : TState := noOps

/-- **The separating context**: a peer that received element `1`, kept it, and
typed `b` after it. Anchor-closed — element `2`'s anchor travels with it — so
this is a state `rust/src/seq.rs::merge` accepts (it refuses incoming states
that are not anchor-closed, `SeqMergeError::NotAnchorClosed`). -/
def peerWithElement : TState := ins 1 0 ⊔ ins 2 1

/-- The same context stripped to the child op alone: a delta that names an
element the receiver may no longer hold. Sharper as a separation — it isolates
the anchoring, with no re-delivery of the element — and, unlike
`peerWithElement`, it is a state the shipping merge refuses. -/
def childOfTheDead : TState := ins 2 1

theorem deletedOne_text : text 5 deletedOne = [] := by decide

theorem neverTyped_text : text 5 neverTyped = [] := by decide

theorem deletedOne_peer_text : text 5 (deletedOne ⊔ peerWithElement) = [Glyph.b] := by
  decide

theorem neverTyped_peer_text :
    text 5 (neverTyped ⊔ peerWithElement) = [Glyph.a, Glyph.b] := by decide

theorem deletedOne_ctx_text : text 5 (deletedOne ⊔ childOfTheDead) = [Glyph.b] := by decide

theorem neverTyped_ctx_text : text 5 (neverTyped ⊔ childOfTheDead) = [] := by decide

/-- ⚠ **TOMBSTONES ARE LOAD-BEARING.** Two states that render the same empty
document — one holding a tombstone, one holding nothing — are **not**
contextually equivalent for the rendered text. The separating context is an
ordinary peer that still holds the element: the replica that kept its tombstone
renders `b`, the replica that dropped it renders `ab`, the deleted character
back on the screen. Dropping a tombstone is therefore not a summary of the
state; it is a loss of evidence the query will need.

Every state here is well-formed and anchor-closed, so the separation survives
the reachability question `TRANSPORTS` row 2 insists on: this is not a
lattice-only pair. -/
theorem tombstones_are_load_bearing :
    text 5 deletedOne = text 5 neverTyped
      ∧ text 5 (deletedOne ⊔ peerWithElement) ≠ text 5 (neverTyped ⊔ peerWithElement)
      ∧ ¬ CtxEquiv (text 5) deletedOne neverTyped :=
  ⟨by decide, by decide, fun h => absurd (h.2 peerWithElement) (by decide)⟩

/-- ⚠ **The anchoring half, isolated.** With the bare child op as context —
nothing re-delivered, only a new element anchored to the deleted one — the
tombstoned replica places the new character and the garbage-collected replica
drops it on the floor. This is the separation `SeqKernel.linearizeK`'s design
note is about ("tombstones are excluded from the output but not from the
traversal"), and it is the one that survives even if re-delivery is ruled out.

⚠ Read with the reachability caveat: `rust/src/seq.rs::merge` **refuses** an
incoming state that is not anchor-closed, so this exact context is a delta the
shipping API rejects. The refusal is the crate enforcing the very hypothesis
this theorem shows is load-bearing — and `tombstones_are_load_bearing` above
makes the same point with a context the crate accepts. -/
theorem tombstone_anchoring_separation :
    text 5 (deletedOne ⊔ childOfTheDead) ≠ text 5 (neverTyped ⊔ childOfTheDead)
      ∧ ¬ CtxEquiv (text 5) deletedOne neverTyped :=
  ⟨by decide, fun h => absurd (h.2 childOfTheDead) (by decide)⟩

/-- The same separation on the identified view, for the record: the merged
document orders are `[2]` and `[]`. -/
theorem tombstones_are_load_bearing_for_doc :
    ¬ CtxEquiv (doc 5) deletedOne neverTyped :=
  fun h => absurd (h.2 childOfTheDead) (by decide)

/-- The window of element ids this miniature can address. -/
def window (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (fun i => (List.range n).map (fun a => (i, a)))

/-- **What a garbage-collecting replica keeps**: the live insertions — every
element that is present and not tombstoned, with its anchor — and nothing else.
The tombstones themselves are gone; that is what GC means. -/
def garbageCollected (n : Nat) (p : TState) : List (Nat × Nat) :=
  (window n).filter (fun q => p.1 q && !(p.2 q.1))

theorem gc_forgets : garbageCollected 5 deletedOne = garbageCollected 5 neverTyped := by
  decide

/-- ⚠ **NO SUMMARY COMPUTED FROM THE LIVE ELEMENTS IS SUFFICIENT** — for any
target type and any post-processing `k`. This is the formal content of the
design decision every sequence CRDT makes and none proves: you may not garbage
collect a tombstone, because the state that results is contextually
distinguishable from the state that never held the element, and no function of
the live elements can tell those apart.

Shaped after `MinimalSummary.no_count_derived_summary_sufficient`: it ranges
over *coarsenings*, not over combiners, and needs no hypothesis on `g`. -/
theorem no_gc_summary_sufficient {T : Type} (g : TState → T)
    (hfac : ∃ k : List (Nat × Nat) → T, ∀ s, g s = k (garbageCollected 5 s)) :
    ¬ Sufficient g (text 5) := by
  intro hsuf
  obtain ⟨k, hk⟩ := hfac
  have heq : g deletedOne = g neverTyped := by rw [hk, hk, gc_forgets]
  exact tombstones_are_load_bearing.2.2 (hsuf deletedOne neverTyped heq)

/-- ⚠ **Which element is tombstoned matters too**, not merely that one is.
Two replicas each typed one letter and deleted it; both render the empty
document; they minted different ids. A peer that anchored to id `1` sees its
own letter in one merge and nothing in the other — the tombstone's *identity*
is consulted by every future anchoring. -/
theorem tombstone_identity_is_load_bearing :
    text 5 (ins 1 0 ⊔ del 1) = text 5 (ins 3 0 ⊔ del 3)
      ∧ ¬ CtxEquiv (text 5) (ins 1 0 ⊔ del 1) (ins 3 0 ⊔ del 3) :=
  ⟨by decide, fun h => absurd (h.2 (ins 4 1)) (by decide)⟩

/-- **And what a tombstone need NOT keep: its content.** Once an id is
tombstoned, no context can make it visible again — tombstones are grow-only and
`visible` filters on the merged tombstone set — so the glyph attached to it is
never read again. Stated over labellings: any two content maps agreeing off the
tombstoned ids render every future merge identically.

This is the one thing the coarsest sufficient summary of a text replica may
throw away, and it is exactly what shipping implementations throw away: the
deleted characters, never the position markers. -/
theorem tombstoned_content_never_read (n : Nat) (c c' : Nat → Glyph) (p : TState)
    (hagree : ∀ i, p.2 i = false → c i = c' i) (z : TState) :
    (visible n (p ⊔ z)).map c = (visible n (p ⊔ z)).map c' := by
  refine List.map_congr_left (fun i hi => ?_)
  have hmem : i ∈ doc n (p ⊔ z) ∧ (!((p ⊔ z).2 i)) = true := List.mem_filter.mp hi
  have hnot : (!((p ⊔ z).2 i)) = true := hmem.2
  have hvis : ((p ⊔ z).2 i) = false := by
    cases hd : (p ⊔ z).2 i with
    | false => rfl
    | true => rw [hd] at hnot; exact absurd hnot (by decide)
  have hp : p.2 i = false := by
    have : (p.2 i || z.2 i) = false := hvis
    cases hd : p.2 i with
    | false => rfl
    | true => rw [hd] at this; exact absurd this (by simp)
  exact hagree i hp

/-! ## §4. The fourth verdict, for text.

`JoinHom.lean` §6 asks of a computation over replicated state: *is it
incrementally mergeable from its results, or must it retain and replay source
evidence?* Images, high-water marks, existential reads and filtered views answer
`fromResults`; counting answers `needsEvidence`. Text answers `needsEvidence`,
and §2 is the proof. -/

/-- ⚠ **THE VERDICT: text is `needsEvidence`.** -/
theorem text_verdict : JoinHom.Fourth.Correct (text 5) JoinHom.Fourth.needsEvidence :=
  text_not_incrementallyMergeable

/-- ⚠ **And so is the identified document order** — the verdict is not an
artifact of erasing ids to glyphs. -/
theorem linearize_verdict :
    JoinHom.Fourth.Correct (linearize 5) JoinHom.Fourth.needsEvidence :=
  linearize_not_incrementallyMergeable

/-- The verdict in `MinimalSummary`'s vocabulary: the rendered text is not a
sufficient summary of itself. -/
theorem text_not_self_sufficient : ¬ Sufficient (text 5) (text 5) :=
  fun h => text_not_incrementallyMergeable
    ((selfSufficient_iff_incrementallyMergeable (text 5)).mp h)

/-- The op set **is** a sufficient summary — the trivial upper bound the whole
question is trying to improve on, and the one the crate ships. -/
theorem opset_sufficient : Sufficient (fun p : TState => p) (text 5) :=
  sufficient_id (text 5)

/-- **Architecture (i), for text, is free.** Replicate the op set and recompute
the view: delivery order and redelivery are unobservable in the rendered text,
for *every* interpreter, with no hypothesis at all — `Move.derived_view_sec`'s
clauses at `interp := text n`. This is `Sequence.sequence_view_sec` one view
further out, at the glyphs the user actually sees. -/
theorem text_view_sec (n : Nat) (base Δ₁ Δ₂ : TState) :
    text n ((base ⊔ Δ₁) ⊔ Δ₂) = text n ((base ⊔ Δ₂) ⊔ Δ₁)
      ∧ text n ((base ⊔ Δ₁) ⊔ Δ₁) = text n (base ⊔ Δ₁) :=
  let h := Move.derived_view_sec (text n) (fun _ => True) (fun _ => trivial) base Δ₁ Δ₂
  ⟨h.1, h.2.1⟩

/-- **Architecture (ii), for text, is impossible.** The pair is the whole point:
the left conjunct holds for every interpreter and needs no hypothesis, the right
one is an impossibility over every combiner. Gossiping ops and deriving the view
is therefore not a design preference of `rust/src/seq.rs`; it is the only
architecture available for this query. -/
theorem text_architecture_is_forced :
    JoinHom.ReplicatesEvidence (text 5) ∧ RequiresEvidence (text 5) :=
  ⟨JoinHom.evidence_architecture_is_free (text 5), text_not_incrementallyMergeable⟩

/-- **The coarsest sufficient summary exists and ships.** Contextual-equivalence
classes for the rendered text form a `MergeState`, the class map is a join
homomorphism, and folding shipped classes with the quotient's own join decodes
to the text of the merged evidence, for every gossip history — `MinimalSummary`'s
synthesis theorem instantiated at the text query. What §5 measures is how much
that quotient actually saves. -/
theorem text_ctxQuot_fold_answers (init : TState) (l : List TState) :
    text 5 (Delta.joinAll init l)
      = ctxAnswer (text 5) (Delta.joinAll (ctxMk (text 5) init) (l.map (ctxMk (text 5)))) :=
  ctxQuot_fold_answers (text 5) init l

/-! ## §5. What contextual equivalence collapses: the window, and nothing else.

The op set is sufficient for free (`opset_sufficient`). The question `MinimalSummary`
makes askable is whether it is *wastefully* sufficient — whether the coarsest
sufficient summary is strictly smaller. For the count it was not (the quotient is
the carrier); for a threshold it was (five classes over eight states). For text,
the answer is exact: `ctxEquiv_iff_agree_window` says the quotient identifies
precisely states that agree on every element/anchor pair inside the fixed id
window. No `WF` or `UniqueAnchor` premise is required. Text keeps exactly what
this query can name. -/

private theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem pair_beq {j b i a : Nat} (h : ((j, b) == (i, a)) = true) : j = i ∧ b = a := by
  have h2 : ((j == i) && (b == a)) = true := h
  have h3 := (Bool.and_eq_true _ _).mp h2
  exact ⟨eq_of_beq h3.1, eq_of_beq h3.2⟩

/-- Two states that agree on every **addressable** pair — both the element and
its anchor inside the id window — emit the same document order below any anchor
the window can reach. The traversal only ever reads pairs of that shape, and it
only ever descends into anchors of that shape. -/
theorem linearizeAux_congr_window {n : Nat} {s s' : SeqState}
    (h : ∀ i a, i < n → a < n → s (i, a) = s' (i, a)) :
    ∀ fuel a, a < n → linearizeAux n s fuel a = linearizeAux n s' fuel a := by
  intro fuel
  induction fuel with
  | zero => intro a _; rfl
  | succ fuel ih =>
    intro a ha
    simp only [linearizeAux]
    have hch : children n s a = children n s' a := by
      simp only [children]
      refine List.filter_congr (fun j hj => ?_)
      exact h j a (List.mem_range.mp (List.mem_reverse.mp hj)) ha
    rw [hch]
    exact flatMap_congr (fun c hc => by rw [ih c (mem_children.mp hc).1])

/-- The same, at the whole document. -/
theorem linearize_congr_window {n : Nat} {s s' : SeqState}
    (h : ∀ i a, i < n → a < n → s (i, a) = s' (i, a)) :
    linearize n s = linearize n s' := by
  cases n with
  | zero => rfl
  | succ m => exact linearizeAux_congr_window h (m + 1) 0 (Nat.succ_pos m)

/-- **The collapse, in general.** Agreement on the addressable window is enough
for contextual equivalence: a context can add ops, but it cannot enlarge the
window, so an unaddressable op stays unaddressable forever. -/
theorem ctxEquiv_of_agree_window {n : Nat} {s s' : SeqState}
    (h : ∀ i a, i < n → a < n → s (i, a) = s' (i, a)) :
    CtxEquiv (linearize n) s s' :=
  ctxEquiv_of_contexts (fun z => linearize_congr_window (fun i a hi ha => by
    show (s (i, a) || z (i, a)) = (s' (i, a) || z (i, a))
    rw [h i a hi ha]))

/-! The converse has to survive malformed states. A state may attach every id
to every anchor, including itself; `WF` and `UniqueAnchor` both fail maximally.
Such saturation is useful as a separating context: it masks every coordinate
except the one under test. The lemmas below prove that deleting that one edge
still strictly shortens the fuel-bounded traversal. Thus duplicate parents do
not create an accidental contextual collapse. -/

/-- The maximally saturated sequence state: every element/anchor pair is
present. It is deliberately malformed and violates unique-parent discipline. -/
def saturatedOps : SeqState := fun _ => true

/-- The saturated state with exactly one element/anchor pair omitted. -/
def saturatedExcept (i a : Nat) : SeqState := fun q => !(q == (i, a))

private theorem sum_map_le_pointwise {α : Type} {l : List α} {f g : α → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hx := h x List.mem_cons_self
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      omega

private theorem sum_map_filter_le_pointwise {α : Type} (l : List α)
    (p : α → Bool) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    ((l.filter p).map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      cases hp : p x <;> simp [hp] <;> omega

private theorem sum_map_filter_lt_of_omitted {α : Type} (l : List α)
    (p : α → Bool) (f g : α → Nat) (i : α) (hi : i ∈ l)
    (hpi : p i = false) (hle : ∀ x ∈ l, f x ≤ g x) (hpos : 0 < g i) :
    ((l.filter p).map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp at hi
  | cons x xs ih =>
      have hx := hle x List.mem_cons_self
      have hxs : ∀ y ∈ xs, f y ≤ g y :=
        fun y hy => hle y (List.mem_cons_of_mem _ hy)
      by_cases hxi : x = i
      · subst x
        have htail := sum_map_filter_le_pointwise xs p f g hxs
        simp [hpi]
        omega
      · have hit : i ∈ xs := (List.mem_cons.mp hi).resolve_left (Ne.symm hxi)
        have htail := ih hit hxs
        cases hp : p x <;> simp [hp] <;> omega

private theorem sum_map_lt_of_mem {α : Type} (l : List α) (f g : α → Nat)
    (i : α) (hi : i ∈ l) (hle : ∀ x ∈ l, f x ≤ g x)
    (hlt : f i < g i) : (l.map f).sum < (l.map g).sum := by
  induction l with
  | nil => simp at hi
  | cons x xs ih =>
      have hx := hle x List.mem_cons_self
      have hxs : ∀ y ∈ xs, f y ≤ g y :=
        fun y hy => hle y (List.mem_cons_of_mem _ hy)
      by_cases hxi : x = i
      · subst x
        have htail := sum_map_le_pointwise hxs
        simp
        omega
      · have hit : i ∈ xs := (List.mem_cons.mp hi).resolve_left (Ne.symm hxi)
        have htail := ih hit hxs
        simp
        omega

private theorem saturatedExcept_aux_length_le (n i a : Nat) :
    ∀ fuel b,
      (linearizeAux n (saturatedExcept i a) fuel b).length ≤
        (linearizeAux n saturatedOps fuel b).length := by
  intro fuel
  induction fuel with
  | zero => intro b; simp [linearizeAux]
  | succ fuel ih =>
      intro b
      simp only [linearizeAux, List.length_flatMap, List.length_cons]
      have hs : children n saturatedOps b = (List.range n).reverse := by
        simp [children, saturatedOps]
      rw [hs]
      simp only [children, saturatedExcept]
      apply sum_map_filter_le_pointwise
      intro c hc
      simp only [List.mem_reverse, List.mem_range] at hc
      have hrec := ih c
      omega

private theorem saturatedExcept_aux_target_lt {n i a fuel : Nat} (hi : i < n)
    (hfuel : 0 < fuel) :
    (linearizeAux n (saturatedExcept i a) fuel a).length <
      (linearizeAux n saturatedOps fuel a).length := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      simp only [linearizeAux, List.length_flatMap, List.length_cons]
      have hs : children n saturatedOps a = (List.range n).reverse := by
        simp [children, saturatedOps]
      rw [hs]
      simp only [children, saturatedExcept]
      apply sum_map_filter_lt_of_omitted _ _ _ _ i
      · simp [hi]
      · simp
      · intro c hc
        simp only [List.mem_reverse, List.mem_range] at hc
        have hrec := saturatedExcept_aux_length_le n i a fuel c
        omega
      · omega

/-- **Even maximally malformed multi-parent states expose every addressable
edge.** Removing one pair from the saturated state strictly changes
`linearize n`. If the anchor is the root, its nonempty child chunk disappears
there; otherwise the saturated root reaches the anchor directly, and the same
strict loss occurs one level down. All other recursive chunks can only shrink. -/
theorem saturatedExcept_observable {n i a : Nat} (hi : i < n) (ha : a < n) :
    linearize n saturatedOps ≠ linearize n (saturatedExcept i a) := by
  intro heq
  have hlen := congrArg List.length heq
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · exact (Nat.ne_of_lt
      (saturatedExcept_aux_target_lt hi (Nat.zero_lt_of_lt hi))) hlen.symm
  · cases n with
    | zero => omega
    | succ fuel =>
        have hfuel : 0 < fuel := by omega
        simp only [linearize, linearizeAux, List.length_flatMap,
          List.length_cons] at hlen
        have hs : children (fuel + 1) saturatedOps 0 =
            (List.range (fuel + 1)).reverse := by
          simp [children, saturatedOps]
        have hw : children (fuel + 1) (saturatedExcept i a) 0 =
            (List.range (fuel + 1)).reverse := by
          simp only [children, saturatedExcept]
          apply List.filter_eq_self.mpr
          intro c hc
          simp only [List.mem_reverse, List.mem_range] at hc
          cases hb : ((c, 0) == (i, a)) with
          | false => rfl
          | true =>
              have hp := pair_beq hb
              omega
        rw [hs, hw] at hlen
        have hstrict :
            (((List.range (fuel + 1)).reverse.map fun c =>
                (c :: linearizeAux (fuel + 1)
                  (saturatedExcept i a) fuel c).length).sum) <
              (((List.range (fuel + 1)).reverse.map fun c =>
                (c :: linearizeAux (fuel + 1) saturatedOps fuel c).length).sum) := by
          apply sum_map_lt_of_mem _ _ _ a
          · simp [ha]
          · intro c hc
            have hrec := saturatedExcept_aux_length_le (fuel + 1) i a fuel c
            simp only [List.length_cons]
            omega
          · simp only [List.length_cons]
            have htarget :=
              saturatedExcept_aux_target_lt (a := a) hi hfuel
            omega
        exact (Nat.ne_of_lt hstrict) hlen.symm

private theorem join_saturatedExcept_eq_saturated (s : SeqState) (i a : Nat)
    (h : s (i, a) = true) : s ⊔ saturatedExcept i a = saturatedOps := by
  funext q
  cases hb : (q == (i, a)) with
  | false =>
      change (s q || saturatedExcept i a q) = true
      simp [saturatedExcept, hb]
  | true =>
      have hq : q = (i, a) := eq_of_beq hb
      subst q
      change (s (i, a) || saturatedExcept i a (i, a)) = true
      simp [saturatedExcept, h]

private theorem join_saturatedExcept_eq_self (s : SeqState) (i a : Nat)
    (h : s (i, a) = false) : s ⊔ saturatedExcept i a = saturatedExcept i a := by
  funext q
  cases hb : (q == (i, a)) with
  | false =>
      change (s q || saturatedExcept i a q) = saturatedExcept i a q
      simp [saturatedExcept, hb]
  | true =>
      have hq : q = (i, a) := eq_of_beq hb
      subst q
      change (s (i, a) || saturatedExcept i a (i, a)) =
        saturatedExcept i a (i, a)
      simp [saturatedExcept, h]

/-- **The converse: contextual equivalence recovers every addressable pair.**
No `WF` or `UniqueAnchor` hypothesis is needed. Saturating every other pair as
the common context reduces a disagreement to `saturatedOps` against
`saturatedExcept`; `saturatedExcept_observable` separates those states even
though they are maximally malformed and multi-parent. -/
theorem agree_window_of_ctxEquiv {n : Nat} {s s' : SeqState}
    (hctx : CtxEquiv (linearize n) s s') :
    ∀ i a, i < n → a < n → s (i, a) = s' (i, a) := by
  intro i a hi ha
  have hz := hctx.2 (saturatedExcept i a)
  cases hs : s (i, a) <;> cases hs' : s' (i, a)
  · rfl
  · rw [join_saturatedExcept_eq_self s i a hs,
      join_saturatedExcept_eq_saturated s' i a hs'] at hz
    exact False.elim (saturatedExcept_observable hi ha hz.symm)
  · rw [join_saturatedExcept_eq_saturated s i a hs,
      join_saturatedExcept_eq_self s' i a hs'] at hz
    exact False.elim (saturatedExcept_observable hi ha hz)
  · rfl

/-- **Exact contextual equivalence for the addressable window.** Two sequence
states are contextually equivalent for `linearize n` exactly when they agree on
every pair whose element and anchor are both below `n`. This holds for arbitrary
states: well-formedness and unique-parent discipline are not hidden premises. -/
theorem ctxEquiv_iff_agree_window {n : Nat} {s s' : SeqState} :
    CtxEquiv (linearize n) s s' ↔
      ∀ i a, i < n → a < n → s (i, a) = s' (i, a) :=
  ⟨agree_window_of_ctxEquiv, ctxEquiv_of_agree_window⟩

/-- One op, as a state. -/
def single (i a : Nat) : SeqState := (ins i a).1

/-- An op the window cannot address: element `7` when the bound is `5`. -/
def outOfWindow : SeqState := single 7 0

/-- An op whose *anchor* the window cannot address: element `3` inserted after
element `7`, when the bound is `5`. -/
def anchorOutOfWindow : SeqState := single 3 7

/-- ⚠ **The quotient is not discrete**: two distinct states, contextually
equivalent for the document. Both witnesses are ops that no context can bring
into view — one because the element is outside the window, one because its
anchor is. -/
theorem collapse_out_of_window :
    (emptyDoc ≠ outOfWindow ∧ CtxEquiv (linearize 5) emptyDoc outOfWindow)
      ∧ (emptyDoc ≠ anchorOutOfWindow
          ∧ CtxEquiv (linearize 5) emptyDoc anchorOutOfWindow) := by
  refine ⟨⟨fun hc => absurd (congrFun hc ((7 : Nat), (0 : Nat))) (by decide), ?_⟩,
    ⟨fun hc => absurd (congrFun hc ((3 : Nat), (7 : Nat))) (by decide), ?_⟩⟩
  · refine ctxEquiv_of_agree_window (fun i a hi _ => ?_)
    show false = ((i, a) == ((7 : Nat), (0 : Nat)))
    cases hb : ((i, a) == ((7 : Nat), (0 : Nat))) with
    | false => rfl
    | true => exact absurd (pair_beq hb).1 (by omega)
  · refine ctxEquiv_of_agree_window (fun i a _ ha => ?_)
    show false = ((i, a) == ((3 : Nat), (7 : Nat)))
    cases hb : ((i, a) == ((3 : Nat), (7 : Nat))) with
    | false => rfl
    | true => exact absurd (pair_beq hb).2 (by omega)

theorem children_empty (n a : Nat) : children n emptyDoc a = [] := by
  simp [children, emptyDoc, noOps]

theorem linearize_empty (n : Nat) : linearize n emptyDoc = [] := by
  cases n with
  | zero => rfl
  | succ m =>
    show ((children (m + 1) emptyDoc 0).flatMap _) = []
    rw [children_empty]
    rfl

/-- Whatever a one-op state emits is that op's element. -/
theorem mem_single {n i a j : Nat} (hj : j ∈ linearize n (single i a)) : j = i := by
  obtain ⟨m, hm, -⟩ := (linearizeAux_below n 0 j hj).invert
  exact (pair_beq hm).1

theorem single_root_wf {n i : Nat} (hin : i < n) (hi0 : 0 < i) : WF n (single i 0) := by
  intro j b hmem
  obtain ⟨hj, hb⟩ := pair_beq hmem
  exact ⟨by omega, by omega, Or.inl hb⟩

theorem chain_wf {n i a : Nat} (hin : i < n) (hai : a < i) (ha0 : 0 < a) :
    WF n (single i a ⊔ single a 0) := by
  intro j b hmem
  have h' : (((j, b) == (i, a)) || ((j, b) == (a, 0))) = true := hmem
  rcases (Bool.or_eq_true _ _).mp h' with hc | hc
  · obtain ⟨hj, hb⟩ := pair_beq hc
    refine ⟨by omega, by omega, Or.inr ⟨0, ?_⟩⟩
    rw [hb]
    show (((a, 0) == (i, a)) || ((a, 0) == (a, 0))) = true
    simp
  · obtain ⟨hj, hb⟩ := pair_beq hc
    exact ⟨by omega, by omega, Or.inl hb⟩

/-- ⚠ **EVERY ADDRESSABLE OP IS OBSERVABLE.** For any op the well-formedness
discipline admits — element inside the window, anchor strictly older — the state
holding it is contextually distinguishable from the state holding nothing. When
the anchor is the root the op is visible immediately; otherwise the context that
delivers the anchor makes it visible.

This is the concrete one-op instance of `ctxEquiv_iff_agree_window`: the collapse
contains the unaddressable ops, and no addressable difference is collapsed.
Text keeps what it can ever name — unlike the threshold of `MinimalSummary` §6,
and closer to the exact count of §5 there. -/
theorem addressable_op_observable {n i a : Nat} (hin : i < n) (hai : a < i) :
    ¬ CtxEquiv (linearize n) emptyDoc (single i a) := by
  intro heq
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · have hmem : i ∈ linearize n (single i 0) :=
      linearize_mem (single_root_wf hin hai) (by show ((i, 0) == (i, 0)) = true; simp)
    rw [← heq.1, linearize_empty] at hmem
    exact absurd hmem (by simp)
  · have hctx := heq.2 (single a 0)
    have hleft : linearize n (emptyDoc ⊔ single a 0) = linearize n (single a 0) := rfl
    have hmem : i ∈ linearize n (single i a ⊔ single a 0) :=
      linearize_mem (chain_wf hin hai ha0)
        (by show (((i, a) == (i, a)) || ((i, a) == (a, 0))) = true; simp)
    rw [← hctx, hleft] at hmem
    exact absurd (mem_single hmem) (by omega)

/-- **The collapse is the fixed window, not the text.** Every op is observable
at some bound: the quotient of §5 loses information only because a *single*
query fixes `n`, which is `MinimalSummary`'s "one query at a time" boundary in
concrete form. A replica answering the document at every size it may grow to
distinguishes every op the discipline admits, and its coarsest sufficient
summary is the op set itself. -/
theorem no_op_is_globally_invisible (i a : Nat) (hai : a < i) :
    ∃ n, ¬ CtxEquiv (linearize n) emptyDoc (single i a) :=
  ⟨i + 1, addressable_op_observable (Nat.lt_succ_self i) hai⟩

/-! ## §6. The verdict is invariant under the order policy — the Fugue contrast.

`Fugue.lean` builds the design that targets the interleaving anomaly: a tree
order in which a replica's run is a chain of descendants, so two concurrent runs
cannot alternate. It changes *which* document the merge produces. The question
this file asks is about *information*, not order, so it should not change at all
— and it does not. Both halves are proved: one general lemma with the order
policy as a parameter, and the Fugue instance of it, computed through
`Fugue.docOrder` itself. -/

/-- **The verdict, for an arbitrary order policy.** On any replicated carrier,
any function from state to document order, and any labelling: a single witness
pair — two states whose rendered documents agree and whose merges with a common
context do not — forces `needsEvidence`. Nothing about anchoring, tie-breaking
or tree shape enters. -/
theorem rendered_order_requiresEvidence {S : Type} [MergeState S]
    (ord : S → List Nat) (lab : Nat → Glyph) {x₁ x₂ y : S}
    (hsame : (ord x₁).map lab = (ord x₂).map lab)
    (hsplit : (ord (x₁ ⊔ y)).map lab ≠ (ord (x₂ ⊔ y)).map lab) :
    RequiresEvidence (fun s => (ord s).map lab) := by
  intro hmerge
  obtain ⟨m, hm⟩ := hmerge
  refine hsplit ?_
  have e1 : (ord (x₁ ⊔ y)).map lab = m ((ord x₁).map lab) ((ord y).map lab) := hm x₁ y
  have e2 : (ord (x₂ ⊔ y)).map lab = m ((ord x₂).map lab) ((ord y).map lab) := hm x₂ y
  rw [e1, e2, hsame]

/-- The RGA verdict, re-derived from the policy-agnostic lemma at
`ord := visible 5`: §2's impossibility is an instance of it, so the two
statements are the same fact at two resolutions. -/
theorem text_requiresEvidence_by_policy : RequiresEvidence (text 5) :=
  rendered_order_requiresEvidence (visible 5) glyph
    (x₁ := typedALow) (x₂ := typedAHigh) (y := typedBMid) (by decide) (by decide)

/-- **Fugue's op set as a genuine lattice.** `Fugue.OpSet` is a `List InsOp`
merged by append: associative, but neither commutative nor idempotent, so it is
not a `MergeState`. The set of ops is one — and it is what a replica actually
holds. -/
abbrev FState := GSet Fugue.InsOp

/-- Every insertion op the window can express, in a canonical enumeration order
(id ascending, then origin with the root first, then side). -/
def opWindow (n : Nat) : List Fugue.InsOp :=
  (List.range n).flatMap (fun i =>
    ((-1 : Int) :: (List.range n).map (fun a => Int.ofNat a)).flatMap (fun o =>
      [⟨i, o, false⟩, ⟨i, o, true⟩]))

/-- Materialize a set of ops into `Fugue.lean`'s list form. The enumeration
order makes `Fugue.lookup`'s first-match rule replica-independent: a state
carrying two ops for one id resolves the same way everywhere (that state is
`Sequence.UniqueAnchor`'s violation in Fugue clothing, discharged there by
content-addressing and here by canonicalisation). -/
def toOpSet (n : Nat) (s : FState) : Fugue.OpSet := (opWindow n).filter s

/-- Whether any op in the state minted the id `i`. The dense id space of
`Fugue.lean` degrades an unmentioned index to a root-anchored element; a replica
that never received the op has no such element, and this is the filter that says
so — the same shape as `visible`'s tombstone filter. -/
def minted (n : Nat) (s : FState) (i : Nat) : Bool :=
  (toOpSet n s).any (fun op => op.id == i)

/-- **The rendered text under the Fugue order** — `Fugue.docOrder`, the real
decision core, with unminted indices filtered out and the glyphs applied. -/
def fugueText (n : Nat) (s : FState) : List Glyph :=
  ((Fugue.docOrder n (toOpSet n s)).filter (minted n s)).map glyph

/-- The replica that typed `a` as a right child of the root, minting id `1`. -/
def fugueALow : FState := fun op => op == ⟨1, -1, true⟩

/-- The replica that typed the same letter, minting id `3`. -/
def fugueAHigh : FState := fun op => op == ⟨3, -1, true⟩

/-- The peer that typed `b`, minting id `2` — between the two. -/
def fugueBMid : FState := fun op => op == ⟨2, -1, true⟩

theorem fugueALow_text : fugueText 4 fugueALow = [Glyph.a] := by decide

theorem fugueAHigh_text : fugueText 4 fugueAHigh = [Glyph.a] := by decide

theorem fugueBMid_text : fugueText 4 fugueBMid = [Glyph.b] := by decide

theorem fugue_low_merge : fugueText 4 (fugueALow ⊔ fugueBMid) = [Glyph.a, Glyph.b] := by
  decide

theorem fugue_high_merge : fugueText 4 (fugueAHigh ⊔ fugueBMid) = [Glyph.b, Glyph.a] := by
  decide

/-- ⚠ **The Fugue order needs evidence too.** The same scenario, read by the
other decision core: two replicas rendering `a`, a peer rendering `b`, and two
merges that disagree about the order. Non-interleaving changes which document
the merge produces; it does not change what the merge must be computed from. -/
theorem fugue_text_requiresEvidence : RequiresEvidence (fugueText 4) :=
  rendered_order_requiresEvidence (fun s => (Fugue.docOrder 4 (toOpSet 4 s)).filter (minted 4 s))
    glyph (x₁ := fugueALow) (x₂ := fugueAHigh) (y := fugueBMid) (by decide) (by decide)

/-- ⚠ **The fourth verdict is order-policy invariant.** On the same editing
intent in the two op vocabularies — two replicas typing one letter each at the
start of an empty document, a peer typing between them — RGA and Fugue disagree
about the merged document (`[b, a]` against `[a, b]`, the arbitration running in
opposite directions) and agree that the rendered text
cannot be merged from rendered texts. Sufficiency is a question about
information; the ordering policy is a question about which of the sufficient
answers is the *nice* one. Fugue answers the second question well and leaves the
first exactly where it was. -/
theorem verdict_order_policy_invariant :
    text 5 (typedALow ⊔ typedBMid) ≠ fugueText 4 (fugueALow ⊔ fugueBMid)
      ∧ JoinHom.Fourth.Correct (text 5) JoinHom.Fourth.needsEvidence
      ∧ JoinHom.Fourth.Correct (fugueText 4) JoinHom.Fourth.needsEvidence :=
  ⟨by decide, text_not_incrementallyMergeable, fugue_text_requiresEvidence⟩

end Uwueave.TextSummary
