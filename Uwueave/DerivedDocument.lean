/-
# Uwueave.DerivedDocument — "a computation over a loom yields a little loom",
decomposed into the three claims it was hiding, and taken as far as each is true.

The slogan this library keeps circling is that **derived state has the
substrate's own shape**. `Holes.lean` §7 already refused to state it as one
theorem, and was right to:

> The observation to state carefully, because the poetic version ("a computation
> over a loom yields a little loom") is *almost* a theorem and it matters which
> part is which.

**Codex decomposed it into three claims and ordered them**, and this file is
that order executed. The decomposition is codex's; the credit for it is not
ours.

  * **Claim 1 — representation closure.** Result evidence (candidates,
    provenance, obligations, certificates) can be represented as a document in
    the same substrate. Codex: *"probably yes, and immediately useful. A forked
    result is naturally a small branching document."* §1. **Landed**, and
    stronger than asked: the representation is an *isomorphism* of mergeable
    states (`encodeEvidence_iso`), so the answer to "does the encoding lose
    evidence" is **nothing** — and §1.4 exhibits two natural coarser encodings
    that do lose, so the faithfulness is a fact about this encoding rather than
    a triviality about all of them.
  * **Claim 2 — merge closure.** `deriveDoc (x ⊔ y) = deriveDoc x ⊔ deriveDoc y`
    — a join-**homomorphism** requirement, not a monotonicity one. §2 for the
    positive (`deriveDoc_hom`, one line over two named ingredients), §3 for the
    necessary negative (`deriveDoc_not_hom`): a document computed from the bare
    count is not a sufficient merge summary. A provenance-retaining document
    does work (`seenDoc_retains_the_evidence`), exactly as
    `JoinHom.no_count_merge_without_provenance` predicts.
  * **Claim 3 — recursion.** Codex: *do not call it a fixed point until
    recursive self-dependence is actually modelled.* §4 does the house-friendly
    version — rank-grounded dependency edges, terminating evaluation, **unique**
    materialization — and §5 does the genuinely self-dependent version on a
    bounded-height carrier, which is the only place in this file where the words
    "fixed point" NAME a theorem rather than warn about one.

⚠ **Claims 1 and 2 are CLOSURE results and are described as such throughout.**
Neither says anything recursive. "The derived object is a document, and
deriving commutes with merge" is a statement about one derivation step; it is
not a fixed-point theorem and is never called one below. That warning is
codex's and it is the reason §§1–2 and §§4–5 are different sections rather than
one narrative.

## What "a document" is here, and why the node type is structured

`WeaveState.lean`'s loom document is a product whose first field is
`nodes : GSet NodeId` — a grow-only causal node set — with per-node content
beside it. The document carrier below is exactly that field's shape:
`EvidenceDoc α := GSet (EvNode α)`, a grow-only set of **attributed nodes**, with
the `MergeState` found by `inferInstance` and **zero new merge proofs**
(`example` in §1.1), exactly as `WeaveState` gets its.

The node id type is the structured `EvNode α` rather than `Nat`. In a deployment
ids are content-derived hashes and the injection into `Nat` is a
collision-resistance premise; `Acyclicity.lean`'s header prices exactly that
step and declines to pretend Lean proved anything about SHA-2. Using a
structured id keeps §1's faithfulness checkable with no cryptographic premise
anywhere, and costs only that `Acyclicity`'s `EdgeGraph` (which is `Nat`-indexed)
does not apply *to this node set*. It applies where the DAG content actually is
— §4's derivation graph, whose vertices are derivation slots and genuinely are
`Nat` — and there it is used **verbatim, unreproved**.

## The transport table — what moves, and what refuses to

| evidence-side fact | hypothesis it needs | document-side fact |
|---|---|---|
| `Evidence`'s componentwise merge | every component grow-only | `encodeEvidence_merge` (§1.2) |
| `Holes.evalSet_hom` | none (any `f`) | `deriveDoc_hom` (§2) |
| `JoinHom.no_count_merge_without_provenance` | — | `tallyDoc_requires_evidence` (§3) |
| `MinimalSummary.no_count_derived_summary_sufficient` | the document factors through `card` | `deriveDoc_not_hom` (§3) |
| `JoinHom.count_summary_must_distinguish` | the summary is a hom and `card` factors through it | `seenDoc_retains_the_evidence` (§3.1) |
| `Acyclicity.grounded_iconfluent` | a shared rank | `pipelines_merge_coordination_free` (§4) |
| `RenderSix.statusOf_sound6` | a right inverse / section of the encoding | `docStatus_sound6` (§6) |

The row that refuses is the count, and it refuses in the sharpest available
form: not "this combiner is wrong" but "**no** document computed from the count
is even enough evidence to try" (§3). §3.1 keeps that from reading as "no
document works": the document that kept *which* elements were seen is a
homomorphism, the count factors through it, and it separates the two replicas —
which is what the impossibility said the escape route would have to look like.

## Honest boundary

⟨TERMINAL⟩ = a theorem of the model; ⟨UNDONE⟩ = work wearing a caveat's clothes.

  * **The evidence document here has no internal edge structure.** §1's document
    is a node *set*: the sense in which a forked result is "branching" is
    `forked_result_is_a_branching_document` — two candidate nodes attributed to
    two distinct sources, a fan of siblings — not a deep parent-linked DAG.
    `Uwueave.EvidenceGraph` now supplies typed candidate/source/obligation/
    certificate vertices, rank-descending internal edges, endpoint well-formedness,
    and `flat_encodeEvidence_is_projection` back to this carrier. ⟨UNDONE at the
    deployment boundary⟩ Those graph identities are still logical ids, not
    cryptographic or content-addressed identities; no hash/signature binding is
    manufactured by the typed graph. §4's DAG remains the dependency graph
    *between* derivations, which is a different graph.
  * **Position nodes are attribution, not self-authenticating provenance.**
    ⟨TERMINAL for the semantic carrier⟩ `deriveAttributedDoc_position_iff`
    proves exactly what the caller's world/source functions and static position
    list say, and `forgetPositions_deriveAttributedDoc` projects back to the
    original evidence document. `Preo.DerivedProgram` derives that list from
    exact typed holes; its verified entry point additionally demands an
    external source-authenticity proof. This file does not manufacture one.
  * **Claim 1 is faithful because every component of `ResultEvidence` is
    grow-only.** ⟨TERMINAL for this carrier⟩ `encodeEvidence` is a relabelling
    along `EvNode α ≃ (α × Source) ⊕ Source ⊕ Source`, and the merge equation is
    that both sides are pointwise `||` at that reindexing. Nothing here says a
    carrier with an LWW or a counter component embeds; `Catalog`'s LWW join
    *selects*, and no theorem below survives that substitution.
  * **§4's class is the rank-grounded graphs, not the acyclic ones.**
    ⟨TERMINAL⟩ `acyclic_pipelines_are_not_all_grounded` exhibits an acyclic
    dependency graph (`i → i+1`) admitting **no** rank at all, so the
    termination result genuinely does not cover every acyclic pipeline. That is
    the price of the house technique, and `Acyclicity.acyclicity_not_iconfluent`
    is why the price is worth paying: the acyclic class is not closed under
    merge and the grounded class is.
  * **§4's recursive materializer is total but not incremental.** ⟨NARROWED⟩
    `Preo.DerivedProgram` gives a certified non-recursive typed derivation an
    incremental cache/update path with fresh-evaluation correctness and a
    zero-recomputation theorem off its exact dependencies. `materialize` for a
    rank-grounded multi-slot pipeline still recomputes through `matFuel`; no
    differential scheduler for that recursive graph is claimed.
  * **§5 needs a height bound handed in, and it does NOT hold at §1's carrier.**
    ⟨UNDONE⟩ `BoundedHeight` is a *hypothesis* — a
    strictly-increasing-along-strict-ascents height with a global ceiling.
    `bitBoundedHeight` inhabits it at the one-bit derived lattice, so §5 is not
    a theorem about an empty class; but `EvidenceDoc α` over an infinite `α`
    has no such bound, so **§5 does not apply to §1's documents**. What it
    applies to is finite-height derived views — a bit, a threshold, a bounded
    fork grade. Constructing a bound for a general derived document is unbuilt,
    and no theorem here suggests one exists.
  * **Self-dependence in §5 is a monotone endofunction, not a derivation
    language.** ⟨NARROWED⟩ `Preo.Expr` now classifies a first-order typed
    non-recursive fragment and `Preo.DerivedProgram` connects its positive
    proofs here. The fixed-point input `F : S → S` remains an arbitrary
    monotone map; no syntax or classifier for self-dependent programs is
    manufactured by that adapter.
  * **§6 reuses `RenderSix`'s carrier; it does not prove a UI exists.**
    ⟨TERMINAL for the claim made⟩ `docStatus_sound6` says the six-status
    honesty contract holds at the document carrier, so one `Carrier6` consumer
    serves primary evidence and derived documents alike. Whether any surface
    renders them identically is not a Lean question and is not claimed.
  * **Noncomputability is inherited.** ⟨TERMINAL at this carrier⟩ `deriveDoc`,
    `docStatus` and `docValues` sit above `Holes.evalSet` and
    `ResultStatus.statusOf`, which take their decisions classically.
    `Classical.choice` is inside the audit floor.

Literature — what each is for here:
  * **Knaster–Tarski**, in its elementary bounded-height form: §5 is the finite
    Kleene iteration `⊥, F⊥ ⊔ ⊥, …` with a height ceiling supplying the
    stabilization that continuity supplies in the general theorem. Nothing
    domain-theoretic is imported and none is claimed.
  * **Stratified negation / stratified Datalog** (Apt–Blair–Walker; Van Gelder):
    §4's shape. A program whose dependency edges strictly descend a stratum
    order has a unique canonical model computed stratum by stratum; here the
    stratum is `rank` and the canonical model is `materialize`.
  * **Differential dataflow / timely** (McSherry et al.; Brun–Decova–Lattuada–
    Traytel for the verified progress half): the incremental evaluator §4's
    boundary names as unbuilt.
  * `Holes.lean` §7, `JoinHom.lean` §5, `MinimalSummary.lean` §5,
    `Acyclicity.lean`, `RenderSix.lean` §3 — the five in-tree results this file
    transports rather than re-proves.
-/
import Uwueave.RenderSix
import Uwueave.MinimalSummary
import Uwueave.Acyclicity

namespace Uwueave.DerivedDocument

open Uwueave Uwueave.Catalog
open Uwueave.ResultStatus (Status statusOf)

universe u

/-! ## §1. CLAIM 1 — REPRESENTATION CLOSURE.

Result evidence is a document in the substrate's own shape. The document is a
grow-only set of attributed nodes — `WeaveState.nodes`'s type with a structured
id — and the encoding is an **isomorphism of mergeable states**, so the answer
to "what does the encoding lose" is *nothing*.

This is a closure result about one representation. It says nothing recursive
and nothing about fixed points; §4 and §5 are where recursion lives. -/

/-! ### §1.1 The carrier -/

/-- **A node of an evidence document.** One constructor per component of
`Evidence.ResultEvidence`: an attributed candidate, a source still owed, a
source certified closed. The type is exactly the disjoint sum
`(α × Source) ⊕ Source ⊕ Source`, presented with names so the document reads. -/
inductive EvNode (α : Type) : Type where
  /-- A candidate value `a`, attributed to the source `o` that justified it. -/
  | cand (a : α) (o : Evidence.Source)
  /-- The source `o` may still speak. -/
  | owed (o : Evidence.Source)
  /-- The source `o` has been certified closed. -/
  | sealedBy (o : Evidence.Source)
  deriving DecidableEq

/-- **An evidence document**: a grow-only set of attributed nodes. This is
`WeaveState.nodes`'s type (`GSet NodeId`) with a structured id — the header says
why the id is structured rather than a hash-shaped `Nat`. -/
abbrev EvidenceDoc (α : Type) : Type := GSet (EvNode α)

/-- **Zero new merge proofs.** The document's merge — commutative, associative,
idempotent — is the G-Set instance, found by composition exactly as
`WeaveState`'s whole-document instance is. -/
example {α : Type} : MergeState (EvidenceDoc α) := inferInstance

/-! ### §1.2 The encoding, and the merge equation -/

/-- **The encoding.** Each component of the evidence becomes the nodes of its
own constructor. Nothing is combined, nothing is dropped. -/
def encodeEvidence {α : Type} (e : Evidence.ResultEvidence α) : EvidenceDoc α
  | .cand a o => Evidence.candidates e (a, o)
  | .owed o => Evidence.obligations e o
  | .sealedBy o => Evidence.certificates e o

/-- **The decoding.** Read each component off the nodes of its constructor. -/
def decodeEvidence {α : Type} (d : EvidenceDoc α) : Evidence.ResultEvidence α :=
  (fun p => d (.cand p.1 p.2), fun o => d (.owed o), fun o => d (.sealedBy o))

/-- **THE REPRESENTATION-CLOSURE EQUATION: encoding preserves merge.**

    encodeEvidence (e₁ ⊔ e₂) = encodeEvidence e₁ ⊔ encodeEvidence e₂

Two replicas may ship their evidence or ship the documents it encodes to, and
sync in either order: same document. This is what makes "a forked result IS a
small branching document" a theorem rather than a slogan — the fork survives the
encoding *and* survives the merge, on the nose.

The content is that both sides are pointwise `||` at the reindexing
`EvNode α ≃ (α × Source) ⊕ Source ⊕ Source`, which is why the proof is a case
split and nothing more. It holds **because every component of `ResultEvidence`
is grow-only**; the boundary says what fails without that. -/
theorem encodeEvidence_merge {α : Type} (e₁ e₂ : Evidence.ResultEvidence α) :
    encodeEvidence (e₁ ⊔ e₂) = encodeEvidence e₁ ⊔ encodeEvidence e₂ := by
  funext n
  cases n <;> rfl

/-- The same equation in `JoinHom.lean`'s vocabulary, so the transports of that
file apply by name rather than by re-proof. -/
theorem encodeEvidence_joinHom {α : Type} : JoinHom (encodeEvidence (α := α)) :=
  encodeEvidence_merge

/-- Decoding preserves merge too — the other half of the isomorphism. -/
theorem decodeEvidence_merge {α : Type} (d₁ d₂ : EvidenceDoc α) :
    decodeEvidence (d₁ ⊔ d₂) = decodeEvidence d₁ ⊔ decodeEvidence d₂ := rfl

/-! ### §1.3 The encoding loses nothing — and that is a theorem, not a hope -/

/-- Decoding inverts encoding, definitionally. -/
theorem decode_encode {α : Type} (e : Evidence.ResultEvidence α) :
    decodeEvidence (encodeEvidence e) = e := rfl

/-- …and encoding inverts decoding: every document is the encoding of some
evidence, because `EvNode` has exactly the three constructors the evidence has
components. -/
theorem encode_decode {α : Type} (d : EvidenceDoc α) :
    encodeEvidence (decodeEvidence d) = d := by
  funext n
  cases n <;> rfl

/-- **The encoding is injective — it loses no evidence.** -/
theorem encodeEvidence_injective {α : Type} {e₁ e₂ : Evidence.ResultEvidence α}
    (h : encodeEvidence e₁ = encodeEvidence e₂) : e₁ = e₂ := by
  rw [← decode_encode e₁, ← decode_encode e₂, h]

/-- **CLAIM 1, AT FULL STRENGTH: evidence and its document are the same
mergeable state.** Both maps preserve the join and they are mutually inverse, so
the representation is an *isomorphism*, not merely an embedding. That is the
exact answer to "does the encoding lose evidence?" — **nothing**, and §1.4 shows
the question was not rhetorical by exhibiting encodings that do lose. -/
theorem encodeEvidence_iso {α : Type} :
    JoinHom (encodeEvidence (α := α))
      ∧ JoinHom (decodeEvidence (α := α))
      ∧ (∀ e : Evidence.ResultEvidence α, decodeEvidence (encodeEvidence e) = e)
      ∧ (∀ d : EvidenceDoc α, encodeEvidence (decodeEvidence d) = d) :=
  ⟨encodeEvidence_joinHom, decodeEvidence_merge, decode_encode, encode_decode⟩

/-- The encoding is an **order** embedding as well: a replica knows more
evidence exactly when its document holds more nodes. Immediate from the
homomorphism and injectivity, and it is what makes "the document grows as the
evidence grows" the same statement twice. -/
theorem encodeEvidence_leq_iff {α : Type} (e₁ e₂ : Evidence.ResultEvidence α) :
    encodeEvidence e₁ ⊑ encodeEvidence e₂ ↔ e₁ ⊑ e₂ := by
  constructor
  · intro h
    have h' : encodeEvidence (e₁ ⊔ e₂) = encodeEvidence e₂ := by
      rw [encodeEvidence_merge]; exact h
    exact encodeEvidence_injective h'
  · intro h
    show encodeEvidence e₁ ⊔ encodeEvidence e₂ = encodeEvidence e₂
    rw [← encodeEvidence_merge, h]

/-! ### §1.4 …and the natural coarser encodings do lose

The isomorphism above would be uninteresting if every encoding were faithful.
Two that are not, both already named in the tree. -/

/-- ⚠ **Keeping only the candidate values is not faithful.** `Evidence.values`
forgets the attribution and the whole closure axis: `exactW` and `openW` have
*equal* values and are different evidences — one renders `exact 47` and the
other `provisional 47`. So a "document" holding only the answer set has thrown
away the thing `Evidence.lean` was built to keep, and `encodeEvidence`'s
faithfulness is a property of *this* encoding rather than of encodings. -/
theorem value_only_encoding_is_not_faithful :
    Evidence.values Evidence.openW = Evidence.values Evidence.exactW
      ∧ Evidence.exactW ≠ Evidence.openW
      ∧ Evidence.render Evidence.exactW = Evidence.View.exact 47
      ∧ Evidence.render Evidence.openW = Evidence.View.provisional 47 := by
  refine ⟨rfl, ?_, Evidence.four_states_inhabited.1,
    Evidence.four_states_inhabited.2.1⟩
  intro h
  have hb : Evidence.obligations Evidence.exactW Evidence.bob
      = Evidence.obligations Evidence.openW Evidence.bob := by rw [h]
  exact absurd hb (by decide)

/-! ### §1.5 A forked result is a branching document, and the document is a
loom document

The two halves codex's claim 1 promises: the fork is *visible in the document*
(two candidate nodes under two distinct sources), and the document satisfies the
referential-integrity row a loom schema would put on it — coordination-free, by
the same argument `WeaveState.bookmarksVerdict` uses. -/

/-- **A forked result IS a small branching document.** The document encoding
`Evidence.forkedClosedW` holds two distinct candidate nodes, attributed to two
distinct sources, whose obligation nodes are both present: a two-branch fan, in
the substrate's own node set. -/
theorem forked_result_is_a_branching_document :
    encodeEvidence Evidence.forkedClosedW (.cand 47 Evidence.alice) = true
      ∧ encodeEvidence Evidence.forkedClosedW (.cand 49 Evidence.bob) = true
      ∧ (EvNode.cand 47 Evidence.alice : EvNode Holes.Val)
          ≠ EvNode.cand 49 Evidence.bob
      ∧ encodeEvidence Evidence.forkedClosedW (.owed Evidence.alice) = true
      ∧ encodeEvidence Evidence.forkedClosedW (.owed Evidence.bob) = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **Referential integrity for a derived document**: every candidate node names
a source the document still owes. This is `WeaveState`'s cross-field row at the
derived carrier — a bookmark never dangles, a candidate never cites a source the
document does not carry. -/
def AttributedToOwed {α : Type} (d : EvidenceDoc α) : Prop :=
  ∀ (a : α) (o : Evidence.Source), d (.cand a o) = true → d (.owed o) = true

/-- **…and it is coordination-free.** The row is per-node-local — a candidate in
the merge came from one side, and that side owed its source — so it survives
every merge with no coordination, by the argument `Acyclicity.grounded_iconfluent`
and `Spec.pointsAtExisting_iconfluent` both use: locality plus growth. -/
theorem attributedToOwed_iconfluent {α : Type} :
    IConfluent (S := EvidenceDoc α) AttributedToOwed := by
  intro x y hx hy a o hmem
  show (x (.owed o) || y (.owed o)) = true
  rcases (Holes.gset_mem_or x y (EvNode.cand a o)).mp hmem with h | h
  · rw [hx a o h]; rfl
  · rw [hy a o h]; exact Bool.or_true _

/-- The row is inhabited by real derived evidence: `exactW`'s document attributes
its one candidate to `alice`, and `alice` is owed. -/
theorem exactW_doc_attributedToOwed :
    AttributedToOwed (encodeEvidence Evidence.exactW) := by
  intro a o h
  have h' : Evidence.cand47 (a, o) = true := h
  have ho : o = Evidence.alice := (Evidence.mem_cand47 h').2
  rw [ho]
  decide

/-! ### §1.6 What the homomorphism buys, by name

`JoinHom.lean` states two transports whose hypothesis is exactly
`encodeEvidence_joinHom`. Both are one line here, and both are about the derived
document rather than about evidence. -/

/-- **Every document invariant pulls back to evidence.** An I-confluent
invariant on derived documents is an I-confluent invariant on the evidence they
encode — `JoinHom.iconfluent_pullback_of_joinHom` at this encoding. So the whole
judgement of `Confluence.lean` may be stated on the document and read on the
evidence. -/
theorem document_invariant_pulls_back {α : Type} {J : Invariant (EvidenceDoc α)}
    (hJ : IConfluent J) :
    IConfluent (S := Evidence.ResultEvidence α) (fun e => J (encodeEvidence e)) :=
  iconfluent_pullback_of_joinHom encodeEvidence_joinHom hJ

/-- **The document may be shipped.** `JoinHom.summaryFold_iff_joinHom` says the
summary-replication architecture is correct **exactly** for join homomorphisms;
`encodeEvidence` is one, so a replica may gossip encoded documents and fold
arrivals with the document lattice's own join, in any order and any batching,
and land where re-encoding the merged evidence lands. -/
theorem encodeEvidence_ships {α : Type} :
    JoinHom.SummaryFoldAgrees (encodeEvidence (α := α)) :=
  (JoinHom.summaryFold_iff_joinHom _).mpr encodeEvidence_joinHom

/-! ## §2. CLAIM 2 — MERGE CLOSURE.

`deriveDoc` derives a document from replicated candidate worlds. The claim is
the **join-homomorphism** equation — deriving-then-merging equals
merging-then-deriving — and codex's ordering is right that it rides claim 1 by
composition: `deriveDoc` is `encodeEvidence` after `Evidence.fromWorlds`, and
both are homomorphisms.

**`deriveDoc_hom` is one line** — a single application of `joinHom_comp`, under a
`show` that names the composition Lean's unifier will not guess through a `def`.
That is the good outcome and it is worth saying plainly: the value here is the
*statement*, and needing no new argument is the content of "the substrate's
machinery transfers". What the one line rides on is two named ingredients —
`Holes.evalSet_hom` (unchanged since `Holes.lean`; it is a genuine homomorphism
because an image distributes over a union) and `encodeEvidence_merge` — plus
`merge_idem` for the two components `fromWorlds` holds constant, which is the
whole of `evidenceOf_joinHom`'s three-rewrite proof.

⚠ This is still a **closure** result. It is one derivation step commuting with
one merge; it is not recursive and is not a fixed-point statement. -/

/-- **Composition of join homomorphisms is a join homomorphism.** Stated
generally because §2's headline is exactly this at two named maps. -/
theorem joinHom_comp {A B C : Type u} [MergeState A] [MergeState B] [MergeState C]
    {g : B → C} {f : A → B} (hg : JoinHom g) (hf : JoinHom f) :
    JoinHom (fun a => g (f a)) := by
  intro x y
  show g (f (x ⊔ y)) = g (f x) ⊔ g (f y)
  rw [hf, hg]

/-- The evidence a computation produces from candidate worlds, with the source
roster held fixed: `Evidence.fromWorlds` read as a function of the worlds
alone. -/
noncomputable def evidenceOf {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source)
    (W : GSet Holes.World) : Evidence.ResultEvidence α :=
  Evidence.fromWorlds f src W obl cert

/-- **Deriving evidence from candidate worlds is a join homomorphism.**
`Holes.evalSet_hom` for the candidate component (transported by
`Evidence.fromWorlds_candidates_hom`, itself unreproved), and `merge_idem` for
the two components the roster holds fixed. -/
theorem evidenceOf_joinHom {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source) :
    JoinHom (evidenceOf f src obl cert) := by
  intro W₁ W₂
  show (Holes.evalSet (fun w => (f w, src w)) (W₁ ⊔ W₂), obl, cert)
      = (Holes.evalSet (fun w => (f w, src w)) W₁
          ⊔ Holes.evalSet (fun w => (f w, src w)) W₂, obl ⊔ obl, cert ⊔ cert)
  rw [Holes.evalSet_hom, merge_idem, merge_idem]

/-- **The derived document**: compute over the candidate worlds, then encode the
resulting evidence as a document. Definitionally the composition §2's headline
is about. -/
noncomputable def deriveDoc {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source)
    (W : GSet Holes.World) : EvidenceDoc α :=
  encodeEvidence (evidenceOf f src obl cert W)

/-- **CLAIM 2, THE POSITIVE HALF — MERGE CLOSURE.**

    deriveDoc (W₁ ⊔ W₂) = deriveDoc W₁ ⊔ deriveDoc W₂

Deriving-then-merging equals merging-then-deriving, **as documents**. A replica
may gossip its candidate worlds or the derived document and land in the same
place, for **every** deterministic `f`, with no hypothesis on the computation at
all.

**One line**, by composition of §1's homomorphism with §2's — which is the
result codex predicted and the reason the ordering put claim 1 first. -/
theorem deriveDoc_hom {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source) :
    JoinHom (deriveDoc f src obl cert) :=
  show JoinHom (fun W => encodeEvidence (evidenceOf f src obl cert W)) from
    joinHom_comp encodeEvidence_joinHom (evidenceOf_joinHom f src obl cert)

/-- The headline as the equation, for readers who want it in that shape. -/
theorem deriveDoc_merge {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source)
    (W₁ W₂ : GSet Holes.World) :
    deriveDoc f src obl cert (W₁ ⊔ W₂)
      = deriveDoc f src obl cert W₁ ⊔ deriveDoc f src obl cert W₂ :=
  deriveDoc_hom f src obl cert W₁ W₂

/-- Exact candidate/source membership in a derived document. -/
theorem deriveDoc_candidate_iff {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source)
    (worlds : GSet Holes.World) (value : α) (source : Evidence.Source) :
    deriveDoc f src obl cert worlds (.cand value source) = true ↔
      ∃ world, worlds world = true ∧ f world = value ∧ src world = source := by
  rw [deriveDoc, evidenceOf, encodeEvidence, Evidence.fromWorlds,
    Holes.mem_evalSet]
  constructor
  · rintro ⟨world, hworld, hp⟩
    exact ⟨world, hworld, congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨world, hworld, hvalue, hsource⟩
    exact ⟨world, hworld, by rw [hvalue, hsource]⟩

/-- **And therefore the derived document ships and folds.** Any gossip history,
any batching, any duplication of documents: the fold of shipped documents equals
the document of the merged worlds. `JoinHom.summaryFold_iff_joinHom` again, now
at the derivation rather than at the encoding. -/
theorem deriveDoc_ships {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source) :
    JoinHom.SummaryFoldAgrees (deriveDoc f src obl cert) :=
  (JoinHom.summaryFold_iff_joinHom _).mpr (deriveDoc_hom f src obl cert)

/-! ### Positioned attribution documents -/

/-- An evidence document augmented with exact value/source/position records.
The old evidence nodes are embedded unchanged, so forgetting the new records
recovers `EvidenceDoc` on the nose. -/
inductive AttributedNode (α Position : Type) where
  | evidence (node : EvNode α)
  | position (candidate : Evidence.PositionCandidate α Position)
  deriving DecidableEq

/-- The grow-only document carrier for attributed expression positions. -/
abbrev AttributedDoc (α Position : Type) := GSet (AttributedNode α Position)

/-- Drop the positional augmentation and retain the original evidence
document. -/
def forgetPositions {α Position : Type}
    (document : AttributedDoc α Position) : EvidenceDoc α :=
  fun node => document (.evidence node)

/-- Materialize ordinary evidence and exact positioned candidates together. -/
noncomputable def deriveAttributedDoc {α Position : Type}
    (f : Holes.World → α) (src : Holes.World → Evidence.Source)
    (positions : List Position) (obl cert : GSet Evidence.Source)
    (worlds : GSet Holes.World) : AttributedDoc α Position
  | .evidence node => deriveDoc f src obl cert worlds node
  | .position candidate => Evidence.positionCandidates f src positions worlds candidate

/-- The augmentation projects exactly to the existing derived document. -/
@[simp] theorem forgetPositions_deriveAttributedDoc {α Position : Type}
    (f : Holes.World → α) (src : Holes.World → Evidence.Source)
    (positions : List Position) (obl cert : GSet Evidence.Source)
    (worlds : GSet Holes.World) :
    forgetPositions (deriveAttributedDoc f src positions obl cert worlds) =
      deriveDoc f src obl cert worlds := rfl

/-- Exact ordinary candidate/source membership survives in the augmented
document. -/
theorem deriveAttributedDoc_candidate_iff {α Position : Type}
    (f : Holes.World → α) (src : Holes.World → Evidence.Source)
    (positions : List Position) (obl cert : GSet Evidence.Source)
    (worlds : GSet Holes.World) (value : α) (source : Evidence.Source) :
    deriveAttributedDoc f src positions obl cert worlds
        (.evidence (.cand value source)) = true ↔
      ∃ world, worlds world = true ∧ f world = value ∧ src world = source :=
  deriveDoc_candidate_iff f src obl cert worlds value source

/-- Exact value/source/position membership in the augmentation. -/
theorem deriveAttributedDoc_position_iff {α Position : Type}
    (f : Holes.World → α) (src : Holes.World → Evidence.Source)
    (positions : List Position) (obl cert : GSet Evidence.Source)
    (worlds : GSet Holes.World)
    (candidate : Evidence.PositionCandidate α Position) :
    deriveAttributedDoc f src positions obl cert worlds (.position candidate) = true ↔
      ∃ world, worlds world = true
        ∧ f world = candidate.value
        ∧ src world = candidate.source
        ∧ candidate.position ∈ positions :=
  Evidence.mem_positionCandidates f src positions worlds candidate

/-- The augmented materialization remains a join homomorphism in candidate
worlds. -/
theorem deriveAttributedDoc_hom {α Position : Type}
    (f : Holes.World → α) (src : Holes.World → Evidence.Source)
    (positions : List Position) (obl cert : GSet Evidence.Source) :
    JoinHom (deriveAttributedDoc f src positions obl cert) := by
  intro left right
  funext node
  cases node with
  | evidence node =>
      exact congrFun (deriveDoc_merge f src obl cert left right) node
  | position candidate =>
      exact congrFun (Evidence.positionCandidates_hom
        f src positions left right) candidate

/-! ## §3. CLAIM 2's NECESSARY NEGATIVE — the count, transported to documents.

Codex's third item, and the reason claim 2 is a real requirement rather than a
description: **being a document does not make a derivation mergeable.** The
counterexample is `JoinHom.lean`'s counting, given a document-valued shape.

`tallyDoc` is the obvious way to make a count "a little loom": encode the count
as an evidence document holding one candidate node whose value is the tally.
Everything about it is a legitimate document — §1 applies to it verbatim — and
it is **not** a join homomorphism, so §2's equation fails for it.

Three refutations at three strengths, none of them re-proved here:

  * `tallyDoc_not_joinHom` — the concrete failure, on one node;
  * `deriveDoc_not_hom` — **no** document computed from the count is a
    sufficient summary, for any post-processing whatsoever
    (`MinimalSummary.no_count_derived_summary_sufficient`, whose engine is
    `card_ctxEquiv_iff`: the count's coarsest sufficient summary is the whole
    set);
  * `mergeable_count_document_must_retain_the_evidence` — the positive form of
    the same fact (`JoinHom.count_summary_must_distinguish`): if a document-valued
    derivation of the count *is* a homomorphism, the document must already
    separate the two replicas, i.e. it must have retained the evidence. -/

/-- The single anonymous source a tally is attributed to. -/
def tallySource : Evidence.Source := 0

/-- The evidence a tally document encodes: one candidate node carrying the
count, nothing owed, nothing certified. -/
def tallyEvidence (n : Nat) : Evidence.ResultEvidence Nat :=
  (fun p => decide (p = (n, tallySource)), (fun _ => false), (fun _ => false))

/-- **A count, made into a document.** `JoinHom.card` of the replicated set,
encoded by §1 — so it is a document in exactly the sense claim 1 established,
and the failure below is not a failure of the representation. -/
def tallyDoc (s : GSet Bool) : EvidenceDoc Nat :=
  encodeEvidence (tallyEvidence (JoinHom.card s))

/-- ⚠ **A document-valued count is not a join homomorphism.** Two replicas that
saw different elements each derive the document holding the node `cand 1`; the
merge of their *worlds* holds `cand 2`, and the merge of their *documents* does
not. Being a document bought nothing: the tally node forgot which element it
counted, and no node in the merged document says `2`. -/
theorem tallyDoc_not_joinHom : ¬ JoinHom tallyDoc := by
  intro h
  have hbad := congrFun (h JoinHom.sawA JoinHom.sawB) (EvNode.cand 2 tallySource)
  exact absurd hbad (by decide)

/-- ⚠ **CLAIM 2's NEGATIVE, AT FULL STRENGTH: no document derived from the count
is sufficient.** For **any** post-processing `k : Nat → EvidenceDoc Nat`, the
document `k ∘ card` is not a sufficient summary for the count — not merely
un-mergeable by a particular combiner, but not enough evidence to try.

This is `MinimalSummary.no_count_derived_summary_sufficient` at a document
target type, and its engine is `MinimalSummary.card_ctxEquiv_iff`: contextual
equivalence for an exact count is *equality of the set*, so the count's coarsest
sufficient summary is the whole set and nothing coarser — document-shaped or
otherwise — can stand in for it.

Read as the answer to the question this file exists to ask: **a derived value
being a document does not make it mergeable.** Claim 1 and claim 2 are
independent, and this is the witness that they are. -/
theorem deriveDoc_not_hom (D : GSet Bool → EvidenceDoc Nat)
    (hfac : ∃ k : Nat → EvidenceDoc Nat, ∀ s, D s = k (JoinHom.card s)) :
    ¬ Sufficient D JoinHom.card :=
  MinimalSummary.no_count_derived_summary_sufficient D hfac

/-- The concrete instance: `tallyDoc` itself is not a sufficient summary. -/
theorem tallyDoc_not_sufficient : ¬ Sufficient tallyDoc JoinHom.card :=
  deriveDoc_not_hom tallyDoc ⟨fun n => encodeEvidence (tallyEvidence n), fun _ => rfl⟩

/-- ⚠ **NO COMBINER ON DOCUMENTS SAVES IT EITHER.** The document-level analogue of
`JoinHom.no_count_merge_without_provenance`, which ranged over every
`m : Nat → Nat → Nat`: here `m` ranges over every binary combiner on **documents**
and none is exact. The witnesses do not depend on `m` — `tallyDoc sawA` and
`tallyDoc sawB` are the *same document*, so `m` is handed identical arguments in
a scenario whose truth is the one-node document and in a scenario whose truth is
the two-node one.

So the fourth verdict for a document-valued count is `needsEvidence`
(`JoinHom.Fourth`), and the promotion to a document changed nothing: the tally
node discarded which element it counted, and merging needs precisely that. -/
theorem tallyDoc_requires_evidence : RequiresEvidence tallyDoc := by
  rintro ⟨m, hm⟩
  have hsame : tallyDoc JoinHom.sawA = tallyDoc JoinHom.sawB := by
    show encodeEvidence (tallyEvidence (JoinHom.card JoinHom.sawA))
        = encodeEvidence (tallyEvidence (JoinHom.card JoinHom.sawB))
    rw [JoinHom.card_sawA, JoinHom.card_sawB]
  have hbad : tallyDoc (JoinHom.sawA ⊔ JoinHom.sawA)
      = tallyDoc (JoinHom.sawA ⊔ JoinHom.sawB) := by
    rw [hm JoinHom.sawA JoinHom.sawA, hm JoinHom.sawA JoinHom.sawB, hsame]
  exact absurd (congrFun hbad (EvNode.cand 2 tallySource)) (by decide)

/-- ⚠ **…unless the document retains the evidence.** The positive form: suppose a
document-valued derivation `g` *is* a join homomorphism and the count factors
through it. Then `g` must already tell the replica that saw `a` from the replica
that saw `b` — the document has kept the provenance, and the derivation is
`JoinHom.lean`'s architecture (i) with extra steps.

`JoinHom.count_summary_must_distinguish` at a document codomain; the `MergeState`
the theorem needs is the one `inferInstance` found in §1.1. -/
theorem mergeable_count_document_must_retain_the_evidence
    (g : GSet Bool → EvidenceDoc Nat) (hg : JoinHom g) (k : EvidenceDoc Nat → Nat)
    (hfactor : ∀ s, JoinHom.card s = k (g s)) : g JoinHom.sawA ≠ g JoinHom.sawB :=
  JoinHom.count_summary_must_distinguish g hg k hfactor

/-! ### §3.1 The "unless" clause is inhabited — the document that keeps the
evidence

A conditional whose hypothesis nothing satisfies would make the theorem above a
decoration. It is satisfied, and by the design the theorem predicts: encode
**which sources were seen** as candidate nodes rather than encoding the tally.
The count is then read off the document, the derivation *is* a join
homomorphism, and — as `mergeable_count_document_must_retain_the_evidence`
requires — the two replicas' documents differ. -/

/-- **The document that retains the evidence.** One candidate node per element
seen, attributed to the source that stands for it — no tally anywhere. It is a
document in exactly the sense `tallyDoc` is: both inhabit `EvidenceDoc Nat`, and
by `encode_decode` every inhabitant of that type is the encoding of an
evidence. -/
def seenDoc (s : GSet Bool) : EvidenceDoc Nat
  | .cand 0 o => s (decide (o = 1))
  | _ => false

/-- …and being the encoding of an evidence is not a hope about it: claim 1's
surjectivity says so of every document, this one included. -/
theorem seenDoc_is_an_encoded_evidence (s : GSet Bool) :
    seenDoc s = encodeEvidence (decodeEvidence (seenDoc s)) :=
  (encode_decode _).symm

/-- **…and it IS a join homomorphism**, so §2's equation holds for it: a replica
may ship this document and a peer may merge documents. What separates it from
`tallyDoc` is not the carrier — both are documents — but that this one never
threw the attribution away. -/
theorem seenDoc_joinHom : JoinHom seenDoc := by
  intro x y
  funext n
  match n with
  | .cand 0 o => rfl
  | .cand (a + 1) o => rfl
  | .owed o => rfl
  | .sealedBy o => rfl

/-- Reading the count back off the document: count the two candidate nodes. -/
def countOfDoc (d : EvidenceDoc Nat) : Nat :=
  JoinHom.bit (d (.cand 0 0)) + JoinHom.bit (d (.cand 0 1))

/-- The count factors through the evidence-retaining document. -/
theorem card_factors_through_seenDoc (s : GSet Bool) :
    JoinHom.card s = countOfDoc (seenDoc s) := rfl

/-- **THE ESCAPE ROUTE, EXHIBITED.** A document-valued derivation of the count
that *is* a join homomorphism exists, the count factors through it, and — as
`mergeable_count_document_must_retain_the_evidence` forces — it separates the two
replicas. So §3's impossibility is not "no document works"; it is exactly "no
document that has forgotten the evidence works", and the boundary between the two
is `tallyDoc` against `seenDoc`. -/
theorem seenDoc_retains_the_evidence :
    JoinHom seenDoc
      ∧ (∀ s, JoinHom.card s = countOfDoc (seenDoc s))
      ∧ seenDoc JoinHom.sawA ≠ seenDoc JoinHom.sawB :=
  ⟨seenDoc_joinHom, card_factors_through_seenDoc,
   mergeable_count_document_must_retain_the_evidence seenDoc seenDoc_joinHom
     countOfDoc card_factors_through_seenDoc⟩

/-! ## §4. CLAIM 3, FIRST VERSION — a rank-grounded derivation pipeline
terminates with a **unique** materialization.

Codex: *claim 3 is substantially more, and the house-friendly first version is
rank-grounded — derived dependency edges strictly increase rank ⇒ evaluation
terminates ⇒ unique materialization.* This section is exactly that, and the DAG
class is stated precisely: **`Acyclicity.Grounded`, not `Acyclicity.Acyclic`.**

The vertices are derivation **slots** (`Nat`), the edges are dependency edges,
and the graph is `Acyclicity.EdgeGraph` — so `Acyclicity.lean` applies verbatim,
unreproved, which is why the header keeps the evidence document's node type out
of this graph.

Two facts make the class the right one:

  * `Acyclicity.grounded_acyclic` — grounded implies acyclic, so a grounded
    pipeline is a genuine DAG;
  * `Acyclicity.grounded_iconfluent` — the grounded class is closed under merge,
    so two replicas may each add derivations offline and the merged pipeline
    still terminates (`pipelines_merge_coordination_free`). The acyclic class is
    **not** closed under merge (`Acyclicity.acyclicity_not_iconfluent`), which is
    the whole reason the house technique restricts to grounded.

And the restriction is real, not cosmetic: `acyclic_pipelines_are_not_all_grounded`
exhibits an acyclic dependency graph admitting no rank at all. -/

/-- **A stratified derivation pipeline.** Slots are derivations; `deps (i, j)`
means slot `i`'s derivation reads slot `j`'s materialized document; `rank` is
the stratum, and `grounded` is the requirement that every dependency edge
strictly descends it — i.e. a derived slot depends only on strictly lower
strata. `reads_deps` is the locality condition that makes the derivation a
*function of its dependencies*: two environments agreeing on slot `i`'s
dependencies give slot `i` the same document. -/
structure Stratified (D : Type) : Type where
  /-- The stratum of each derivation slot. -/
  rank : Nat → Nat
  /-- The dependency edges: `deps (i, j)` = slot `i` reads slot `j`. -/
  deps : Acyclicity.EdgeGraph
  /-- Every dependency edge strictly descends the rank. -/
  grounded : Acyclicity.Grounded rank deps
  /-- The derivation at each slot, as a function of the environment. -/
  eval : Nat → (Nat → D) → D
  /-- A derivation reads only its declared dependencies. -/
  reads_deps : ∀ (i : Nat) (σ τ : Nat → D),
    (∀ j, deps (i, j) = true → σ j = τ j) → eval i σ = eval i τ

/-- **A materialization**: an assignment of a document to every slot that
satisfies every derivation's own equation. This is what "the pipeline has been
evaluated" means, stated without reference to any evaluation order. -/
def Materializes {D : Type} (P : Stratified D) (σ : Nat → D) : Prop :=
  ∀ i, σ i = P.eval i σ

/-- The fuel-indexed evaluator: with `fuel + 1` steps, evaluate slot `i` over an
environment computed with `fuel`. Elementary recursion on the fuel, so no
well-founded machinery is needed; `matFuel_stable` is what turns it into a
rank-indexed one. -/
def matFuel {D : Type} [Inhabited D] (P : Stratified D) : Nat → Nat → D
  | 0, _ => default
  | fuel + 1, i => P.eval i (fun j => matFuel P fuel j)

/-- **Enough fuel is enough.** Once the fuel exceeds a slot's rank, more fuel
changes nothing: the dependencies have strictly smaller rank (groundedness) and
`reads_deps` says nothing else is read. This is where the rank does its work. -/
theorem matFuel_stable {D : Type} [Inhabited D] (P : Stratified D) :
    ∀ (fuel fuel' i : Nat), P.rank i < fuel → fuel ≤ fuel' →
      matFuel P fuel i = matFuel P fuel' i := by
  intro fuel
  induction fuel with
  | zero => intro _ i h; exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro fuel' i hlt hle
    match fuel' with
    | 0 => exact absurd hle (Nat.not_succ_le_zero f)
    | f' + 1 =>
      show P.eval i (fun j => matFuel P f j) = P.eval i (fun j => matFuel P f' j)
      refine P.reads_deps i _ _ (fun j hj => ?_)
      exact ih f' j (Nat.lt_of_lt_of_le (P.grounded i j hj) (Nat.le_of_lt_succ hlt))
        (Nat.le_of_succ_le_succ hle)

/-- **The materialization**: evaluate each slot with fuel one above its rank.
Total, by ordinary recursion — the termination is `matFuel`'s structural
recursion and the *correctness* of stopping is `matFuel_stable`. -/
def materialize {D : Type} [Inhabited D] (P : Stratified D) (i : Nat) : D :=
  matFuel P (P.rank i + 1) i

/-- **Existence.** `materialize` satisfies every derivation's equation: it is a
materialization. -/
theorem materialize_materializes {D : Type} [Inhabited D] (P : Stratified D) :
    Materializes P (materialize P) := by
  intro i
  show P.eval i (fun j => matFuel P (P.rank i) j) = P.eval i (materialize P)
  refine P.reads_deps i _ _ (fun j hj => ?_)
  exact (matFuel_stable P (P.rank j + 1) (P.rank i) j (Nat.lt_succ_self _)
    (P.grounded i j hj)).symm

/-- **Uniqueness.** Any two materializations are equal — by strong induction on
the rank: a slot's value is determined by its dependencies, which lie strictly
lower. Nothing about the evaluation order enters, which is the point: the
pipeline's answer is a property of the pipeline, not of a schedule. -/
theorem materialize_unique {D : Type} (P : Stratified D) {σ τ : Nat → D}
    (hσ : Materializes P σ) (hτ : Materializes P τ) : σ = τ := by
  have key : ∀ n i, P.rank i = n → σ i = τ i := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro i hi
      rw [hσ i, hτ i]
      refine P.reads_deps i _ _ (fun j hj => ?_)
      exact ih (P.rank j) (hi ▸ P.grounded i j hj) j rfl
  funext i
  exact key (P.rank i) i rfl

/-- **CLAIM 3, FIRST VERSION: a rank-grounded derivation pipeline terminates
with a unique materialization.** Derived documents may feed later derivations;
every dependency edge strictly descends the rank; evaluation is total, and the
assignment it computes is the **only** one satisfying the derivations.

This is claim 3 in the form codex sanctioned — rank-grounded, house technique,
no domain theory — and it is the first statement in this file where the word
"materialization" means the solution of a genuinely recursive system rather than
one derivation step. §5 is the version where the recursion is self-dependent. -/
theorem stratified_derive_terminates {D : Type} [Inhabited D] (P : Stratified D) :
    Materializes P (materialize P)
      ∧ ∀ σ, Materializes P σ → σ = materialize P :=
  ⟨materialize_materializes P,
   fun _ hσ => materialize_unique P hσ (materialize_materializes P)⟩

/-- Every grounded pipeline is a genuine DAG — `Acyclicity.grounded_acyclic`, so
"terminates" is not being bought by a cyclic graph nobody looked at. -/
theorem stratified_deps_acyclic {D : Type} (P : Stratified D) :
    Acyclicity.Acyclic P.deps :=
  Acyclicity.grounded_acyclic P.grounded

/-- **The merged pipeline.** Two replicas share a rank and a family of
derivations; one of them is `P`, and the other has declared its own dependency
edges `deps'`, grounded for the same rank. The merge unions the edge sets.

Both obligations survive the union and neither needs a new argument: the class
is closed by `Acyclicity.grounded_iconfluent`, and locality only gets *easier*
as the declared dependencies grow — a derivation that reads only `P.deps`
a fortiori reads only `P.deps ⊔ deps'`. -/
def mergePipeline {D : Type} (P : Stratified D) (deps' : Acyclicity.EdgeGraph)
    (hg' : Acyclicity.Grounded P.rank deps') : Stratified D where
  rank := P.rank
  deps := P.deps ⊔ deps'
  grounded := Acyclicity.grounded_iconfluent P.rank P.deps deps' P.grounded hg'
  eval := P.eval
  reads_deps := fun i σ τ h =>
    P.reads_deps i σ τ (fun j hj => h j (by
      show (P.deps (i, j) || deps' (i, j)) = true
      rw [hj]; rfl))

/-- **Two replicas may extend a pipeline offline.** Each declares dependency
edges in a partition; the merged pipeline is still grounded, so it still
terminates with a unique materialization — coordination-free, by
`Acyclicity.grounded_iconfluent` and nothing else.

⚠ This is exactly what the *acyclic* class would not give:
`Acyclicity.acyclicity_not_iconfluent` says two acyclic dependency graphs can
merge to a cyclic one, so a pipeline discipline that asked only for acyclicity
would need a coordination event at every derivation added. -/
theorem pipelines_merge_coordination_free {D : Type} [Inhabited D]
    (P : Stratified D) (deps' : Acyclicity.EdgeGraph)
    (hg' : Acyclicity.Grounded P.rank deps') :
    Materializes (mergePipeline P deps' hg') (materialize (mergePipeline P deps' hg'))
      ∧ ∀ σ, Materializes (mergePipeline P deps' hg') σ
          → σ = materialize (mergePipeline P deps' hg') :=
  stratified_derive_terminates _

/-! ### §4.1 The class is exactly the grounded graphs — and the gap is inhabited

A finite acyclic graph always admits a rank. This one does not, because the slot
space is all of `Nat`: the pipeline "slot `i` reads slot `i+1`" is acyclic and
has no stratification, so §4's theorem genuinely does not cover it. Stating the
gap is what keeps "rank-grounded" from reading as "acyclic". -/

/-- The pipeline in which every slot reads the next one: `i → i + 1`. -/
def succEdges : Acyclicity.EdgeGraph := fun e => decide (e.2 = e.1 + 1)

/-- Reachability in `succEdges` strictly increases the slot index. -/
theorem succEdges_reaches_lt {a b : Nat} (h : Acyclicity.Reaches succEdges a b) :
    a < b := by
  induction h with
  | edge h =>
    have : _ = _ + 1 := of_decide_eq_true h
    omega
  | step _ h ih =>
    have : _ = _ + 1 := of_decide_eq_true h
    omega

theorem succEdges_acyclic : Acyclicity.Acyclic succEdges :=
  fun v hv => Nat.lt_irrefl v (succEdges_reaches_lt hv)

/-- ⚠ **AN ACYCLIC PIPELINE NEED NOT BE GROUNDED.** `i → i + 1` is acyclic and
admits **no** rank function whatsoever: a rank would have to descend strictly at
every step, giving an infinite descending chain in `Nat`.

So §4's termination theorem covers strictly fewer pipelines than "the acyclic
ones", and this is the witness. The trade is `Acyclicity.lean`'s own: the
grounded class is stronger, local, closed under merge, and free; the acyclic
class is weaker, global, and escalates. -/
theorem acyclic_pipelines_are_not_all_grounded :
    Acyclicity.Acyclic succEdges
      ∧ ¬ ∃ rank : Nat → Nat, Acyclicity.Grounded rank succEdges := by
  refine ⟨succEdges_acyclic, ?_⟩
  rintro ⟨rank, hg⟩
  have step : ∀ n, rank (n + 1) < rank n := fun n => hg n (n + 1) (by simp [succEdges])
  have descend : ∀ n, rank n + n ≤ rank 0 := by
    intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ k ih => have := step k; omega
  have := descend (rank 0 + 1)
  omega

/-! ## §5. CLAIM 3, SECOND VERSION — self-dependence, and the least fixed point.

§4's derivations are stratified: no slot depends on itself, directly or
transitively. **This section is where that assumption is dropped**, and it is
the only place in this file where the words "fixed point" name a theorem rather
than warn about one — because it is the only place where recursive
self-dependence is actually modelled.

What replaces the rank is a **bounded height** on the derived lattice: a
strictly-increasing-along-strict-ascents height with a global ceiling. That is
the elementary form of Knaster–Tarski: the Kleene iteration `⊥`, `⊥ ⊔ F⊥`, …
cannot ascend forever, and where it stops it is the *least* pre-fixed point,
hence the least fixed point.

⚠ `BoundedHeight` is a hypothesis, not a construction — the boundary says so,
and §1's `EvidenceDoc α` over an infinite `α` does not satisfy it. What does:
finite derived lattices — a fork grade, a threshold, a bit. -/

variable {S : Type u}

/-- **A carrier of bounded height**: a bottom, and a height that strictly
increases along every strict ascent and never exceeds a global bound. This is
the finiteness §5 actually uses — no cardinality, no enumeration, just a
ceiling on chain length. -/
structure BoundedHeight (S : Type u) [MergeState S] : Type u where
  /-- The least element. -/
  bot : S
  /-- …and it is least. -/
  bot_least : ∀ x : S, bot ⊑ x
  /-- The height of a state. -/
  height : S → Nat
  /-- The global ceiling. -/
  bound : Nat
  /-- No state exceeds the ceiling. -/
  height_le : ∀ x : S, height x ≤ bound
  /-- Height strictly increases along a strict ascent. -/
  height_lt : ∀ x y : S, x ⊑ y → x ≠ y → height x < height y

/-- The Kleene iteration of a derivation `F` from the bottom, accumulating with
the join so the sequence ascends by construction. -/
def iter [MergeState S] (F : S → S) (H : BoundedHeight S) : Nat → S
  | 0 => H.bot
  | n + 1 => iter F H n ⊔ F (iter F H n)

/-- The iteration ascends. -/
theorem iter_le_succ [MergeState S] (F : S → S) (H : BoundedHeight S) (n : Nat) :
    iter F H n ⊑ iter F H (n + 1) := le_merge_left _ _

/-- While the iteration is still moving, its height is at least its index. -/
theorem iter_height_grows [MergeState S] (F : S → S) (H : BoundedHeight S) :
    ∀ n, (∀ m, m < n → iter F H m ≠ iter F H (m + 1)) →
      n ≤ H.height (iter F H n) := by
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hne
    have hk : k ≤ H.height (iter F H k) := ih (fun m hm => hne m (Nat.lt_succ_of_lt hm))
    have hlt : H.height (iter F H k) < H.height (iter F H (k + 1)) :=
      H.height_lt _ _ (iter_le_succ F H k) (hne k (Nat.lt_succ_self k))
    omega

/-- **The iteration stabilizes** — within the height bound, because it cannot
keep climbing past the ceiling. This is where "finite" is spent, and it is the
only place. -/
theorem iter_stabilizes [MergeState S] (F : S → S) (H : BoundedHeight S) :
    ∃ m, iter F H m = iter F H (m + 1) :=
  Classical.byContradiction fun hc => by
    have hne : ∀ m, iter F H m ≠ iter F H (m + 1) := fun m h => hc ⟨m, h⟩
    have h := iter_height_grows F H (H.bound + 1) (fun m _ => hne m)
    have h2 := H.height_le (iter F H (H.bound + 1))
    omega

/-- Every iterate is below every pre-fixed point: the leastness induction, which
needs monotonicity of `F` and nothing else. -/
theorem iter_le_of_prefixed [MergeState S] {F : S → S} (H : BoundedHeight S)
    (hmono : MonotoneLeq F) {y : S} (hy : F y ⊑ y) : ∀ n, iter F H n ⊑ y := by
  intro n
  induction n with
  | zero => exact H.bot_least y
  | succ k ih => exact merge_le_iff.mpr ⟨ih, leq_trans (hmono _ _ ih) hy⟩

/-- **CLAIM 3, SECOND VERSION: a monotone derivation on a bounded-height carrier
has a least fixed point.** Self-dependence is permitted — `F` may read the very
value it computes — and the recursive system still has a canonical solution:
`F x = x`, and `x` is below every pre-fixed point `F y ⊑ y`, hence below every
fixed point.

This is the *only* statement in this file that is a fixed-point theorem, and it
is stated here rather than in §§1–2 because it is the only one where the
recursion is real. Its proof is the elementary bounded-height Knaster–Tarski:
stabilization from the height ceiling (`iter_stabilizes`), leastness from
monotonicity (`iter_le_of_prefixed`), and antisymmetry to turn the pre-fixed
point into a fixed one. -/
theorem finite_monotone_lfp [MergeState S] (F : S → S) (H : BoundedHeight S)
    (hmono : MonotoneLeq F) :
    ∃ x : S, F x = x ∧ ∀ y : S, F y ⊑ y → x ⊑ y := by
  obtain ⟨m, hm⟩ := iter_stabilizes F H
  refine ⟨iter F H m, ?_, fun y hy => iter_le_of_prefixed H hmono hy m⟩
  have hpre : F (iter F H m) ⊑ iter F H m := by
    show F (iter F H m) ⊔ iter F H m = iter F H m
    rw [merge_comm]
    exact hm.symm
  have hbelow : ∀ n, iter F H n ⊑ iter F H m := iter_le_of_prefixed H hmono hpre
  have hup : ∀ n, iter F H n ⊑ F (iter F H m) := by
    intro n
    induction n with
    | zero => exact H.bot_least _
    | succ k ih => exact merge_le_iff.mpr ⟨ih, hmono _ _ (hbelow k)⟩
  exact leq_antisymm hpre (hup m)

/-- **A join homomorphism is monotone**, so every derivation §2 licenses is a
legitimate `F` for §5 — the two claims meet here, and the meeting point is
`JoinHom.joinHom_implies_monotone` rather than a new hypothesis. -/
theorem joinHom_lfp [MergeState S] (F : S → S) (H : BoundedHeight S)
    (hF : JoinHom F) : ∃ x : S, F x = x ∧ ∀ y : S, F y ⊑ y → x ⊑ y :=
  finite_monotone_lfp F H (joinHom_implies_monotone hF)

/-! ### §5.1 The hypothesis is inhabited

`BoundedHeight` is a premise, and a premise nothing satisfies makes §5 a theorem
about an empty class. The smallest derived lattice a loom actually renders — one
bit, "has anything arrived at all" — carries one. -/

/-- Two one-bit states agreeing at the only index are equal. -/
theorem unit_gset_ext {x y : GSet Unit} (h : x () = y ()) : x = y := by
  funext u
  cases u
  exact h

/-- **A one-bit derived lattice has bounded height.** `GSet Unit` — the carrier
of a yes/no derived view (`JoinHom.verdict_exists`'s answer at one position) —
with the indicator as its height and `1` as its ceiling. So §5 is not a theorem
about an empty class, and the class it is about is the one a renderer's badge
lives in. -/
def bitBoundedHeight : BoundedHeight (GSet Unit) where
  bot := fun _ => false
  bot_least := fun x => by
    funext u
    show (false || x u) = x u
    rfl
  height := fun s => JoinHom.bit (s ())
  bound := 1
  height_le := fun s => by cases s () <;> decide
  height_lt := fun x y hxy hne => by
    have hy : (x () || y ()) = y () := congrFun hxy ()
    cases hx : x () with
    | true =>
      rw [hx, Bool.true_or] at hy
      exact absurd (unit_gset_ext (hx.trans hy)) hne
    | false =>
      cases hy2 : y () with
      | true => decide
      | false => exact absurd (unit_gset_ext (hx.trans hy2.symm)) hne

/-- **A concrete least fixed point.** The self-dependent derivation "once anyone
has said anything, keep saying it" on the one-bit lattice has a least fixed
point, by §5 at `bitBoundedHeight`. Small, and the point is only that the
existential is inhabited by something the file constructed rather than
assumed. -/
theorem bit_lfp_exists :
    ∃ x : GSet Unit, (fun s : GSet Unit => s) x = x
      ∧ ∀ y : GSet Unit, (fun s : GSet Unit => s) y ⊑ y → x ⊑ y :=
  finite_monotone_lfp (fun s => s) bitBoundedHeight (fun _ _ h => h)

/-! ## §6. THE RENDERER PAYOFF — one interface, two kinds of document.

Codex: *"the UI-reuse claim needs only 1 and a shared renderer interface."* This
section is that sentence discharged. Claim 1 supplies a section of the encoding;
`RenderSix.lean` supplies the interface; and the connecting lemma is small,
which is the honest report: **the six-status machinery applies to the derived
document by construction, and the transport is a general lemma about sections
rather than anything about documents.**

What is actually gained: a consumer written once against `RenderSix.Carrier6`
serves primary evidence and derived documents alike, and the honesty guarantees
it relies on — an `absent` badge is a promise about every permitted future, a
`pending` badge is escapable — hold at the document carrier by the *same*
theorem (`RenderSix.statusOf_sound6`), not by a look-alike. -/

/-- **A sound six-status evaluator transports along any retraction.** Reindex
the state space by `φ`, with `ψ` a section of it, and every clause of
`RenderSix.SoundEvaluator6` follows: the four `exact`/`absent` clauses are
direct, and `pending_escapable` — the only clause that must *produce* a state —
uses the section to pull the escaping future back.

General, and flagged as new content: no lemma of this shape existed, and the
confluence-free content is entirely `RenderSix`'s. -/
theorem sound6_transport {S' T β : Type} {F : Evidence.Future T} {answer : T → GSet β}
    {peval : T → Status β} (φ : S' → T) (ψ : T → S') (hφψ : ∀ t, φ (ψ t) = t)
    (h : RenderSix.SoundEvaluator6 F answer peval) :
    RenderSix.SoundEvaluator6 (fun a b => F (φ a) (φ b)) (fun s => answer (φ s))
      (fun s => peval (φ s)) where
  exact_correct := fun s v hv => h.exact_correct (φ s) v hv
  exact_final := fun s t v hf hv => h.exact_final (φ s) (φ t) v hf hv
  absent_correct := fun s hv => h.absent_correct (φ s) hv
  absent_final := fun s t hf hv => h.absent_final (φ s) (φ t) hf hv
  pending_escapable := fun s hv => by
    obtain ⟨t, hft, hne⟩ := h.pending_escapable (φ s) hv
    exact ⟨ψ t, by rw [hφψ]; exact hft, by rw [hφψ]; exact hne⟩

/-- The six-status badge of a derived document: decode and read
`ResultStatus.statusOf`. -/
noncomputable def docStatus (d : EvidenceDoc Holes.Val) : Status Holes.Val :=
  statusOf (decodeEvidence d)

/-- The answer set a derived document carries. -/
noncomputable def docValues (d : EvidenceDoc Holes.Val) : GSet Holes.Val :=
  Evidence.values (decodeEvidence d)

/-- The sealed future at the document carrier: the evidence-level sealed future,
read through the decoding. Because §1's encoding is an isomorphism, this is the
same relation transported, not a new notion. -/
def DocSealed (d d' : EvidenceDoc Holes.Val) : Prop :=
  Evidence.SealedFuture (decodeEvidence d) (decodeEvidence d')

/-- **THE CONNECTING LEMMA — and it is small.** The badge read off a derived
document is the badge read off the evidence it encodes, definitionally. That is
the whole of "one renderer serves both": there is nothing to reconcile, because
the document *is* the evidence at a different index. -/
theorem docStatus_encodeEvidence (e : Evidence.ResultEvidence Holes.Val) :
    docStatus (encodeEvidence e) = statusOf e := rfl

/-- **The six-status honesty contract holds at the document carrier.**
`RenderSix.statusOf_sound6` transported along §1's isomorphism: `exact` reports
are true and irrevocable, `absent` reports are true and irrevocable, `pending`
reports are escapable — for derived documents, by the same theorem that gives it
for evidence. -/
theorem docStatus_sound6 : RenderSix.SoundEvaluator6 DocSealed docValues docStatus :=
  sound6_transport decodeEvidence encodeEvidence decode_encode RenderSix.statusOf_sound6

/-- The deployed six-status carrier over derived documents. -/
def docCarrier6 : RenderSix.Carrier6 DocSealed Holes.Val :=
  RenderSix.stdCarrier6 _ _

/-- **The sanctioned renderer for derived documents**: report `docStatus` at the
document it read. -/
noncomputable def renderDoc (C : RenderSix.Carrier6 DocSealed Holes.Val)
    (d : EvidenceDoc Holes.Val) : C.R := C.report d (docStatus d)

/-- …and it is honest, by `RenderSix.soundEvaluator6_renders_honestly` over the
contract above. -/
theorem renderDoc_honest (C : RenderSix.Carrier6 DocSealed Holes.Val) :
    RenderSix.HonestRenderer6 DocSealed docValues C (renderDoc C) :=
  RenderSix.soundEvaluator6_renders_honestly C docStatus_sound6

/-- The derived document of a definitively-absent result carries the `absent`
badge. -/
theorem docStatus_emptyClosed :
    docStatus (encodeEvidence ResultStatus.emptyClosedW) = Status.absent :=
  ResultStatus.statusOf_emptyClosedW

/-- The derived document of a nothing-observed-yet result carries the `pending`
badge. -/
theorem docStatus_emptyOpen :
    docStatus (encodeEvidence ResultStatus.emptyOpenW) = Status.pending :=
  ResultStatus.statusOf_emptyOpenW

/-- **The absence badge on a DERIVED document is backed.** `RenderSix`'s
`renderedAbsent_implies_absent_forever` at the document renderer: a "no results"
badge on a derived document is a promise that the answer set is empty at *every*
permitted future of that document, not merely now.

This is the payoff stated honestly: the guarantee is `RenderSix`'s, the carrier
is derived, and nothing was re-proved to move it here. -/
theorem derived_absence_badge_is_backed :
    RenderSix.AbsenceCert DocSealed docValues
      (encodeEvidence ResultStatus.emptyClosedW) :=
  RenderSix.renderedAbsent_implies_absent_forever (renderDoc_honest docCarrier6)
    ((RenderSix.std6_says _ _ _ _).mpr docStatus_emptyClosed)

/-- **The spinner badge on a derived document is escapable.** The other new
guarantee, likewise transported: a derived document showing "loading" has a
permitted future at which it is not loading. -/
theorem derived_pending_badge_can_end :
    ∃ t, DocSealed (encodeEvidence ResultStatus.emptyOpenW) t
      ∧ ¬ docCarrier6.Says (renderDoc docCarrier6 t) Status.pending :=
  RenderSix.renderedPending_implies_the_wait_can_end (renderDoc_honest docCarrier6)
    ((RenderSix.std6_says _ _ _ _).mpr docStatus_emptyOpen)

/-- **ONE CONSUMER, TWO KINDS OF DOCUMENT.** A single six-handler consumer,
written once, reads the derived documents of the two zero-candidate results and
tells them apart — the distinction `RenderSix.six_carrier_separates` earns for
primary evidence, now available at the derived carrier with the same handlers.

Together with `docStatus_encodeEvidence` this is codex's UI-reuse claim in full:
claim 1 supplies the representation, `RenderSix` supplies the interface, and the
badge does not change when the evidence becomes a document. -/
theorem one_renderer_serves_both :
    docCarrier6.elim (renderDoc docCarrier6 (encodeEvidence ResultStatus.emptyClosedW))
        (fun _ => false) (fun _ => false) false false false true = false
      ∧ docCarrier6.elim (renderDoc docCarrier6 (encodeEvidence ResultStatus.emptyOpenW))
        (fun _ => false) (fun _ => false) false false false true = true := by
  constructor
  · show docCarrier6.elim (docCarrier6.report _ (docStatus _)) _ _ _ _ _ _ = _
    rw [docStatus_emptyClosed, RenderSix.elim_absent]
  · show docCarrier6.elim (docCarrier6.report _ (docStatus _)) _ _ _ _ _ _ = _
    rw [docStatus_emptyOpen, RenderSix.elim_pending]

/-! ## §7. The three claims, side by side.

One statement, so the decomposition is checkable against the file rather than
against the header. Read the shapes: claims 1 and 2 are equations (closure),
claim 3 is an existence-and-uniqueness (recursion). -/

/-- **CODEX'S THREE CLAIMS, AS THIS FILE LEAVES THEM.**

  1. **Representation closure** — encoding preserves merge, and loses nothing.
  2. **Merge closure** — deriving commutes with merging, for every deterministic
     computation; **and** it is a real requirement, because a document-valued
     derivation of the count is mergeable by no combiner whatsoever.
  3. **Recursion** — a rank-grounded pipeline terminates with a unique
     materialization.

The negative conjunct is deliberately inside the statement: claims 1 and 2 are
independent, and without the count's refutation "the derived value is a
document" would read as if it implied "the derived value merges". -/
theorem the_three_claims {α : Type} (f : Holes.World → α)
    (src : Holes.World → Evidence.Source) (obl cert : GSet Evidence.Source)
    {D : Type} [Inhabited D] (P : Stratified D) :
    (∀ e₁ e₂ : Evidence.ResultEvidence α,
        encodeEvidence (e₁ ⊔ e₂) = encodeEvidence e₁ ⊔ encodeEvidence e₂)
      ∧ (∀ e₁ e₂ : Evidence.ResultEvidence α,
          encodeEvidence e₁ = encodeEvidence e₂ → e₁ = e₂)
      ∧ (∀ W₁ W₂ : GSet Holes.World,
          deriveDoc f src obl cert (W₁ ⊔ W₂)
            = deriveDoc f src obl cert W₁ ⊔ deriveDoc f src obl cert W₂)
      ∧ RequiresEvidence tallyDoc
      ∧ Materializes P (materialize P)
      ∧ (∀ σ, Materializes P σ → σ = materialize P) :=
  ⟨encodeEvidence_merge, fun _ _ h => encodeEvidence_injective h,
   deriveDoc_merge f src obl cert, tallyDoc_requires_evidence,
   (stratified_derive_terminates P).1, (stratified_derive_terminates P).2⟩

end Uwueave.DerivedDocument
