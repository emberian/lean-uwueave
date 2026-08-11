/-
# Uwueave.Wellformed — the Grove property: a merge is still a DOCUMENT.

Every other invariant in this library is an *application* invariant — "at most
one pin", "the budget is 10", "the balance is non-negative" — and the whole
judgement (`Confluence.lean`) is about whether a merge keeps it. That question
has a companion the library never asked:

> when a merge *breaks* an application invariant, is the result still a
> well-formed document?

**Grove** — Michael D. Adams, Eric Griffis, Thomas J. Porter, Sundara Vishnu
Satish, Eric Zhao, Cyrus Omar, *"Grove: A Bidirectionally Typed Collaborative
Structure Editor Calculus"*, **POPL 2025**, doi `10.1145/3704909` — answers
"yes" for a collaborative *structure editor*: its edit log is a CmRDT, its
relocation conflicts are represented explicitly with holes and cross-tree
references, and **every editor state remains statically meaningful** — no
sequence of concurrent edits can produce a state the type system rejects.
Conflicts are represented, never crashed on.

⚠ **CITED, NOT READ.** The paper is not in this repo's paperbin and no author
of this file has read it; the description above is the brief this module was
written against, and it matches `docs/BIBLIOGRAPHY.md`'s entry, which is
itself flagged *NOT ARCHIVED — relayed from an external review*. Every
sentence attributed to Grove here inherits that indirection. Read the primary
source before citing this file's framing of it.

## What this module builds

`WellFormed` (§2) — a **structural** predicate on a composed loom document:
every reference resolves, every anchor is present, every sequence linearizes,
every conflict record is a legal conflict record. Then the headline:

  * **`merge_preserves_wellformed` (§3)** — the merge of two well-formed
    documents is well-formed. No side hypothesis, no application invariant, no
    reachability premise, no agreement premise. This is the theorem Grove has
    and we lacked.
  * **`mergeAll_wellformed` (§3)** — the same over a whole gossip round: fold
    any list of well-formed replicas into a well-formed base and the result is
    well-formed. Grove's property is about *sequences* of concurrent edits;
    this is its state-based shadow.

And then the point of the whole exercise — the **separation** (§4), because
without it "well-formed" is just a new name for the invariants we already had:

  * `wellFormed_iconfluent` versus `onePin_not_iconfluent` — two predicates on
    **the same document type**, one free, one refuted, so the notions
    genuinely differ.
  * `merged_doc_violates_onePin_but_is_wellFormed` — the merge of two
    single-pin documents has two pins and is **still a well-formed document**.
    It is an *illegal* document, and it is a document. A UI can open it.
  * `wellFormed_and_onePin_not_iconfluent` — **all** of this document's
    coordination cost sits in the application conjunct; well-formedness
    contributes none of it.
  * both non-implications (`wellFormed_not_implies_onePin`,
    `onePin_not_implies_wellFormed`), so neither predicate is the other in
    disguise.

§5 shows the conflict is *represented*: where `OnePin` fails, the merged
document carries both pins, both resolve to nodes that exist, and both nodes
have content to render — `pin_conflict_renderable`. Concurrent edits to one
node both surface in the register view (`content_conflict_surfaces`), riding
`MVRegister.conflict_surfaces` and the retention stance `ORMap.lean` argues
for at map level (conflicts retained, policy left to the view).

§6 is the implementor-facing corollary: `no_crash` — **every reader defined on
well-formed documents is total on merges of well-formed documents**, for every
reader, not a list of them — plus the concrete readers a loom UI actually
runs (`merge_renders`: bookmark resolution, pin resolution, the never-blank
content pane, the text linearization), and `readPinned_total_on_merge`, a
reader whose totality genuinely needs well-formedness, so the quantifier is
not vacuous. §6 also proves the sharpest conjunct is not decoration:
`horizon_conjunct_is_load_bearing` plants a register that is non-empty and
displays **nothing**, and shows `WellFormed` rejects the resulting document at
exactly that conjunct.

## The document, and why it is WeaveState's plus exactly one field

`WovenDoc := WeaveState.WeaveDoc × (Text × Horizon)`.

The left factor is `WeaveState.lean`'s deployed schema **verbatim** — same
nodes, bookmarks, contents, activation, grants, revocations, pins, quota, and
the same deliberately-poisoned pin ceiling, which is why §4's clash reuses
`WeaveState.pinA` / `pinB` / `pins_clash` rather than inventing a fresh one.
Two fields are added, and only two:

  * `Text : NodeId → Sequence.SeqState` — per-node anchored text. Required,
    not decorative: "every sequence linearizes" has **no referent** on
    `WeaveDoc`, whose header says text inside a node is out of scope
    (`SeqKernel.lean`'s problem). A well-formedness predicate with no
    linearizable structure in it would be missing the most interesting field.
  * `Horizon : Clock` — the replica's own version vector, merged by
    componentwise max like any vector clock. It is what makes "a legal
    conflict record" *sayable*: a write whose clock is outside the horizon is
    not a write this document can account for, and (§6) it is boundedness
    against the horizon that makes the MV-register's conflict view
    **inhabited** — a non-blank content pane is a theorem, not a hope.

So: not a miniature, an extension — the real schema plus the field the
property needs. The world is still `WeaveState`'s miniature (two users, `Nat`
ids, root scope 9, budget 10), and that is upstream's stated boundary.

## What our analogue does and does not capture

Grove is a **calculus**: a term language, a bidirectional typing judgement,
an operational semantics, an edit log that is a CmRDT, holes and cross-tree
references as the *representation* of a relocation conflict. This module is
none of that. It is a **state-based structural predicate** over a record of
CvRDT fields, and its theorem is about the join of two states.

  * ⟨UNDONE⟩ **No bidirectional typing — no typing at all.** There is no term
    language here, so "well-typed" has no referent and `WellFormed` is not a
    typing judgement; it is referential integrity plus per-structure
    well-formedness. Building a typed AST with a judgement over it is real
    work that nobody here has done, not a fact about the world.
  * ⟨UNDONE⟩ **No edit-log CmRDT, so this is not Grove's quantifier.** Grove
    (as reported) quantifies over *sequences of concurrent edits*; we
    quantify over *pairs (and folds) of states*. Ours needs no reachability
    premise, which is stronger in one direction — but it says **nothing about
    whether an edit preserves well-formedness**, because operations are not
    modeled in this file. `Exec.lean` / `Traces.lean` are where that bridge
    would be built; it is not built.
  * ⟨UNDONE⟩ **No cross-tree references and no holes.** Our conflict
    representation is *retention* — both pins present, both writes in view —
    not a hole term carrying provenance. Retention is a different
    representation, not a weaker one, but nothing here defines how a renderer
    should present it, and there is no relocation to represent in the first
    place (`Move.lean` prices node moves as an op-log with a derived view and
    refuses them as replicated state).
  * ⟨TERMINAL⟩ **`WellFormed` is deliberately not application-legal.** A
    two-pin document satisfies it. That is the entire design; a predicate
    that rejected two pins would be `weaveDocInv`, and `weaveDocInv` is not
    I-confluent (`WeaveState.weaveDocSeamVerdict.escalatesGlobally`).
  * ⟨TERMINAL⟩ **`UniqueAnchor` is not a conjunct, and cannot be.**
    `Sequence.wf_unique_anchor_not_iconfluent` refutes it: adding it would
    make the headline **false**. The consequence is honest and load-bearing —
    a merged document may show one element id **twice** in `linearize`
    (`Sequence.dup_id_appears_twice`). It still linearizes: total, in-bounds,
    every present element appears, every non-root anchor precedes. So the
    document stays *statically meaningful* and may still read wrong. A
    content-addressed id scheme discharges the gap cryptographically
    (`Sequence.uniqueAnchor_violation_extracts_collision`), which is a
    collision-resistance premise about a deployment's hash, not a theorem.
  * ⟨TERMINAL⟩ **Structural ≠ intended.** `Sequence.interleaving_anomaly`
    stands: a well-formed merge can interleave two users' runs. Intention
    preservation is not formalized anywhere in this repo, and `WellFormed`
    does not smuggle it in.
  * ⟨UNDONE⟩ **The horizon is a premise on the write path.** `WellFormed`
    requires every write's clock to sit under the document's horizon. Nothing
    in this file checks that the shipping write path maintains that — it is
    an operation-level obligation of the same family as `Authority.lean`'s
    signature premises, and it is unmodeled here.

Both directions of falsifiability are named rather than assumed:
`docX_wellFormed` inhabits the predicate and `wellFormed_refutable` exhibits a
document it rejects, so `WellFormed` is neither vacuous nor trivially true.
-/
import Uwueave.WeaveState
import Uwueave.Sequence

namespace Uwueave.Wellformed

open Uwueave Uwueave.Catalog Uwueave.Causality Uwueave.MVRegister Uwueave.Spec

/-! ## §1. The document

`WeaveState.WeaveDoc` verbatim, plus per-node text and the replica horizon.
Every instance is inherited: **zero new merge proofs**, exactly as
`WeaveState.lean` insists. -/

/-- Node ids — `WeaveState.NodeId`, restated so this file reads standalone. -/
abbrev NodeId := Nat

/-- The two-user miniature — `WeaveState.User`. -/
abbrev User := Bool

/-- Per-node anchored text: one `Sequence.SeqState` per node. The field
`WeaveState.WeaveDoc` deliberately omits, added here because "every sequence
linearizes" needs a sequence. -/
abbrev Text := NodeId → Sequence.SeqState

/-- The replica's version vector: the causal horizon every write must sit
under. Merged by componentwise max (the product-of-`Nat`-max instance) — an
ordinary vector clock, `Causality.Clock`. -/
abbrev Horizon := Clock

/-- **The woven document.** The deployed loom schema, plus per-node text, plus
the horizon. -/
abbrev WovenDoc := WeaveState.WeaveDoc × (Text × Horizon)

/-- Zero new merge proofs: the whole document's join is assembled by the
product and pointwise instances. -/
example : MergeState WovenDoc := inferInstance

/-- The grow-only causal node set. -/
abbrev nodes (d : WovenDoc) : GSet NodeId := WeaveState.nodes d.1
/-- Each user's grow-only bookmark set. -/
abbrev bookmarks (d : WovenDoc) : User → GSet NodeId := WeaveState.bookmarks d.1
/-- Per-node contents: a multi-value register per node. -/
abbrev contents (d : WovenDoc) : NodeId → MVReg := WeaveState.contents d.1
/-- The delegation DAG. -/
abbrev grants (d : WovenDoc) : Authority.GrantSet := WeaveState.grants d.1
/-- The pinned-node set — the deliberately-kept application ceiling. -/
abbrev pins (d : WovenDoc) : GSet NodeId := WeaveState.pins d.1
/-- Per-node anchored text. -/
abbrev text (d : WovenDoc) : Text := d.2.1
/-- The replica's causal horizon. -/
abbrev horizon (d : WovenDoc) : Horizon := d.2.2

/-! ## §2. Well-formedness — the structural predicate

Six conditions, one per structure that can *dangle*. Every one of them is a
question a **renderer** asks, not a question the application's rules ask: can
this reference be followed, is this anchor there, does this traversal
terminate, is this conflict record one I can display. The pin field is the
sharpest illustration and it is why the field is here: *"every pin resolves to
a node"* is structural and lives below, *"there is at most one pin"* is the
application rule and lives in §4 — same field, opposite verdicts. -/

/-- **A well-formed document.** Structural well-formedness, as a conjunction
of per-field conditions over the schema. `n` bounds text element ids and
`root` is the authority root scope; both are parameters of the *predicate*,
identical on premises and conclusion of every theorem below — they are never
hypotheses relating two documents.

Deliberately **absent**, each for a stated reason:

  * *anything about pin cardinality, the budget, or activation timestamps* —
    those are application rules (§4), and a structural predicate that rejected
    them could not survive a merge;
  * *`Sequence.UniqueAnchor`* — not I-confluent
    (`Sequence.wf_unique_anchor_not_iconfluent`); including it makes
    `merge_preserves_wellformed` false;
  * *any condition on `revocations`* — a revocation naming a grant this
    replica has not received yet is **early, not malformed**; demanding
    referential integrity there would refuse a legal partition state.
    (`WeaveState.lean` makes the same call for the same reason: the
    revocation set's guarantees are view-level and fail-closed.) -/
structure WellFormed (n root : Nat) (d : WovenDoc) : Prop where
  /-- **Every bookmark resolves.** For every user, every bookmarked id is an
  existing node — the foreign key a UI follows to draw the bookmark list. -/
  bookmarksResolve : ∀ u, PointsAtExisting (nodes d) (bookmarks d u)
  /-- **Every pin resolves.** The *structural* half of the pin field: whatever
  is pinned is a node that exists. Says nothing about how many. -/
  pinsResolve : PointsAtExisting (nodes d) (pins d)
  /-- **Every existing node has content.** A node is created with its initial
  write (content-addressed: the id is derived from the content), so a node
  whose register is empty is a dangling node, not an empty one. This is the
  cross-field condition that makes the content pane renderable. -/
  contentPresent : ∀ k, nodes d k = true → ∃ w, contents d k w = true
  /-- **Every conflict record is legal**: every write in every register
  carries a clock inside the document's horizon. This is what rules out a
  register whose writes ascend forever — the register that is non-empty and
  yet displays *nothing*, because no write is maximal. §6 turns it into
  `content_view_inhabited`. -/
  writesInHorizon : ∀ k w, contents d k w = true → Clock.le w.2 (horizon d)
  /-- **Every sequence linearizes**: each node's text is `Sequence.WF n` —
  ids in bounds, every anchor strictly older than what it anchors, every
  anchor either the root sentinel or itself present. This is exactly what
  `linearize` needs to terminate and to place every element. -/
  textLinearizes : ∀ k, Sequence.WF n (text d k)
  /-- **Every grant resolves**: the delegation DAG is `Authority.WF root` —
  every grant's parent exists (or is the root) and scope only narrows. -/
  grantsResolve : Authority.WF root (grants d)

/-! ## §3. The headline

The merge of two well-formed documents is well-formed. Four of the six
conjuncts are one line each, and every one of those lines is an **existing**
theorem of this library applied at the right projection — referential
integrity over grow-only sets, RGA well-formedness, grant-DAG
well-formedness. That is the composition algebra doing its job; the only new
arguments are the two cross-field conjuncts (`contentPresent`,
`writesInHorizon`), and both are the `grounded_iconfluent` shape: a fact about
one element of a grow-only set, plus monotonicity of the thing it points at. -/

/-- **THE THEOREM. The merge of two well-formed documents is a well-formed
document — unconditionally.**

There are no hypotheses beyond well-formedness of the two operands. No
agreement premise (contrast `WeaveState.weaveDoc_segmented`, which needs
`docSeam a = docSeam b`), no application invariant, no reachability or causal
delivery premise, no bound relating the two documents. `n` and `root` are
parameters of `WellFormed` itself and appear identically on both premises and
the conclusion; they say nothing about the operands' relationship.

Read at the keyboard: **sync can never hand you a broken document.** It can
hand you an *illegal* one — two pins, an over-drawn budget — and §4 proves it
does; what it cannot do is hand you one whose references dangle, whose
anchors are missing, whose text will not lay out, or whose conflict records
cannot be displayed. That is Grove's guarantee, in this library's setting and
at this library's much smaller resolution. -/
theorem merge_preserves_wellformed (n root : Nat) (d e : WovenDoc)
    (hd : WellFormed n root d) (he : WellFormed n root e) :
    WellFormed n root (d ⊔ e) where
  bookmarksResolve u :=
    pointsAtExisting_iconfluent (nodes d, bookmarks d u) (nodes e, bookmarks e u)
      (hd.bookmarksResolve u) (he.bookmarksResolve u)
  pinsResolve :=
    pointsAtExisting_iconfluent (nodes d, pins d) (nodes e, pins e)
      hd.pinsResolve he.pinsResolve
  contentPresent k hk := by
    cases (Bool.or_eq_true _ _).mp (hk : (nodes d k || nodes e k) = true) with
    | inl h =>
      obtain ⟨w, hw⟩ := hd.contentPresent k h
      exact ⟨w, by show (contents d k w || contents e k w) = true; simp [hw]⟩
    | inr h =>
      obtain ⟨w, hw⟩ := he.contentPresent k h
      exact ⟨w, by show (contents d k w || contents e k w) = true; simp [hw]⟩
  writesInHorizon k w hw := by
    have hor : (contents d k w || contents e k w) = true := hw
    cases (Bool.or_eq_true _ _).mp hor with
    | inl h =>
      have hle : w.2.1 ≤ (horizon d).1 ∧ w.2.2 ≤ (horizon d).2 :=
        hd.writesInHorizon k w h
      exact ⟨Nat.le_trans hle.1 (Nat.le_max_left _ _),
             Nat.le_trans hle.2 (Nat.le_max_left _ _)⟩
    | inr h =>
      have hle : w.2.1 ≤ (horizon e).1 ∧ w.2.2 ≤ (horizon e).2 :=
        he.writesInHorizon k w h
      exact ⟨Nat.le_trans hle.1 (Nat.le_max_right _ _),
             Nat.le_trans hle.2 (Nat.le_max_right _ _)⟩
  textLinearizes k :=
    Sequence.wf_iconfluent n (text d k) (text e k)
      (hd.textLinearizes k) (he.textLinearizes k)
  grantsResolve :=
    Authority.wf_iconfluent root (grants d) (grants e)
      hd.grantsResolve he.grantsResolve

/-- The headline in the library's own judgement form: structural
well-formedness is **I-confluent**. By Bailis et al.'s necessary-and-sufficient
result (cited in `Confluence.lean`, not re-proved), a coordination-free
convergent implementation of a document that stays well-formed exists — the
loom never has to stop and agree in order to remain a loom. -/
theorem wellFormed_iconfluent (n root : Nat) : IConfluent (WellFormed n root) :=
  merge_preserves_wellformed n root

/-- A whole gossip round: fold a list of replicas into a base. -/
def mergeAll : WovenDoc → List WovenDoc → WovenDoc
  | base, [] => base
  | base, d :: ds => mergeAll (base ⊔ d) ds

/-- **The fold version — the closest state-based shadow of Grove's "no
sequence of concurrent edits".** Merge in any finite list of well-formed
replicas, in any order, and the result is a well-formed document. (Order is
immaterial by the merge laws; this statement does not need that, since it
holds for *every* list.) What it is still not: a statement about *edits*.
Operations are not modeled in this file — see the header's ⟨UNDONE⟩ note. -/
theorem mergeAll_wellformed (n root : Nat) :
    ∀ (ds : List WovenDoc) (base : WovenDoc), WellFormed n root base →
      (∀ d ∈ ds, WellFormed n root d) → WellFormed n root (mergeAll base ds) := by
  intro ds
  induction ds with
  | nil => intro base hb _; exact hb
  | cons d ds ih =>
    intro base hb hall
    exact ih (base ⊔ d)
      (merge_preserves_wellformed n root base d hb (hall d (by simp)))
      (fun e he => hall e (by simp [he]))

/-! ## §4. The separation — why this is not a renaming

Everything above would be worth little if `WellFormed` were just the
application invariant under a new name. These are the theorems that say it is
not: on **one document type**, one predicate is free and another is refuted;
neither implies the other; and the merge that breaks the application rule is
still a document.

The clash is `WeaveState.lean`'s, reused rather than reinvented —
`WeaveState.pinA`, `WeaveState.pinB`, `WeaveState.pins_clash`. The
contribution here is that the same merge is now *shown to be well-formed*. -/

/-- The application rule: at most one pinned node, document-wide.
`WeaveState.pinsVerdict`'s invariant, read at woven-document scale. -/
def OnePin (d : WovenDoc) : Prop :=
  ∀ m k, pins d m = true → pins d k = true → m = k

/-- Nodes 0 and 1 both exist. -/
def twoNodes : GSet NodeId := fun k => k == 0 || k == 1

/-- Both users bookmark node 0. -/
def bothBookmark : User → GSet NodeId := fun _ => fun k => k == 0

/-- A witness document: the shared two-node core, with the pin set, the
per-node register, the per-node text and the horizon left open. Everything
else is `WeaveState`'s demo material (`demoChain`, `noRevs`, `quota₀`). -/
def mkDoc (pin : GSet NodeId) (cts : NodeId → MVReg) (txt : Text) (h : Horizon) :
    WovenDoc :=
  ((((twoNodes, bothBookmark),
     (cts, ((fun _ _ => (⟨1, 0⟩ : LWW)),
            (Authority.demoChain, Authority.noRevs)))),
    (pin, WeaveState.quota₀)),
   (txt, h))

/-- Replica X's text on every node: element 1 at the root. -/
def txtX : Text := fun _ => fun p => p == ((1 : Nat), (0 : Nat))
/-- Replica Y's text on every node: element 2 at the root. -/
def txtY : Text := fun _ => fun p => p == ((2 : Nat), (0 : Nat))

/-- **Replica X**: pins node 0, writes `MVRegister.wA` at clock `(1,0)`. -/
def docX : WovenDoc :=
  mkDoc WeaveState.pinA (fun _ => single wA) txtX (1, 0)

/-- **Replica Y**: pins node 1, writes `MVRegister.wB` at clock `(0,1)` —
concurrent with X's write, and a different pin. Both replicas are legal; they
have simply been apart. -/
def docY : WovenDoc :=
  mkDoc WeaveState.pinB (fun _ => single wB) txtY (0, 1)

private theorem twoNodes_of_eq_zero : twoNodes 0 = true := by decide
private theorem twoNodes_of_eq_one : twoNodes 1 = true := by decide

private theorem bookmarks_resolve_shared (u : User) :
    PointsAtExisting twoNodes (bothBookmark u) := by
  intro m hm
  have hm' : (m == (0 : NodeId)) = true := hm
  have : m = 0 := by simpa using hm'
  subst this
  exact twoNodes_of_eq_zero

private theorem txtX_wf (k : NodeId) : Sequence.WF 5 (txtX k) := by
  intro i a h
  have h' : ((i, a) == ((1 : Nat), (0 : Nat))) = true := h
  simp at h'
  obtain ⟨rfl, rfl⟩ := h'
  exact ⟨by omega, by omega, Or.inl rfl⟩

private theorem txtY_wf (k : NodeId) : Sequence.WF 5 (txtY k) := by
  intro i a h
  have h' : ((i, a) == ((2 : Nat), (0 : Nat))) = true := h
  simp at h'
  obtain ⟨rfl, rfl⟩ := h'
  exact ⟨by omega, by omega, Or.inl rfl⟩

/-- Replica X is a well-formed document. -/
theorem docX_wellFormed : WellFormed 5 9 docX where
  bookmarksResolve := bookmarks_resolve_shared
  pinsResolve := by
    intro m hm
    have hm' : (m == (0 : NodeId)) = true := hm
    have : m = 0 := by simpa using hm'
    subst this
    exact twoNodes_of_eq_zero
  contentPresent := fun _ _ => ⟨wA, rfl⟩
  writesInHorizon := by
    intro _ w hw
    have hw' : (w == wA) = true := hw
    have : w = wA := by simpa using hw'
    subst this
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  textLinearizes := txtX_wf
  grantsResolve := Authority.demoChain_wf

/-- Replica Y is a well-formed document. -/
theorem docY_wellFormed : WellFormed 5 9 docY where
  bookmarksResolve := bookmarks_resolve_shared
  pinsResolve := by
    intro m hm
    have hm' : (m == (1 : NodeId)) = true := hm
    have : m = 1 := by simpa using hm'
    subst this
    exact twoNodes_of_eq_one
  contentPresent := fun _ _ => ⟨wB, rfl⟩
  writesInHorizon := by
    intro _ w hw
    have hw' : (w == wB) = true := hw
    have : w = wB := by simpa using hw'
    subst this
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  textLinearizes := txtY_wf
  grantsResolve := Authority.demoChain_wf

/-- Each replica satisfies the application rule on its own. -/
theorem docX_onePin : OnePin docX := WeaveState.pinA_atMostOne
/-- Likewise. -/
theorem docY_onePin : OnePin docY := WeaveState.pinB_atMostOne

/-- The merged pin set is literally `WeaveState.pinA ⊔ WeaveState.pinB` — the
clash is upstream's, transported by nothing more than a projection. -/
theorem pins_merged : pins (docX ⊔ docY) = WeaveState.pinA ⊔ WeaveState.pinB := rfl

/-- ⚠ The merge pins two nodes: `WeaveState.pins_clash`, read here. -/
theorem merged_violates_onePin : ¬ OnePin (docX ⊔ docY) :=
  fun h => WeaveState.pins_clash h

/-- ⚠ **The application rule is not I-confluent** — two offline users each
pin, the sync shows both pins. `WeaveState.pinsVerdict`'s ceiling at
woven-document scale. -/
theorem onePin_not_iconfluent : ¬ IConfluent OnePin :=
  fun h => merged_violates_onePin (h docX docY docX_onePin docY_onePin)

/-- **⭑ The separation, half one: the merged document that breaks the rule is
still a document.** Two well-formed, individually legal replicas; their merge
has two pins — and is well-formed. Both pins resolve, both nodes have content,
every bookmark still resolves, every text still linearizes, the grant DAG is
still a DAG. The conflict is *represented*: a UI opens this document, renders
"pinned: node 0, node 1", and asks the human. Nothing crashes and nothing is
silently dropped.

Contrast the two conclusions carefully — this is the whole point of the
module. `¬ OnePin (docX ⊔ docY)` is a real defect the application must have a
policy for (`Necessity.necessity`: no library cleverness removes it).
`WellFormed 5 9 (docX ⊔ docY)` says the defect is a *state you can look at*
rather than a state that rejects itself. -/
theorem merged_doc_violates_onePin_but_is_wellFormed :
    OnePin docX ∧ OnePin docY
    ∧ ¬ OnePin (docX ⊔ docY)
    ∧ WellFormed 5 9 (docX ⊔ docY) :=
  ⟨docX_onePin, docY_onePin, merged_violates_onePin,
   merge_preserves_wellformed 5 9 docX docY docX_wellFormed docY_wellFormed⟩

/-- **⭑ The separation, half two: the two notions genuinely differ.** On one
and the same document type, structural well-formedness is I-confluent and the
application rule is refuted. Neither is a restatement of the other, and no
lift carries one to the other. -/
theorem wellformed_and_onePin_differ :
    IConfluent (WellFormed 5 9) ∧ ¬ IConfluent OnePin :=
  ⟨wellFormed_iconfluent 5 9, onePin_not_iconfluent⟩

/-- **All of the coordination cost lives in the application conjunct.** The
conjunction `WellFormed ∧ OnePin` escalates — and by the previous theorems the
escalation is entirely `OnePin`'s, since the same witness pair leaves the
`WellFormed` conjunct intact. Operationally: coordinate about pins, never
about well-formedness. -/
theorem wellFormed_and_onePin_not_iconfluent :
    ¬ IConfluent (fun d => WellFormed 5 9 d ∧ OnePin d) :=
  fun h => merged_violates_onePin
    (h docX docY ⟨docX_wellFormed, docX_onePin⟩ ⟨docY_wellFormed, docY_onePin⟩).2

/-- Well-formed does not imply legal — the merge is the witness. -/
theorem wellFormed_not_implies_onePin :
    ∃ d : WovenDoc, WellFormed 5 9 d ∧ ¬ OnePin d :=
  ⟨docX ⊔ docY,
   merge_preserves_wellformed 5 9 docX docY docX_wellFormed docY_wellFormed,
   merged_violates_onePin⟩

/-- A document pinning node 7, which does not exist. Legal by the application
rule (exactly one pin) and structurally broken (the pin dangles). -/
def docDangling : WovenDoc :=
  mkDoc (fun k => k == 7) (fun _ => single wA) txtX (1, 0)

/-- Legal does not imply well-formed: one pin, pointing at nothing. -/
theorem onePin_not_implies_wellFormed :
    ∃ d : WovenDoc, OnePin d ∧ ¬ WellFormed 5 9 d := by
  refine ⟨docDangling, ?_, ?_⟩
  · intro m k hm hk
    have hm' : (m == (7 : NodeId)) = true := hm
    have hk' : (k == (7 : NodeId)) = true := hk
    have hm7 : m = 7 := by simpa using hm'
    have hk7 : k = 7 := by simpa using hk'
    exact hm7.trans hk7.symm
  · intro h
    have := h.pinsResolve 7 (by decide)
    exact absurd this (by decide)

/-- **The floor is refutable.** `WellFormed` rejects something, so it is not
the constant `True` in disguise — the companion to `docX_wellFormed`, which
shows it is not the constant `False` either. -/
theorem wellFormed_refutable : ∃ d : WovenDoc, ¬ WellFormed 5 9 d :=
  let ⟨d, _, hbad⟩ := onePin_not_implies_wellFormed
  ⟨d, hbad⟩

/-! ## §5. Conflict representation — both sides, and both resolvable

Well-formedness is what *lets* a UI render the conflict. The theorems below
say what is actually in the merged document at the moment the application rule
fails: not a repair, not a winner — both sides, with every reference in them
resolving. This is `ORMap.lean`'s stance (conflicts retained, the policy left
to the view) and `MVRegister.lean`'s (`conflict_surfaces`) at document
scale. -/

/-- **⭑ Where the application rule fails, the document carries both sides —
and both sides are renderable.** If `d` pins `m` and `e` pins `k`, the merge
holds both pins; both resolve to nodes that exist; and both of those nodes
have content to display. So the renderer has everything it needs to draw a
two-pin document with both node titles and let the human choose. Note the
statement never assumes `m ≠ k`: when the replicas agree it degenerates to
one pin, which is the same theorem. -/
theorem pin_conflict_renderable (n root : Nat) {d e : WovenDoc}
    (hd : WellFormed n root d) (he : WellFormed n root e)
    {m k : NodeId} (hm : pins d m = true) (hk : pins e k = true) :
    pins (d ⊔ e) m = true ∧ pins (d ⊔ e) k = true
    ∧ nodes (d ⊔ e) m = true ∧ nodes (d ⊔ e) k = true
    ∧ (∃ w, contents (d ⊔ e) m w = true)
    ∧ (∃ w, contents (d ⊔ e) k w = true) := by
  have hwf := merge_preserves_wellformed n root d e hd he
  have hpm : pins (d ⊔ e) m = true := by
    show (pins d m || pins e m) = true; simp [hm]
  have hpk : pins (d ⊔ e) k = true := by
    show (pins d k || pins e k) = true; simp [hk]
  exact ⟨hpm, hpk, hwf.pinsResolve m hpm, hwf.pinsResolve k hpk,
         hwf.contentPresent m (hwf.pinsResolve m hpm),
         hwf.contentPresent k (hwf.pinsResolve k hpk)⟩

/-- **Nothing is dropped at the register level either** — unconditionally, no
well-formedness needed: a write present on either side is present after the
merge. The replicated state of an MV-register is grow-only, so a concurrent
edit is retained rather than arbitrated (contrast `LWW.join_selects`, which
*selects*, and would lose one side without trace). -/
theorem both_writes_present (d e : WovenDoc) (k : NodeId) {w w' : Write}
    (hw : contents d k w = true) (hw' : contents e k w' = true) :
    contents (d ⊔ e) k w = true ∧ contents (d ⊔ e) k w' = true :=
  ⟨by show (contents d k w || contents e k w) = true; simp [hw],
   by show (contents d k w' || contents e k w') = true; simp [hw']⟩

/-- The merged register at any node is exactly `MVRegister.sAB`, the file's
own two-concurrent-writes state. -/
theorem contents_merged (k : NodeId) : contents (docX ⊔ docY) k = sAB := rfl

/-- **⭑ Both concurrent edits are visible in the merged document.** Not merely
present in the state — *in view*, i.e. neither is causally superseded, so the
register displays a genuine two-branch fork. `MVRegister.conflict_surfaces`,
read on the merged document. Together with `pin_conflict_renderable` this is
the module's answer to "what does a UI show": both pins, and both edits. -/
theorem content_conflict_surfaces :
    InView (contents (docX ⊔ docY) 0) wA ∧ InView (contents (docX ⊔ docY) 0) wB := by
  rw [contents_merged]
  exact conflict_surfaces

/-! ## §6. `no_crash` — what an implementor actually needs

The property a UI needs is not "the invariant held". It is "**the reader I
wrote does not have to handle a case that cannot be displayed**". That is a
totality statement, and it follows from §3 for *every* reader at once.

First the kit that makes the sharpest concrete instance true: a register
bounded by the horizon always has a maximal write, so the content pane of an
existing node is never blank. -/

/-- A strictly dominating clock has a strictly larger coordinate sum — the
measure the search for a maximal write descends on. -/
private theorem clock_lt_sum {c c' : Clock} (h : Clock.lt c c') :
    c.1 + c.2 < c'.1 + c'.2 := by
  have h' : c.1 ≤ c'.1 ∧ c.2 ≤ c'.2 ∧ c ≠ c' := h
  have hne : ¬ (c.1 = c'.1 ∧ c.2 = c'.2) := by
    intro he
    exact h'.2.2 (by cases c; cases c'; simp_all)
  have h1 := h'.1
  have h2 := h'.2.1
  omega

private theorem view_inhabited_fuel {s : MVReg} {H : Clock}
    (hb : ∀ w, s w = true → Clock.le w.2 H) :
    ∀ (fuel : Nat) (w : Write), s w = true →
      H.1 + H.2 ≤ w.2.1 + w.2.2 + fuel → ∃ v, InView s v := by
  intro fuel
  induction fuel with
  | zero =>
    intro w hw hle
    refine ⟨w, hw, ?_⟩
    intro v hv hdom
    have hwb : w.2.1 ≤ H.1 ∧ w.2.2 ≤ H.2 := hb w hw
    have hvb : v.2.1 ≤ H.1 ∧ v.2.2 ≤ H.2 := hb v hv
    have hsum := clock_lt_sum hdom
    have h1 := hwb.1; have h2 := hwb.2
    have h3 := hvb.1; have h4 := hvb.2
    omega
  | succ fuel ih =>
    intro w hw hle
    by_cases hdom : ∃ v, s v = true ∧ Dom w.2 v.2
    · obtain ⟨v, hv, hd⟩ := hdom
      exact ih v hv (by have := clock_lt_sum hd; omega)
    · exact ⟨w, hw, fun v hv hd => hdom ⟨v, hv, hd⟩⟩

/-- **A register bounded by a horizon always shows something.** If every write
in `s` sits under `H` and `s` holds any write at all, then some write is *in
view* — not causally superseded by anything present. Without a bound this is
false in the model: a register whose writes ascend forever is non-empty and
displays nothing, which is the "still meaningful" failure this module exists
to exclude. `WellFormed.writesInHorizon` is exactly the hypothesis that buys
it. -/
theorem view_inhabited {s : MVReg} {H : Clock}
    (hb : ∀ w, s w = true → Clock.le w.2 H) {w₀ : Write} (h₀ : s w₀ = true) :
    ∃ v, InView s v :=
  view_inhabited_fuel hb (H.1 + H.2) w₀ h₀ (by omega)

/-- **The content pane of an existing node is never blank.** On a well-formed
document, every node that exists has a register with at least one write in
view. -/
theorem content_view_inhabited (n root : Nat) {d : WovenDoc}
    (h : WellFormed n root d) {k : NodeId} (hk : nodes d k = true) :
    ∃ v, InView (contents d k) v :=
  let ⟨_, hw⟩ := h.contentPresent k hk
  view_inhabited (fun w' hw' => h.writesInHorizon k w' hw') hw

/-! ### The horizon conjunct is load-bearing, proved rather than asserted

A structural condition nobody can violate is decoration. This register — every
write whose clock's second coordinate is zero, i.e. the whole infinite chain
`(0,0) < (1,0) < (2,0) < …` — is non-empty and has **no** write in view, because
every write it holds is superseded by another it holds. Planted in a document
it produces the exact failure `WellFormed` exists to exclude: an existing node
whose content pane renders **blank**. -/

/-- The unbounded register: every write clocked `(k, 0)`, for every `k`. -/
def unboundedReg : MVReg := fun w => w.2.2 == 0

theorem unbounded_nonempty : unboundedReg (0, (0, 0)) = true := by decide

/-- ⚠ **Non-empty, and it displays nothing.** Every present write is strictly
dominated by another present write (bump the first coordinate), so the
MV-register's view is empty. -/
theorem unbounded_view_empty : ¬ ∃ v, InView unboundedReg v := by
  intro ⟨v, hv, hmax⟩
  have hv0 : v.2.2 = 0 := by simpa [unboundedReg] using hv
  refine hmax (v.1, (v.2.1 + 1, 0)) (by simp [unboundedReg]) ?_
  refine ⟨Nat.le_succ _, ?_, ?_⟩
  · exact hv0 ▸ Nat.le_refl 0
  · intro heq
    have h1 : v.2.1 = v.2.1 + 1 := congrArg Prod.fst heq
    omega

/-- A document identical to `docX` except that every register is
`unboundedReg`. It satisfies every other conjunct of `WellFormed`; only the
horizon condition rejects it. -/
def docBlank : WovenDoc :=
  mkDoc WeaveState.pinA (fun _ => unboundedReg) txtX (1, 0)

/-- **⭑ `writesInHorizon` is load-bearing, not decoration.** `docBlank` has an
existing node, holding writes, whose content pane displays nothing — and it is
rejected by `WellFormed`, at exactly the horizon conjunct (the witness write
`(0, (5, 0))` is present and sits outside the horizon `(1, 0)`; the other five
conjuncts are `docX`'s). Drop that conjunct and the never-blank guarantee of
`content_view_inhabited` goes with it. -/
theorem horizon_conjunct_is_load_bearing :
    nodes docBlank 0 = true
    ∧ (∃ w, contents docBlank 0 w = true)
    ∧ (¬ ∃ v, InView (contents docBlank 0) v)
    ∧ ¬ (∀ k w, contents docBlank k w = true → Clock.le w.2 (horizon docBlank))
    ∧ ¬ WellFormed 5 9 docBlank := by
  refine ⟨by decide, ⟨(0, (0, 0)), unbounded_nonempty⟩, unbounded_view_empty,
    ?_, ?_⟩
  · intro hall
    exact absurd (hall 0 (0, (5, 0)) (by decide)) (by decide)
  · intro h
    exact unbounded_view_empty (content_view_inhabited 5 9 h (k := 0) (by decide))

/-- **⭑ `no_crash`, for implementors.** Let `read` be **any** projection that
is defined (answers `some`) on every well-formed document — a renderer, a
serializer, a query, an export. Then it is defined on the merge of any two
well-formed documents. There is no case to handle for "the sync produced
something I cannot read", for every reader at once, not for a list of them.

The proof is one application of `merge_preserves_wellformed`, and that is the
honest accounting: this corollary contributes **no** new mathematical content.
What it contributes is the statement in the implementor's vocabulary, with the
quantifier where it belongs — over all readers. -/
theorem no_crash {α : Type} (n root : Nat) (read : WovenDoc → Option α)
    (htotal : ∀ d, WellFormed n root d → (read d).isSome = true)
    {d e : WovenDoc} (hd : WellFormed n root d) (he : WellFormed n root e) :
    (read (d ⊔ e)).isSome = true :=
  htotal _ (merge_preserves_wellformed n root d e hd he)

/-- The same fact as a **term**, for readers whose *type* demands
well-formedness: a dependently-typed projection `f` can be applied to the
merge, because the merge supplies its own proof obligation. An implementor who
writes `f` never constructs a well-formedness certificate by hand at a sync
point — the theorem hands one over. -/
def readMerge {α : Type} {n root : Nat}
    (f : (d : WovenDoc) → WellFormed n root d → α)
    {d e : WovenDoc} (hd : WellFormed n root d) (he : WellFormed n root e) : α :=
  f (d ⊔ e) (merge_preserves_wellformed n root d e hd he)

/-- **The concrete readers a loom UI runs, all total on merges.** Every
bookmark resolves; every pin resolves; every existing node's content pane
shows something; every node's text lays out in bounds; and every element
present in a node's text appears in that node's layout. Each conjunct is the
corresponding structural condition (or `Sequence.lean`'s theorem about it)
applied to `merge_preserves_wellformed`'s output.

⚠ Not claimed, and false in general: that the layout shows each element
**once**. That needs `Sequence.UniqueAnchor`, which is not I-confluent and is
therefore deliberately outside `WellFormed` — see the header. A merged
document can duplicate an id in its layout and is still well-formed. -/
theorem merge_renders (n root : Nat) {d e : WovenDoc}
    (hd : WellFormed n root d) (he : WellFormed n root e) :
    (∀ u m, bookmarks (d ⊔ e) u m = true → nodes (d ⊔ e) m = true)
    ∧ (∀ m, pins (d ⊔ e) m = true → nodes (d ⊔ e) m = true)
    ∧ (∀ k, nodes (d ⊔ e) k = true → ∃ v, InView (contents (d ⊔ e) k) v)
    ∧ (∀ k j, j ∈ Sequence.linearize n (text (d ⊔ e) k) → j < n)
    ∧ (∀ k i a, text (d ⊔ e) k (i, a) = true →
        i ∈ Sequence.linearize n (text (d ⊔ e) k)) := by
  have hwf := merge_preserves_wellformed n root d e hd he
  exact ⟨fun u => hwf.bookmarksResolve u, hwf.pinsResolve,
         fun k hk => content_view_inhabited n root hwf hk,
         fun _ _ hj => Sequence.linearize_lt hj,
         fun k _ _ h => Sequence.linearize_mem (hwf.textLinearizes k) h⟩

/-- A reader a naive implementation gets wrong: *"is the pinned node `m`
present?"* It answers `none` — the crash case, "pinned id not found" — exactly
when a pin dangles, which is a state `WellFormed` excludes. -/
def readPinned (m : NodeId) (d : WovenDoc) : Option Bool :=
  if pins d m = true then (if nodes d m = true then some true else none)
  else some false

/-- The reader is total on well-formed documents — its `none` branch is
unreachable, by `pinsResolve` and nothing else. -/
theorem readPinned_total (n root : Nat) (m : NodeId) (d : WovenDoc)
    (h : WellFormed n root d) : (readPinned m d).isSome = true := by
  unfold readPinned
  by_cases hp : pins d m = true
  · simp [hp, h.pinsResolve m hp]
  · simp [hp]

/-- **`no_crash` at a reader whose totality genuinely depends on
well-formedness** — the non-vacuity witness for §6's quantifier. Sync never
produces "pinned id not found", including the sync that produces two pins. -/
theorem readPinned_total_on_merge (n root : Nat) (m : NodeId) {d e : WovenDoc}
    (hd : WellFormed n root d) (he : WellFormed n root e) :
    (readPinned m (d ⊔ e)).isSome = true :=
  no_crash n root (readPinned m) (readPinned_total n root m) hd he

/-- The merged document really does lay out — a concrete instance, computed.
Replica X's element 1 and replica Y's element 2 both survive, newest first
(the RGA rule: descending id order at a shared anchor). -/
example : Sequence.linearize 5 (text (docX ⊔ docY) 0) = [2, 1] := by decide

/-! ## §7. The report

Both classifications as first-class `Verdict` values, so a schema report can
carry them beside `WeaveState.lean`'s rows. The pair is the module's summary:
**the structural predicate is free; the application rule is not.** -/

/-- Structural well-formedness: FREE. -/
def wellFormedVerdict : Verdict (WellFormed 5 9) :=
  .free (wellFormed_iconfluent 5 9)

/-- The application rule: CLASH, carrying the two-replica repro — and both
replicas of that repro are certified well-formed documents
(`docX_wellFormed`, `docY_wellFormed`), which is what makes the clash a
*conflict to render* rather than a corruption. -/
def onePinVerdict : Verdict OnePin :=
  .clash docX docY docX_onePin docY_onePin merged_violates_onePin

/-- Well-formedness needs no coordination, ever. -/
example : wellFormedVerdict.isFree = true := rfl
/-- The pin rule does — the ceiling `WeaveState.lean` keeps on purpose. -/
example : onePinVerdict.isFree = false := rfl

/-- The escalation reading of the pair, recovered: the *application* rule is
what forces a meeting; nothing structural does. -/
example : ¬ IConfluent OnePin := onePin_not_iconfluent

/-- And the headline, restated at the shape a caller uses it in: any two
well-formed replicas sync into a well-formed document. -/
example (a b : WovenDoc) (ha : WellFormed 5 9 a) (hb : WellFormed 5 9 b) :
    WellFormed 5 9 (a ⊔ b) :=
  merge_preserves_wellformed 5 9 a b ha hb

end Uwueave.Wellformed
