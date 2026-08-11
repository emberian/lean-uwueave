/-
# Uwueave.WeaveState — a loom document, whole: the library's demo of itself.

Every other module classifies an ingredient. This one serves the meal: a
multiplayer weave document with the fields a real loom carries — a causal node
set, per-node contents, per-user cursors, per-user bookmarks, pins, a
capability lattice, a shared budget — declared as one ordinary product type,
its `MergeState` inherited entirely from the composition instances (**zero new
merge proofs** — `example : MergeState WeaveDoc := inferInstance` below), and
its realistic invariant set classified end-to-end through the Spec DSL. The
question the library exists to answer — *"can my loom document be a CRDT?"* —
gets its answer on this document, every row backed by a term.

All three of the DSL's answers appear, on the same document:

  * **Free, proved.** Growing the weave, editing node contents, issuing
    attenuated grants, bookmarking, moving your own cursor: none of it ever
    waits for a peer, under any partition schedule.
  * **Clash, with the repro.** "At most one pinned node" — kept in the schema
    DELIBERATELY — is the uniqueness ceiling
    (`Catalog.gset_atMostOne_not_iconfluent`), and its `{0}`/`{1}` witness
    pair transports to two complete legal documents whose sync pins two
    nodes (`weaveDocVerdict`). The clash is shown in situ, not designed away.
  * **The seam.** The shared budget clashes globally yet is free within an
    allocation (`Spec.budgetSegVerdict`, reused verbatim) — and the capstone
    theorem `weaveDoc_segmented` (the one substantial new proof here) widens
    that seam to the WHOLE document: merges that hold (pins, allocation)
    fixed preserve the entire invariant set and the seam itself.
    Operationally: coordinate exactly at two events — pinning, and
    re-dividing the budget. Everything else runs free, always.

## The schema, field by field — what each verdict means at the keyboard

  * `nodes` — the grow-only causal node set. Verdict FREE (`nodesVerdict`):
    a node you have seen can never vanish in a sync. Insertion needs no
    coordination; DAG-ness is structural (`Acyclicity.causal_dag_free`).
    *Moving* a node is deliberately NOT state here — it is an op-log with a
    derived view, priced in `Move.lean` and implemented by the exported
    kernel (`Exec.lean`); a schema that made the parent relation mutable
    state would be refuted by `Acyclicity.acyclicity_not_iconfluent`.
  * `contents` — per-node **multi-value registers**, not LWW, and the choice
    is the point (`contentsVerdict`): an LWW join *selects*, so a concurrent
    edit of the same node would silently lose one side
    (`Catalog.lww_every_invariant_iconfluent`'s virtue is exactly that
    vice). A loom wants the fork visible and navigable — the MV-register
    surfaces both writes (`MVRegister.conflict_surfaces`) and resolution is
    an ordinary write at a dominating clock
    (`MVRegister.resolution_is_a_write`). The replicated state is grow-only
    writes; the conflict view is derived, never replicated. Text *inside* a
    node is the sequence problem — `SeqKernel.lean` / loro — not re-solved
    here.
  * `activation` — per-user keyed LWW flags: *your* view position, *your*
    expanded branches. FREE by keyed independence
    (`Weave.per_user_activation_free`). Per-user is a theorem-shaped design
    decision, not taste: a *shared* replicated active path is refuted
    outright (`Weave.active_path_not_iconfluent` — two users activate
    sibling branches, the merge lights both), and "whose cursor wins" is not
    a question a merge should answer.
  * `bookmarks` — per-user grow-only sets of node ids (chosen over escrowed
    *counts*, which would be `Spec.escrowFree`'s row; id-sets carry the
    interesting invariant). The row is the cross-field one: **every
    bookmark points at an existing node**, for every user — free BECAUSE
    nodes only grow (`Spec.pointsAtExisting_iconfluent`, earned against the
    joint merge, lifted through `keyed_cross_iconfluent`). A bookmark never
    dangles, and no lift could have told you so. Un-bookmarking is OR-Set
    territory (`ORSet.lean`), not modeled on this document.
  * `grants`, `revocations` — the `Authority.lean` substrate. Issuing
    attenuated grants is FREE (`grantsVerdict` = `Authority.wf_iconfluent`):
    delegate on a plane, in a partition; every merge is again a well-formed
    grant DAG, and authority provably only narrows
    (`Authority.scope_le_root`). The revocation set carries **no state
    invariant to classify** — its guarantee is the fail-closed *derived
    view*: a late-arriving revocation only ever shrinks authority
    (`Authority.authority_view_antitone`), and concurrent admin duels
    annihilate rather than resurrect (`Authority.duelling_admins_annihilate`;
    `Era.lean` prices the arbitration that keeps a survivor). Signatures and
    id-collision-freedom are premises, priced in `Authority.lean`'s header.
  * `pins` — "the community pin": at most one pinned node, document-wide.
    The poisoned ceiling, kept deliberately: `pinsVerdict` is
    `Spec.atMostOneClash` verbatim, and `weaveDocVerdict` transports its
    witness pair to whole-document scale. Two offline users each pin; the
    sync shows two pins. The exits are the standard three: make pins
    per-user (keyed — free), make the pin an MV-register (the fork
    surfaces), or coordinate the pin event. The schema keeps the ceiling so
    the demo shows what a clash looks like *in situ*.
  * `quota` — a shared storage budget with the allocation in-state
    (`Segmented.QuotaState`). Globally refuted, free within an allocation:
    `quotaVerdict` is `Spec.budgetSegVerdict` reused verbatim. Spends never
    wait; re-allocation is the field's only coordination point — and the
    document-level seam below inherits exactly that.

## What the schema does not model, honestly

Real concurrent text (loro / Fugue; the house kernel is `SeqKernel.lean`),
node moves (op-log + `Exec.lean` kernel, priced by `Move.view_not_stable`),
delivery and liveness (`Delta.lean`, `Liveness.lean`), authentication and
content-addressing (premises, per `Authority.lean`), and the world is the
usual miniature: two users (`Bool`), `Nat` ids, root scope 9, budget 10.

## New content, flagged

Proving the composed verdicts taught that `Spec.lean`'s lift kit is one rung
short for realistic records, so this file adds three ∀-general one-line
lifts — `fst_iconfluent` (a left-field invariant lifts to the product),
`at_key_iconfluent` (a single-key invariant lifts to the keyed map), and
`keyed_cross_iconfluent` (a joint-merge cross result lifts pointwise over a
keyed right family with a shared left field) — plus the capstone seam theorem
`weaveDoc_segmented`. Everything else is existing catalog verdicts, lifts,
and packaged values, cited by name.
-/
import Uwueave.Spec
import Uwueave.Weave
import Uwueave.Authority
import Uwueave.MVRegister

namespace Uwueave.WeaveState

open Uwueave Uwueave.Catalog Uwueave.Spec Uwueave.Segmented
open Uwueave.Weave Uwueave.Authority Uwueave.MVRegister

universe u v w

/-! ## §1. Three lifts the schema teaches

`Spec.lean`'s worked examples never needed these, because every invariant
there was shaped to sit in `product_iconfluent`'s conjunction or quantify
over every key. A realistic record is lumpier: fields with no invariant at
all (`revocations`), invariants that watch one key of a map (`contents` at
the genesis node), and a cross-field relation against a *keyed* family
(`bookmarks`). Each lift is one line — the confluence content is entirely
the lifted theorem's — but no lemma of these shapes existed, so they are new
content, flagged as such. -/

/-- **The left-field lift.** An invariant watching only the left field of a
product is I-confluent over the product as soon as it is on the field — the
product merge is componentwise, so the field's own confluence is the whole
story. This is how a record row *skips* fields that carry no invariant
(here: `revocations`, and the whole right half in `weaveDocFreeVerdict`). -/
theorem fst_iconfluent {A : Type u} {B : Type v} [MergeState A] [MergeState B]
    {IA : Invariant A} (h : IConfluent IA) :
    IConfluent (S := A × B) (fun p => IA p.1) :=
  fun x y hx hy => h x.1 y.1 hx hy

/-- **The single-key lift.** An invariant watching one key's value is
I-confluent over the keyed map as soon as it is on the value — merge is
pointwise, so key `k₀` merges alone. The `pi_iconfluent` shape quantifies
over *every* key; this is its one-key corner (here: "the genesis node's
content is written", which says nothing about any other node). -/
theorem at_key_iconfluent {K : Type u} {V : Type v} [MergeState V]
    {J : Invariant V} (k₀ : K) (h : IConfluent J) :
    IConfluent (S := K → V) (fun f => J (f k₀)) :=
  fun f g hf hg => h (f k₀) (g k₀) hf hg

/-- **The keyed cross lift.** A cross-field invariant proved against the
joint merge of `A × B` holds pointwise over `A × (U → B)`: one shared left
field, a keyed family on the right, the relation demanded at every key. The
per-key instance *is* the joint-merge fact at `(p.1, p.2 u)` — no new
confluence argument, but note what this is NOT: it does not manufacture a
cross result from per-field verdicts (that candidate is false,
`Catalog.lww_cross_field_not_iconfluent`); it only transports one already
earned. Here: referential integrity of every user's bookmarks against the
one shared node set. -/
theorem keyed_cross_iconfluent {A : Type u} {B : Type v} {U : Type w}
    [MergeState A] [MergeState B] {R : A → B → Prop}
    (h : IConfluent (S := A × B) (fun p => R p.1 p.2)) :
    IConfluent (S := A × (U → B)) (fun p => ∀ u, R p.1 (p.2 u)) :=
  Uwueave.keyed_cross_iconfluent h

/-! ## §2. The document

Ordinary type formers, instances resolved by composition — this is the DSL's
whole stance: a schema is just a Lean type. Layout (all products
right-nested):

```
WeaveDoc = ((nodes, bookmarks), (contents, (activation, (grants, revocations))))
           × (pins, quota)
```

The `(nodes, bookmarks)` adjacency is deliberate: the cross-field row lives
on that sub-pair. `(pins, quota)` sit apart as the document's entire
coordination surface — §5 makes that a theorem. -/

/-- The two-user miniature (`Weave.lean`'s move). Everything per-user in the
schema is a `User → _` map; the construction is uniform in the index type. -/
abbrev User := Bool

/-- Node ids. In a deployment these are content-derived hashes; here, `Nat`,
with id-uniqueness a premise priced in `Authority.lean`'s header. -/
abbrev NodeId := Nat

/-- The free-running core: every field of the document except the two that
coordinate. -/
abbrev WeaveCore :=
  (GSet NodeId × (User → GSet NodeId))
  × ((NodeId → MVReg) × ((User → NodeId → LWW) × (GrantSet × Revoked)))

/-- **The loom document.** The core, plus the poisoned pin ceiling and the
budgeted quota. This *is* the schema — no bespoke AST, no new instances. -/
abbrev WeaveDoc := WeaveCore × (GSet NodeId × QuotaState)

/-- The grow-only causal node set. -/
abbrev nodes (d : WeaveDoc) : GSet NodeId := d.1.1.1
/-- Each user's grow-only set of bookmarked node ids. -/
abbrev bookmarks (d : WeaveDoc) : User → GSet NodeId := d.1.1.2
/-- Per-node contents: a multi-value register per node (grow-only tagged
writes; the conflict view is derived — `MVRegister.InView`). -/
abbrev contents (d : WeaveDoc) : NodeId → MVReg := d.1.2.1
/-- Per-user activation flags: each user's own view position, LWW per node. -/
abbrev activation (d : WeaveDoc) : User → NodeId → LWW := d.1.2.2.1
/-- The delegation DAG (`Authority.lean`). -/
abbrev grants (d : WeaveDoc) : GrantSet := d.1.2.2.2.1
/-- Revoked grant ids, grow-only. No state invariant — its guarantees are
view-level and fail-closed (`Authority.authority_view_antitone`). -/
abbrev revocations (d : WeaveDoc) : Revoked := d.1.2.2.2.2
/-- The pinned-node set — the deliberately-kept ceiling. -/
abbrev pins (d : WeaveDoc) : GSet NodeId := d.2.1
/-- The budgeted storage quota: allocation plus per-user spend. -/
abbrev quota (d : WeaveDoc) : QuotaState := d.2.2

/-- **Zero new merge proofs.** The whole document's `MergeState` — merge,
commutativity, associativity, idempotence — is assembled by the product and
pointwise instances from `Confluence.lean` and the catalog's leaf instances.
Nothing was proved to make this line elaborate; that is the composition
algebra doing its job. -/
example : MergeState WeaveDoc := inferInstance

/-! ## §3. The rows — every field's verdict, named

Each verdict is a *value*: the free ones carry the catalog theorem, the clash
one carries the two-replica repro, the seam one carries both halves. The
composed judgements in §4–§5 are assembled from exactly these ingredients. -/

/-- `nodes`: the genesis node (id 0) is present — every weave hangs off a
root. FREE (`Catalog.gset_mem_iconfluent` via the packaged
`Spec.gsetMemFree`): anything observed survives every merge. What a user
sees: the document never loses its root, and no sync can un-create a node. -/
def nodesVerdict : Verdict (S := GSet NodeId) (fun s => s 0 = true) :=
  gsetMemFree 0

/-- `contents`: the genesis node's register has genuinely been written —
a fresh document is born with its root prompt. FREE: "some write is present"
is upward-closed under inclusion (`Catalog.gset_monotone_iconfluent`),
lifted to the keyed map by `at_key_iconfluent`. What a user sees: the root
content can never blank out at a sync; and when two users edit one node
concurrently, *both* writes survive into the derived view
(`MVRegister.conflict_surfaces`) — the fork is the product, not a casualty. -/
def contentsVerdict :
    Verdict (S := NodeId → MVReg) (fun c => ∃ w, c 0 w = true) :=
  .free (at_key_iconfluent 0 (gset_monotone_iconfluent
    (I := fun c => ∃ w, c w = true)
    (fun _s _t hsub => fun ⟨w, hw⟩ => ⟨w, hsub w hw⟩)))

/-- `activation`: every user's every flag register is genuinely written
(timestamp ≥ 1 — the two-user miniature initializes activation at document
birth, `Spec.loomInv`'s convention). FREE by keyed independence —
`Weave.per_user_activation_free` over `Catalog.lww_every_invariant_iconfluent`.
Per-user is the *theorem-shaped* choice: the shared alternative is refuted
(`Weave.active_path_not_iconfluent`, restated in §6) — a shared active path
merges into a non-path. What a user sees: your cursor is yours; a sync never
teleports your view because someone else navigated. -/
def activationVerdict :
    Verdict (S := User → NodeId → LWW) (fun a => ∀ u k, 1 ≤ (a u k).ts) :=
  .free (per_user_activation_free
    (fun _ => pi_iconfluent fun _ => lww_every_invariant_iconfluent
      (fun r => 1 ≤ r.ts)))

/-- `bookmarks` × `nodes` — **the cross-field row**: every user's every
bookmark points at an existing node. Relational, so no per-field lift could
ever produce it (`Verdict.cross`'s whole point); the evidence is
`Spec.pointsAtExisting_iconfluent` — referential integrity over grow-only
sets is I-confluent because nodes only grow — transported through
`keyed_cross_iconfluent` to the per-user family. What a user sees: a
bookmark never dangles, on any replica, after any merge; nobody validates
anything at sync time and the FK holds anyway. -/
def bookmarksVerdict :
    Verdict.cross (fun (ns : GSet NodeId) (bm : User → GSet NodeId) =>
      ∀ u, PointsAtExisting ns (bm u)) :=
  Verdict.cross_free
    (keyed_cross_iconfluent (R := PointsAtExisting) pointsAtExisting_iconfluent)

/-- `grants`: the delegation DAG is well-formed against root scope 9 (the
`Authority.lean` demo world). FREE (`Authority.wf_iconfluent`): grants can be
issued offline and every merge of well-formed replicas is well-formed — and
on any well-formed state no grant's scope exceeds the root's
(`Authority.scope_le_root`), so nobody manufactures authority by syncing.
What a user sees: sharing access works on a plane; a peer's merge can add
delegations but never widen one. -/
def grantsVerdict : Verdict (S := GrantSet) (WF 9) :=
  .free (wf_iconfluent 9)

/-- `pins`: at most one pinned node, document-wide — **the poisoned ceiling,
kept on purpose.** This is `Spec.atMostOneClash` verbatim: the verdict
carries the `{0}`/`{1}` witness pair whose union pins two nodes. What a user
sees: two offline users each pin a node; the sync shows both pins and the
"one pin" rule is silently false — no library cleverness fixes this
(`Necessity.necessity`); the design must pick per-user pins (free), an
MV-pin (visible fork), or a coordinated pin event. -/
def pinsVerdict :
    Verdict (S := GSet NodeId)
      (fun s => ∀ m n, s m = true → s n = true → m = n) :=
  atMostOneClash

/-- `quota`: the budget-10 invariant on allocation-plus-spend — the **seam
verdict**, `Spec.budgetSegVerdict` reused verbatim. Globally refuted (two
legal re-allocations merge over budget — the carried clash), free within an
allocation (`Segmented.budget_segmented`). What a user sees: spending
storage never waits for anyone; only *re-dividing* crosses the allocation
seam, while `Scheduling` demands determine actual meetings. -/
def quotaVerdict : SegVerdict (BudgetInv 10) (User → Nat) :=
  budgetSegVerdict

/-! ## §4. The composed judgement

The free core first, then the full document. The core's proof term *is* its
classification report: one combinator per schema node, every leaf a named
catalog theorem. -/

/-- The core invariant — the realistic free rows of §3, conjoined in schema
order: genesis present and referential integrity on the `(nodes, bookmarks)`
pair; genesis content written; activation genuinely written per user; the
grant DAG well-formed (the revocation set deliberately carries no conjunct —
`fst_iconfluent` is how the row skips it). -/
def coreInv : Invariant WeaveCore := fun c =>
  (c.1.1 0 = true ∧ ∀ u, PointsAtExisting c.1.1 (c.1.2 u))
  ∧ ((∃ w, c.2.1 0 w = true)
    ∧ ((∀ u k, 1 ≤ (c.2.2.1 u k).ts)
      ∧ WF 9 c.2.2.2.1))

/-- **The core is coordination-free** — assembled from the §3 rows' own
theorems, one combinator per schema node: `product_iconfluent` down the
spine, `and_iconfluent` where two rows watch one sub-pair, the three §1
lifts at the lumpy corners. Read the term against §3: it is `nodesVerdict` ∧
`bookmarksVerdict` ∧ `contentsVerdict` ∧ `activationVerdict` ∧
`grantsVerdict`, as one proof. -/
theorem core_iconfluent : IConfluent coreInv :=
  product_iconfluent
    (and_iconfluent
      (fst_iconfluent (gset_mem_iconfluent 0))
      (keyed_cross_iconfluent (R := PointsAtExisting)
        pointsAtExisting_iconfluent))
    (product_iconfluent
      (at_key_iconfluent 0 (gset_monotone_iconfluent
        (I := fun c => ∃ w, c w = true)
        (fun _s _t hsub => fun ⟨w, hw⟩ => ⟨w, hsub w hw⟩)))
      (product_iconfluent
        (per_user_activation_free
          (fun _ => pi_iconfluent fun _ => lww_every_invariant_iconfluent
            (fun r => 1 ≤ r.ts)))
        (fst_iconfluent (wf_iconfluent 9))))

/-- The core verdict, packaged for the report table. -/
def coreVerdict : Verdict coreInv := .free core_iconfluent

/-- The full document invariant: the free core, plus the two deliberate
coordination features — the pin ceiling and the budget. -/
def weaveDocInv : Invariant WeaveDoc := fun d =>
  coreInv d.1
  ∧ ((∀ m n, pins d m = true → pins d n = true → m = n)
    ∧ BudgetInv 10 (quota d))

/-- Everything *except* the ceiling and the budget, read at whole-document
scale: FREE, by the left-field lift of `core_iconfluent`. This row is the
precise statement of "the document's coordination cost is exactly its two
deliberate features" — remove them from the invariant set and nothing else
ever waits. -/
def weaveDocFreeVerdict : Verdict (S := WeaveDoc) (fun d => coreInv d.1) :=
  .free (fst_iconfluent core_iconfluent)

/-! ### The clash, in situ — concrete witnesses

The transported repro needs concrete legal states to hold fixed. These are
also §5's seam witnesses: the same two documents refute global freedom in
both packagings. -/

/-- One replica's pin: node 0. -/
def pinA : GSet NodeId := fun n => n == 0
/-- The other replica's pin: node 1. -/
def pinB : GSet NodeId := fun n => n == 1

theorem pinA_atMostOne : ∀ m n, pinA m = true → pinA n = true → m = n := by
  intro m n hm hn
  have h1 : m = 0 := by simpa [pinA] using hm
  have h2 : n = 0 := by simpa [pinA] using hn
  rw [h1, h2]

theorem pinB_atMostOne : ∀ m n, pinB m = true → pinB n = true → m = n := by
  intro m n hm hn
  have h1 : m = 1 := by simpa [pinB] using hm
  have h2 : n = 1 := by simpa [pinB] using hn
  rw [h1, h2]

/-- The merged pin set holds both pins — the ceiling's refutation, stated on
the exact merge the transports below produce. -/
theorem pins_clash :
    ¬ ∀ m n, (pinA ⊔ pinB) m = true → (pinA ⊔ pinB) n = true → m = n :=
  fun h => absurd (h 0 1 (by decide) (by decide)) (by decide)

/-- A legal quota: the budget split 5/5, nothing spent. -/
def quota₀ : QuotaState := ((fun _ => 5), (fun _ => 0))

theorem quota₀_legal : BudgetInv 10 quota₀ :=
  ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, rfl⟩

/-- A legal core: node 0 with its genesis write (`MVRegister.wA`), both
users bookmarking it, activation initialized, and `Authority.demoChain` (the
two-link delegation demo) with nothing revoked. -/
def core₀ : WeaveCore :=
  (((fun n => n == 0), (fun _ => fun n => n == 0)),
   ((fun k w => k == 0 && w == wA),
    ((fun _ _ => ⟨1, 0⟩),
     (demoChain, noRevs))))

theorem core₀_legal : coreInv core₀ :=
  ⟨⟨rfl, fun _ _ h => h⟩,
   ⟨wA, by decide⟩,
   fun _ _ => Nat.le_refl 1,
   demoChain_wf⟩

/-- ⚠ **The whole document clashes — the ceiling's repro at full scale.**
`Verdict.prodClashRight` transports the pin pair: two COMPLETE documents,
each legal (same legal core `core₀`, same legal quota `quota₀`, one pin
each), whose merge pins nodes 0 and 1. This is the pair a loom
implementation must pick a policy for, and it is pasteable into a test as
is. Every ingredient is named: the core's legality is `core₀_legal` (backed
by §3's free rows), the quota's is `quota₀_legal`, and the refutation is
`pins_clash` — `pinsVerdict`'s witness content, replanted at document
scale. -/
def weaveDocVerdict : Verdict weaveDocInv :=
  Verdict.prodClashRight (IA := coreInv)
    (IB := fun q : GSet NodeId × QuotaState =>
      (∀ m n, q.1 m = true → q.1 n = true → m = n) ∧ BudgetInv 10 q.2)
    (pinA, quota₀) (pinB, quota₀)
    ⟨pinA_atMostOne, quota₀_legal⟩ ⟨pinB_atMostOne, quota₀_legal⟩
    (fun hmerge => pins_clash hmerge.1)
    core₀ core₀_legal

/-! ## §5. The capstone: the document's whole coordination surface, named

`Segmented.lean`'s design recipe says: when the DSL hands you a clash, look
for a σ. The library's own demo should practice what it preaches. The pin
ceiling and the budget are the document's only non-free rows — so project
out exactly `(pins, allocation)` and ask whether the *entire* invariant set
is segmented over it. It is. -/

/-- The document seam: the pin set and the quota allocation — the two
projections replicas hold fixed between explicit coordination events. -/
def docSeam (d : WeaveDoc) : GSet NodeId × (User → Nat) :=
  (pins d, (quota d).1)

/-- **The whole document is segmented over `docSeam`** — the file's one
substantial new confluence proof, and its punchline. Merges of legal
documents agreeing on (pins, allocation) preserve the FULL invariant set
and the seam itself: the core is free outright (`core_iconfluent`), an
agreed pin set merges idempotently so the ceiling transfers, and the quota
is `Segmented.budget_segmented`'s fiber. Nothing else in the schema can
move the seam — that is the closure half, and it is what makes "coordinate
only to pin or re-allocate" a theorem instead of a slogan. -/
theorem weaveDoc_segmented : SegmentedIConfluent docSeam weaveDocInv := by
  intro x y hσ hx hy
  have hσ' : (pins x, (quota x).1) = (pins y, (quota y).1) := hσ
  injection hσ' with hpins halloc
  have hpmerge : pins x ⊔ pins y = pins x := by rw [hpins, merge_idem]
  have hbud := budget_segmented 10 (quota x) (quota y) halloc hx.2.2 hy.2.2
  refine ⟨⟨core_iconfluent x.1 y.1 hx.1 hy.1, ?_, hbud.1⟩, ?_⟩
  · intro m n hm hn
    have hm' : pins x m = true := by
      have h : (pins x ⊔ pins y) m = true := hm
      rwa [hpmerge] at h
    have hn' : pins x n = true := by
      have h : (pins x ⊔ pins y) n = true := hn
      rwa [hpmerge] at h
    exact hx.2.1 m n hm' hn'
  · show (pins x ⊔ pins y, (quota x ⊔ quota y).1) = (pins x, (quota x).1)
    rw [hpmerge, hbud.2]

/-- **The document's seam verdict** — both halves packaged, `SegVerdict`
exactly as the DSL intends it shipped. The carried clash is
`weaveDocVerdict`'s own pair (the two one-pin documents — global freedom is
refuted, not waved at); the seam is `weaveDoc_segmented`. Reading, at the
keyboard: edits, delegations, bookmarks, cursor moves and spends sync freely
in any order forever; the *only* times this document ever needs its
replicas in a room are a pin change and a budget re-division — and a
same-seam sync can cause neither behind your back (`staysInSeam`, §6). -/
def weaveDocSeamVerdict : SegVerdict weaveDocInv (GSet NodeId × (User → Nat)) where
  σ := docSeam
  seamFree := weaveDoc_segmented
  x := (core₀, (pinA, quota₀))
  y := (core₀, (pinB, quota₀))
  hx := ⟨core₀_legal, pinA_atMostOne, quota₀_legal⟩
  hy := ⟨core₀_legal, pinB_atMostOne, quota₀_legal⟩
  hbad := fun h => pins_clash h.2.1

/-! ## §6. The report — the whole document at a glance

Every row is `rfl` against a term above; the `Bool` is the summary, the term
is the evidence. This table is what the README points at. -/

/-- nodes: free — a seen node never vanishes. -/
example : nodesVerdict.isFree = true := rfl
/-- contents: free — genesis content survives every merge; concurrent edits
fork visibly instead of losing silently. -/
example : contentsVerdict.isFree = true := rfl
/-- activation: free — per-user by theorem, not taste. -/
example : activationVerdict.isFree = true := rfl
/-- bookmarks ⊆ nodes: free — the cross-field row, earned against the joint
merge; no lift produced it and none could have. -/
example : bookmarksVerdict.isFree = true := rfl
/-- grants: free — delegate offline; authority only narrows. -/
example : grantsVerdict.isFree = true := rfl
/-- pins: CLASH — the kept ceiling, with its two-replica repro. -/
example : pinsVerdict.isFree = false := rfl
/-- quota, demoted to the binary answer a `Verdict`-only consumer sees:
clash. The seam is the refined truth (`quotaVerdict`, §3). -/
example : quotaVerdict.toClash.isFree = false := rfl
/-- The free core, composed: everything but the two deliberate features. -/
example : coreVerdict.isFree = true := rfl
/-- The same fact at whole-document scale. -/
example : weaveDocFreeVerdict.isFree = true := rfl
/-- The full document, binary reading: NOT free — and the verdict carries
two complete legal documents whose sync breaks the pin rule. -/
example : weaveDocVerdict.isFree = false := rfl
/-- The seam verdict demotes to the same binary answer — a `SegVerdict`
never overclaims. -/
example : weaveDocSeamVerdict.toClash.isFree = false := rfl

/-- Why activation is per-user, restated from `Weave.lean`: a *shared*
replicated active path is not a CRDT — two users activate sibling branches
and the merged flag-set is no longer a path. -/
example : ¬ IConfluent (S := ActiveSet) IsActivePath :=
  active_path_not_iconfluent

/-- The escalation reading, recovered from the packaged witnesses: the full
invariant set is globally not I-confluent. Coordination is *required* — the
seam theorem says only where. -/
example : ¬ IConfluent weaveDocInv :=
  weaveDocSeamVerdict.escalatesGlobally

/-- The free-running half, usable as-is by an implementation: same-seam
legal documents merge legally — every sync between coordination events is
safe. -/
example (a b : WeaveDoc) (hσ : docSeam a = docSeam b)
    (ha : weaveDocInv a) (hb : weaveDocInv b) : weaveDocInv (a ⊔ b) :=
  weaveDocSeamVerdict.freeWithinSeam hσ ha hb

/-- The closure half: a same-seam sync can neither pin a node nor
re-allocate the budget behind your back — the seam moves only at explicit
coordination events. -/
example (a b : WeaveDoc) (hσ : docSeam a = docSeam b)
    (ha : weaveDocInv a) (hb : weaveDocInv b) : docSeam (a ⊔ b) = docSeam a :=
  weaveDocSeamVerdict.staysInSeam hσ ha hb

end Uwueave.WeaveState
