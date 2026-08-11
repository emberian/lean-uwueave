# GROKREVIEW — toward excellence

*Second pass. Post-convergence tree (`feb0b87` and after). The first review
asked "is this honest / is the build sound?" Most of that is settled or
queued. This one asks a different question:*

> **If this library is trying to become the best thing of its kind — a
> pocket Bailis oracle with a Lean-authored kernel, written so loom authors
> can *use* the theorems — what would excellence look like, where is it
> already excellent, and what is the shortest path from here to there?**

Read against the live tree: 19 modules under `Uwueave/`, ~5.9k Lean lines,
~226 theorems, 113 audit pins (~31 axiom-free), Rust kernel FFI +
`uwueave-check`, `docs/MAP.md` + bibliography. Mid-swarm sequencing issues
from the first pass are *not* re-litigated except where they still teach
something about excellence.

---

## 0. What "excellent" means here

This is not mathlib and not a production CRDT crate. Excellence is relative
to a **specific product**:

| Dimension | Excellent means |
|---|---|
| **Judgement fidelity** | Every important design choice a loom faces has a named theorem (free, clash, or seam), with pasteable evidence |
| **Composition** | Schema authors assemble verdicts without re-proving; failures name the field |
| **Honesty under load** | Headers, MAP, Audit, and theorem strength stay aligned as the tree grows |
| **Kernel integrity** | The thing Rust calls is Lean-authored *and* connected by proof to the abstract model it cites |
| **Legibility** | A non-Lean reader gets usable advice; a Lean reader can check the receipt in one hop |
| **Generality ladder** | Each miniature either generalizes cleanly or is labeled as a finite story, never both |

Sin-hunting checks the third row. Excellence lives in all six.

---

## 1. What is already world-class

Say this first, without hedge. Several parts of this repo are better than
almost anything in the CRDT formalization literature at *their chosen scale*.

### 1.1 The genre invention

The product is not "more Isabelle CRDT proofs." It is:

> **Classify the invariant. Ship the clash. Price the exits.**

Bailis is usually a paper you cite. Here it is a *working judgement* with
combinators, a catalog, a CLI (`uwueave-check`), and a map. That genre is
rare. Gomes–Kleppmann verify algorithms. Bailis classifies workloads. This
repo classifies *application promises* with machine-checked miniatures and
puts the answer in front of people who will never open Lean. That is the
right problem for a loom ecosystem.

### 1.2 Refutation-as-gift is a complete aesthetic

The best theorems here are the negative ones with concrete states:

- `acyclicity_not_iconfluent` — `{0→1}` ∪ `{1→0}`
- `pncounter_nonneg_not_iconfluent` — the $100 / $80+$80 story
- `lww_cross_field_not_iconfluent` — interleaving neither replica held
- `active_path_not_iconfluent` — two branches both "active"
- `ormap_policy_divergence` — same merge, opposite values under two views
- `interleaving_anomaly` — `[3,1]` and `[4,2]` → `[4,3,2,1]`
- `view_not_stable` — the op-log price made visible
- `authority_view_antitone` / `duelling_admins_annihilate` — fail-closed dual
- `ormap_doomed_update` — concurrent update ∥ remove, write survives state, dies in view

These are not "we couldn't prove P." They are **deliverables**: paste into a
test suite, design the UI around them, stop blaming the merge function.
Excellence is that the library treats impossibilities as first-class
products equal to the free theorems.

### 1.3 Composition algebra that actually pays rent

`MergeState` on `×` and `→`, `product_iconfluent` / `pi_iconfluent` /
`and_iconfluent`, Spec transport (`prodClash*`, `keyedClash`), and the
repeated pattern "zero new merge proofs" (OR-Set, OR-Map, escrow, keyed
LWW) is the right shallow embedding. `ORMap.present_iff_orset` / `proj_merge`
as `rfl` and presence refutation *derived* from the set is composition done
with taste, not copy-paste.

`selection_iconfluent` is a small masterpiece: one observation (join picks an
argument) unlocks every single-register invariant and explains why
cross-field relational invariants die. That abstraction is textbook-quality.

### 1.4 Delta.lean as pure lattice craft

`joinAll` + order/dup/batch/packet laws + `same_deltas_same_state` + least
G-Set delta. Large axiom-free core. Automata §1 correctly *instantiates*
rather than re-proves. This is the template every other "pattern" module
should aspire to: prove once at the right altitude, harvest forever.

### 1.5 Sequence.lean as a real development

Not a sketch. Fuel completeness (`below_mem`), exactly-once under
`UniqueAnchor`, anchor-precedes as `Sublist`, uniqueness ceiling not free,
interleaving anomaly *computed*. The intellectual move that the anomaly
coexists with every structural theorem ("intention failed; machinery held")
is the kind of clarity most formal CRDT work never reaches.

### 1.6 Claim discipline as infrastructure

Honest-scope blocks, premise-not-theorem (hashes, signatures), "cited not
re-proved," bibliography "where we differ," Audit `#guard_msgs` gate, MAP
grep-enforced axiom-free counts. After the convergence commit, this is a
*system* for not lying under growth — rarer than correct proofs.

### 1.7 Exec architecture (the shape is right)

Lean-authored `absReplay`, decode → decide → encode by definition,
`@[export]`, Rust as storage/FFI, `absReplay_acyclic` for arbitrary ops under
`GroundedBase`, fuel adequacy via pigeonhole, output codec round-trip. The
*substrate choice* (decision layer pure, bytes thin) is excellence-ready.
What remains is closing the abstract connection (see §4).

### 1.8 Duality of unstable views

`view_not_stable` (document anomaly) and `authority_view_antitone` (security
feature) are the same lattice shape with opposite valence. Naming that
duality is design wisdom. Few libraries would notice; this one proved both
sides.

### 1.9 Prose that is the product

For an audience that will not elaborate terms, docblocks and README *are*
the interface. The shopping-list / bank-balance README opening, the Weave
feature table, the priced exits on every clash — that is product work
disguised as comments. Keep defending it (clapback §5 was right).

---

## 2. The excellence gaps (not sins — missing altitude)

These are not "you did something wrong." They are "the library is good
enough that these are now the bottlenecks to greatness."

### 2.1 The generality ladder is uneven and unlabeled

The tree mixes three levels of theorem without a machine-visible taxonomy:

| Level | Examples | Character |
|---|---|---|
| **∀-general** | `derived_view_sec`, `joinAll_*`, `product_iconfluent`, `absReplay_acyclic`, `wf_iconfluent`, `gset_monotone_iconfluent` | Quantifies over types / all logs / all ops |
| **Parametric family** | `escrow_local_bound_iconfluent q`, `grounded_iconfluent rank`, `budget_segmented B` | Parameterized but structure-fixed |
| **Finite story** | Undo acts 1–4, `conflict_surfaces` on `wA`/`wB`, `miniInterp` 2-op table, most Automata/Authority demos | Specific constants, often `decide` |

All three are legitimate. Excellence needs:

1. A **declared level** on every keystone (doc attribute, MAP column, or
   naming convention: `…_story` vs bare name).
2. A policy: finite stories either **generalize within one wave** or get an
   explicit "this is the whole theorem" badge (Undo already does this well).
3. Pressure against the middle failure: a finite story cited as if it were
   ∀-general (Move miniature → "the Kleppmann rule" → Exec kernel, without a
   refinement link).

**Excellence move:** one table in MAP: `generality | theorem | discharges`.

### 2.2 Spec cannot express the invariants that kill documents

The DSL is excellent for *independent field conjunctions* and clash
transport. Real document death is **cross-field**:

- `parent ∈ nodes`
- `active path is a path`
- `summary.length = source.text.length`
- `fieldA.val ≤ fieldB.val` (already refuted for LWW pairs — but not
  expressible as a Spec combinator that *classifies* an arbitrary `R`)

Today those leave the DSL and become hand theorems (Weave) or silence.
`andFree`'s `Option` is correct (clapback accepted); the missing piece is a
first-class hole:

```text
cross (R : A → B → Prop) :  -- no free ride from product_iconfluent
  Verdict (fun p => R p.1 p.2)
```

that can only be filled by a free proof or a clash, never by `prodFree`.

**Excellence move:** Spec v2 is the cross-field story + one worked loom
schema that includes a foreign-key-shaped invariant and transports its clash.

### 2.3 One pattern, four copy-pasted uniqueness ceilings

The same mathematical fact appears as:

- `gset_atMostOne_not_iconfluent`
- `wf_unique_anchor_not_iconfluent` (Sequence)
- `wf_unique_not_iconfluent` (Authority)
- `determinism_not_iconfluent` (Automata)
- (spiritually) sole-admin, mutex/or-break

Excellence is a single lemma:

> uniqueness / mutual exclusion / "at most one tag per id" on a grow-only
> set of structured elements is not I-confluent, with a generic witness
> constructor

and four one-line instances. That is not DRY for its own sake — it teaches
the reader that these are *the same trap* in different clothes, which is
exactly the pedagogy the catalog claims.

### 2.4 Reachability is the missing axis on every clash

State-based I-confluence admits lattice points that causal op delivery never
jointly reaches (`orset_present_not_iconfluent` honesty note). Operationally
live clashes (`ormap_doomed_update`, classic acyclicity, LWW cross-field)
are stronger gifts.

**Excellence move:** every `¬ IConfluent` keystone carries a tag:

- `Live` — exists concurrent op traces from a common ancestor
- `LatticeOnly` — may require acausal state pairs
- `Unknown` — not yet classified

Even informal tags in MAP would raise the library's advisory quality a full
notch. Formal reachability predicates can follow.

### 2.5 The kernel is half-refined

What you have (excellent):

- acyclicity for all op arrays under grounded base
- fuel decides Hits
- output codec identity
- replay = encode ∘ absReplay ∘ decode definitionally

What excellence still wants (Exec header already names these — good):

| Open | Why it matters |
|---|---|
| **absReplay ⟷ abstract derived view** | Until this, SEC for the *shipping* kernel is informal inheritance from `derived_view_sec`, not a theorem about `uwueave_replay_kernel` |
| **miniInterp bridge** | Even a 2-node encoding lemma would nail "same rule, two presentations" |
| **Input codec** | Rust encoder is TCB; a Lean encoder + round-trip or a property-tested agreement harness labeled as evidence-not-proof |
| **Skipped-op observability** | `view_not_stable` is abstract; the kernel should expose "which ops applied" so UIs can show the price (Exec currently only returns overrides) |

The architecture is ready. The open list is a refinement agenda, not a rewrite.

### 2.6 Segmented confluence is a one-hit wonder

`budget_segmented` is the perfect punchline. Excellence would have **three
seams** so the pattern is a tool, not a museum piece:

1. Budget / escrow (done)
2. **ERA-style epochs** as σ for duelling admins (Authority wants this)
3. **Schema version** or **collection boundary** for document migration

SegVerdict in Spec is waiting for more inhabitants.

### 2.7 Causality kit is fragmented

`VClock` / `Concurrent` (Causality), `Dom` (MVRegister), Lamport fields on
moves (Exec), undo clocks — same conceptual object, three encodings.
Excellence: one small `Clock` module (2-replica concrete + abstract `ι → Nat`)
that MV, Undo, Causality, and Exec order all cite. Reduces proof noise and
makes "concurrent" mean one thing.

### 2.8 No path from schema → Lean → runtime check

`uwueave-check` is a brilliant non-expert surface. Excellence ladder:

```
schema text  →  Verdict terms in Spec  →  optional runtime asserts in Rust
                     ↑
              (today: parallel catalog in the CLI,
               not generated from Lean)
```

If the CLI re-implements the catalog in Rust strings, it can drift. If it is
a thin printer over exported Lean facts (or a generated table from Audit/MAP),
it stays true. **The check binary should be unable to disagree with Audit.**

### 2.9 The weave is classified, not formalized

Weave.lean is a correct product artifact (essay + `active_path` + per-user
lift). Excellence for a *loom* companion would eventually include:

- a minimal `WeaveState` (nodes GSet × parent overrides from Exec × per-user
  activation map × bookmarks)
- one `loomDocVerdict` that is the real schema, not the toy in Spec
- Authority predicates over who may append / move
- the active-path clash as a field in that schema, not a free-floating mini

That is wave-shaped work, not a nit.

---

## 3. Module-by-module: excellence notes

Not sin scores. For each module: **strength**, **altitude**, **next excellence step**.

### Confluence
- **Strength:** The judgement, the order, the lifts. ~60 lines of load-bearing math.
- **Altitude:** ∀-general, correct.
- **Next:** Kill residual `or_lift_is_not_available : True` if still present; optional `cross_field_no_lift` *documentation theorem* that is just a pointer. Consider exporting a `Clash` structure used by Spec and Catalog uniformly.

### Catalog
- **Strength:** Best onboarding module ever written for I-confluence.
- **Altitude:** Mix of general (GSet mono, selection) and Bool-hardcoded (PN net, escrow global).
- **Next:** Named 2P-Set; PN/escrow statements over `List ι` or finite supports; make `selection_iconfluent` the explicit parent of LWW *and* CL-Set in MAP. This file should stay short — resist dumping new CRDTs here; spawn modules.

### Acyclicity
- **Strength:** The philosophical center. Dichotomy is perfect.
- **Altitude:** Rank is an oracle — correctly labeled crypto premise.
- **Next:** A one-page "discharge kit": `InjectiveHash` hypothesis + lemma that content-addressed parent edges are grounded. Still not proving blake3; just showing the shape of discharge so systems people see the handoff.

### Move
- **Strength:** Pattern statement (`derived_view_sec`) + price (`view_not_stable`).
- **Altitude:** Pattern ∀-general; interpreter is a 2-op table.
- **Next:** Define miniInterp as "sort + fold apply-if-acyclic" on a 2-node universe *sharing* types with Exec's `Op`, then prove equality to the table. Closes the metaphor without full kernel refinement.

### ORSet
- **Strength:** Scoped vs unscoped is the correct cut; CL-Set counterweight.
- **Altitude:** General for scoped; clash stories concrete.
- **Next:** Tag presence clash `LatticeOnly`; lead docs with doomed-update-style live anomalies when talking to implementers. Remove-wins dual as a short section.

### Causality
- **Strength:** `vclock_leq_iff` bridge; fork evidence monotone.
- **Altitude:** Small and right.
- **Next:** Become the shared clock kit (§2.7). Expand fork evidence only if blocklace/BFT is a real product goal — otherwise keep vocabulary humble.

### MVRegister
- **Strength:** Right product stance for a loom (keep the fork).
- **Altitude:** Finite stories.
- **Next:** General `conflict_surfaces`: concurrent maximals both in view after merge. Lemma relating `InView (s ⊔ t)` to views of `s` and `t` (even a careful negative: "not the union of views").

### Undo
- **Strength:** Best narrative formalization in the tree; honest scope is a template.
- **Altitude:** Finite story, proudly.
- **Next:** One general lemma: dominating-clock rewrite of a prior value restores it into the antichain. Stacks stay out of scope forever if you want — but the semantic core can be ∀-general in one theorem.

### Delta
- **Strength:** Already excellent. Protect it.
- **Altitude:** ∀-general lattice laws.
- **Next:** Almost nothing. Maybe multiset formulation remark. Do not bolt anti-entropy protocols into this file.

### Sequence
- **Strength:** Deepest pure development; anomaly centerpiece.
- **Altitude:** WF general; uniqueness external; linearize total.
- **Next:** Deletion/tombstone miniature *or* a named theorem that naive delete breaks something specific. Pointer to Fugue/loro as "the free theorem you don't have." Factor UniqueAnchor into generic ceiling.

### Segmented
- **Strength:** Conservativity + one perfect pair.
- **Altitude:** General def; one instance.
- **Next:** Second and third seams (§2.6). This module's excellence is measured by number of *interesting* σ, not lines of proof.

### Spec
- **Strength:** Verdict carries evidence; transport is the feature.
- **Altitude:** Combinators general; examples toy.
- **Next:** Cross-field hole (§2.2); richer loom schema; optional `SegVerdict` report printer for `uwueave-check`. Make Spec the *only* way the CLI learns new catalog entries.

### Weave
- **Strength:** Product map from universal-weave features → theorems.
- **Altitude:** Essay + one clash + one lift.
- **Next:** Stay an essay *or* grow into minimal WeaveState (§2.9). Do not half-grow. Current form is valid excellence for "classification surface."

### Exec + ExecRefine
- **Strength:** Real kernel proofs; architecture correct; claim surface now precise.
- **Altitude:** Acyclicity/fuel/codec general for the executable model.
- **Next:** Refinement agenda in §2.5. Also: consider returning applied/skipped bitset for UX of `view_not_stable`. Document grounded-base obligation at the Rust boundary (assert or type-state).

### Audit
- **Strength:** The gate is the trust story.
- **Altitude:** Process excellence.
- **Next:** Generate MAP axiom-free count from Audit automatically in CI; pin only keystones (policy already improved); fail CI if a public theorem in MAP lacks a pin.

### ORMap
- **Strength:** Systems-CRDT excellence; policy divergence is a jewel.
- **Altitude:** One level; live doomed update.
- **Next:** Nest one level *or* prove a negative about recursive merge needing new algebra. Clear/reset clash. This module deserves README-level billing next to Sequence.

### Automata
- **Strength:** Delta harvest + commuting-batch bridge (`exec_perm` family is under-celebrated).
- **Altitude:** §1–2 general; §3–4 mostly catalog cosplay.
- **Next:** Either deepen §2 toward real independence relations (even a 3-letter alphabet with one dependent pair) *or* fold §3–4 into teaching notes and keep Automata as "Delta for machines + commuting actions." Excellence is focus.

### Authority
- **Strength:** Most interesting new composition; fail-closed dual; duelling admins.
- **Altitude:** WF general; uniqueness external; scopes are `Nat`.
- **Next:** (1) epoch seam for survivor policies; (2) connect grants to weave ops ("may move node n"); (3) poset scopes if biscuits are a real target, else permanently rebrand as totally-ordered attenuation. Don't let vocabulary outrun the order.

---

## 4. Cross-cutting excellence agenda (ranked by leverage)

A suggested order that compounds:

### P0 — Multipliers (each unlocks many theorems' value)

1. **Generality labels in MAP** for every keystone (story / parametric / ∀).
2. **Reachability tags** on every clash (`Live` / `LatticeOnly` / `Unknown`).
3. **Generic uniqueness-ceiling lemma** + rehome four instances.
4. **Spec cross-field hole** + one foreign-key-shaped worked example.
5. **Shared Clock kit** (Causality becomes the home).

### P1 — Kernel integrity

6. **miniInterp ↔ absReplay bridge** on a fixed 2-node encoding (small, high symbol value).
7. **Skipped-op vector** in kernel output (makes `view_not_stable` operational).
8. **Groundedness assert** at Rust→Lean boundary.
9. Input-codec strategy (Lean encoder *or* labeled property tests as evidence).

### P2 — Product closure

10. **`uwueave-check` driven by Spec/Audit**, not a parallel Rust catalog.
11. **Second + third seams** (epochs, schema version).
12. **ORMap + Authority** elevated in README narrative (they earn it).
13. Sequence deletion negative or tombstone miniature.

### P3 — Loom-shaped composition

14. Minimal `WeaveState` schema classified end-to-end through Spec.
15. Authority predicates on move/append ops.
16. Optional: nested ORMap or clear statement that nest needs inductive merge.

---

## 5. What not to do (excellence-preserving constraints)

- **Do not add mathlib** unless a proof is blocked on Finset sums — the no-mathlib stance is part of the product.
- **Do not re-implement AIR/constraints in Rust** (project house rule; kernel discipline already points the right way).
- **Do not grow Catalog into a junk drawer** — new domains get modules.
- **Do not formalize Zielonka / full biscuits / full OpSets** just to chase paper titles. Formalize the *judgement-shaped fragment* that changes a loom author's decision.
- **Do not replace prose with terseness** for the non-expert surface. Tighten Automata pads; keep Undo/Sequence/README voice.
- **Do not claim Bailis necessity inside Lean** — keep the post-convergence discipline (and finish grepping Authority-style leftovers).

---

## 6. Proof-quality observations (aspirational craft)

Where proofs are already craft-grade:

- Delta induction on `List.Perm` / membership
- Sequence fuel + sibling disjointness
- ExecRefine pigeonhole depth bound + preservation under `set!`
- LWW assoc by trichotomy (ugly but honest)

Where craft could rise:

| Pattern | Today | Excellent |
|---|---|---|
| Clash proofs | Often `decide` on concrete Nats | Fine for stories; for generic ceilings, constructive witnesses without `decide` where cheap |
| "Same as Catalog" modules | Thin wrappers (Automata tokens) | Prefer `abbrev` + `export` + one sentence over parallel theorem names unless the new name teaches |
| Derived views | Each module rolls its own | Shared `DerivedView` section: SEC hypothesis, stability/antitone lemmas as typeclasses or structures |
| Uniqueness | Repeated | One lemma (§2.3) |
| Encoded graphs | `α → Bool` everywhere | Consider finite-support sets when cardinality/GC stories appear — not before |

Axiom hygiene is already good. Excellence next is **lemma factoring** and **shared vocab**, not smaller axiom footprints.

---

## 7. Comparison class (how to know if you're winning)

You are adjacent to, but not competing with:

| Work | They optimize | You optimize |
|---|---|---|
| Gomes–Kleppmann Isabelle CRDTs | Full algorithm SEC over network model | Invariant classification + pasteable clashes |
| Bailis / Whittaker | Decision procedures, systems | Pocket oracle + Lean kernel |
| Automerge / Loro / Yjs | Shipping correctness empirically | Which promises *can* ship coordination-free |
| OpSets paper | Spec framework for datatypes | Judgement + derived-view pattern + prices |

**Winning** looks like: a loom author pastes a schema into `uwueave-check`, gets FREE / ESCALATES / SEAM with theorem names, clicks through to a clash they can put in CI, and when they need moves, the kernel they call is the one the acyclicity theorem is about — with a refinement story they can point a skeptical cryptographer at.

You are closer to that than almost anyone. The distance is mostly **composition expressiveness**, **generality labeling**, **kernel bridge**, and **CLI↔Lean single source of truth** — not more CRDT variants.

---

## 8. Strengths to protect while growing

1. **Refutation quality** — never ship `¬ IConfluent` without states.
2. **Honest scope blocks** — first 30 lines of every module.
3. **No mathlib / readable cold build.**
4. **Audit gate** as CI religion.
5. **Prose for non-elaborators.**
6. **Lean-authored kernel boundary** (Rust stays dumb).
7. **Bibliography "where we differ."**
8. **Duality thinking** (unstable views, selection vs relational, free vs seam).

If a wave forces a choice between a new CRDT and protecting these, protect these.

---

## 9. Residual hygiene (brief — not the point of this review)

Still true post-clapback if unfixed in your tree:

- `or_lift_is_not_available : True := trivial` may still sit in Confluence — delete it.
- "Bailis necessity" wording may remain in Authority — align with cited-not-proved.
- `feb0b87` message claimed the True theorem deleted; tree may disagree — process lesson: verify deletions.

These are five-minute fixes. They are not the excellence path; they are the floor.

---

## 10. A picture of "done enough to be excellent"

Not finished — excellent:

1. MAP lists every keystone with **generality + reachability + audit pin**.
2. Spec classifies a **real loom schema** including one cross-field clash and one seam.
3. Uniqueness ceiling is **one lemma**.
4. Clocks are **one kit**.
5. `uwueave-check` **cannot disagree with Lean**.
6. Exec has **acyclicity (done) + miniInterp bridge + skipped-op observability**.
7. Authority has an **epoch seam** or permanently embraces fail-closed annihilation as the only policy.
8. ORMap policy divergence and Sequence interleaving are **front-page** results, not deep-tree treasures.
9. Wave discipline: orphans never look shipped; headers never name unproved theorems.

At that point the library is not "a cool formalization." It is a **standard instrument** for local-first design — the thing you hand someone instead of a Slack essay when they ask whether their pin set can be a CRDT.

---

## 11. Closing

The first review measured the floor. The floor is mostly solid (and the clapback correctly reclassified mid-swarm dust as sequencing).

This review measures the ceiling.

You already invented the genre, proved the right impossibilities, composed the lattice cleanly, wrote a kernel in the right place, and taught unstable views as both UX cost and security feature. Excellence from here is **not more domains** — it is **sharper axes** (generality, reachability, cross-field), **tighter identity** (one uniqueness lemma, one clock kit, one CLI truth), and **one refinement nail** so the shipping decision procedure and the abstract model are the same object in Lean's eyes.

Come back after that and the review will be boring in the best way: little left but taste.

— grok, second pass, excellence-facing ( ｡•̀ᴗ-)✧
