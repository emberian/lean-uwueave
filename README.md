# lean-uwueave

**For everyone who got three bugs deep into replicating a branching document and
started wondering whether the problems were theirs or the universe's.**

Good news, of a particular flavor: many of them are the universe's — and the
universe wrote down which ones. This repo is that list, machine-checked, with
working code attached. It grew out of a real question asked by a real loom
builder:

> *"isn't the hard part of making a DAG/tree CRDT just enforcing the
> requirements of a DAG/tree?"*

Yes. And the honest answer to *that* has three parts, each of which is a
theorem here rather than a vibe:

1. **The question is never "is my merge a CRDT" — it's "does my *invariant*
   survive my merge."** This test has a name (*invariant confluence*, Bailis
   et al. 2015) and a wonderful property: it is necessary *and* sufficient. If
   your invariant fails it, no library — however clever, including this one —
   can maintain it without coordination. You aren't bad at this; the universe
   said no. What's left is choosing *how* to pay: coordinate, arbitrate
   (someone's edit loses), or repair afterward. Every design in this repo is
   honest about which of those it chose.
2. **"The graph stays acyclic" fails that test for arbitrary edge insertion**
   (two replicas, two innocent edges, one merged cycle — we prove it) —
   **but a stronger, humbler invariant passes it and gives you acyclicity for
   free**: *every edge points to something older*. Content-addressing — ids
   that are hashes of contents-plus-parents, like git — hands you that
   invariant without asking. An append-only, hash-linked weave simply cannot
   have a cycle, needs no cycle check, and merges freely at any scale.
3. **The edits that don't fit that shape — moving a node, merging nodes —
   go through a pattern**: replicate the grow-only *log of operations*, and
   *derive* the structure by deterministic replay. Convergence becomes a
   theorem. So does the price: an older edit arriving late can quietly un-do
   a move you watched happen. We didn't hide that; we proved it, so you can
   design your UI around it instead of discovering it from a bug report.

(The lake library and Rust crate spell it `Uwueave`/`uwueave`; the project is
lean-uwueave, and that was never a typo.)

## If you don't read Lean

You don't have to. Three things here are useful with zero formal-methods
background:

- **The verdict table below.** Each row tells you whether a feature can be
  coordination-free, with the theorem named so you (or a friend, or a model)
  can check the receipt.
- **The counterexamples.** Every "no" comes with a concrete two-replica
  scenario — real states, usually three lines each. They paste straight into
  your test suite, whatever language it's in. A refutation here is a gift:
  it's the exact bug your users would have found for you, delivered early
  and politely.
- **The design advice** in "If you are building a loom," which is just the
  theorems wearing comfortable clothes.

## The map

| File | What it settles |
|---|---|
| `Uwueave/Confluence.lean` | The judgement itself: `MergeState`, `IConfluent`, and `escalation_witness` — a failed invariant *always* yields a runnable two-replica repro. Plus the lifts that let a document's verdict be computed field-by-field. |
| `Uwueave/Catalog.lean` | The classic structures — G-Set, counters, LWW, escrow — with merge laws proved and keystone invariants classified. The pattern worth internalizing: ceilings, uniqueness, and mutual exclusion escalate; grow-only facts and per-replica quotas run free; a lone LWW register can never merge-break anything (`lww_every_invariant_iconfluent`) while two LWW registers can break any invariant *relating* them (`lww_cross_field_not_iconfluent`). |
| `Uwueave/Acyclicity.lean` | The DAG dichotomy of part 2 above: `acyclicity_not_iconfluent`, `grounded_iconfluent`, `grounded_acyclic` — packaged as `causal_dag_free`. |
| `Uwueave/Move.lean` | The op-log pattern's guarantee, once and generically (`derived_view_sec`), and its price on a concrete miniature (`view_not_stable`). |
| `Uwueave/ORSet.lean` | Removable sets, both honest ways: add-wins correctly scoped (`orset_present_survives`), unscoped presence refuted (`orset_present_not_iconfluent`), and the causal-length set free per-element (`clset_present_iconfluent`). |
| `Uwueave/Causality.lean` | Vector clocks: the clock order *is* the merge's order (`vclock_leq_iff`) — and fork evidence is forever (`fork_evidence_iconfluent`): a peer caught equivocating cannot gossip its way back to innocence. |
| `Uwueave/MVRegister.lean` | The multi-value register: keep the fork, show the fork. Concurrent writes both surface (`conflict_surfaces`); resolving is just another write (`resolution_is_a_write`). For a loom this isn't conflict *handling* — forks are the product. |
| `Uwueave/Undo.lean` | Multi-user undo/redo as ordinary writes at fresh clocks — the view restores (`undo_restores`), history is never rewritten (`undo_preserves_history`), and a concurrent undo conflicts *visibly* instead of losing silently. |
| `Uwueave/Delta.lean` | Why shipping deltas instead of states is sound: `joinAll` is exactly the least upper bound, and `same_deltas_same_state` — same delta-set, any order, any duplication, any batching, same replica. Twelve of its sixteen theorems use no axioms at all. |
| `Uwueave/Sequence.lean` | The text layer, with its boundary drawn precisely: membership and anchor-order hold from well-formedness alone; exactly-once needs an id-uniqueness premise *and we prove that premise isn't free*; and the centerpiece is a concrete interleaving-anomaly witness — two runs merging to `[4,3,2,1]`, strictly alternated. No-interleaving is explicitly *not* claimed; that's what real sequence CRDTs (loro, Fugue) are for. |
| `Uwueave/Segmented.lean` | The gentlest verdict: some invariants that fail globally are free *within a seam* (`budget_segmented` vs `budget_not_iconfluent` — same invariant, both verdicts). Spend freely inside your quota; coordinate only to re-divide it. |
| `Uwueave/Spec.lean` | A composition DSL where verdicts carry their evidence: a schema's answer is either a proof or a counterexample transported up from the exact field that caused it. |
| `Uwueave/Weave.lean` | A real weave library's feature list classified feature-by-feature — including the loom-specific theorem that a *shared* replicated active path is not a CRDT (`active_path_not_iconfluent`); make it per-user, which is better UX anyway. |
| `Uwueave/Exec.lean` | The executable kernel: the move-replay decision procedure, authored in Lean, exported to C, and linked into the Rust crate — so the part that must be right lives in one place, next to its model. |
| `Uwueave/Audit.lean` | The trust ledger, enforced: every keystone theorem's axiom footprint is pinned with `#guard_msgs`. A `sorry` or `native_decide` sneaking in anywhere *fails the build*. Eighteen keystones use no axioms at all. |

## The Rust crate (`rust/`)

`uwueave` wraps the **Lean-compiled kernel** rather than re-implementing it:
`build.rs` runs `lake build`, compiles the emitted C plus a three-function
shim, and links the Lean runtime — so building it requires a Lean toolchain
([elan](https://elan.lean-lang.org)), on purpose. The semantics have one home.

- `causal::CausalWeave<T>` — the append-only content-addressed DAG. Grounded
  by construction, so `merge` is a plain union with **no cycle check** — the
  theorems above are why that's not recklessness. A same-id-different-bytes
  encounter is refused loudly as corruption, never silently deduplicated.
- `movelog::MoveLog` — moves as a grow-only op set whose replay decision is
  `Exec.lean`'s kernel, called through FFI. There is no Rust replay
  implementation to drift out of sync, because there is no Rust replay
  implementation.
- `tests/properties.rs` — randomized law-checking (merge laws, groundedness,
  replay determinism, view acyclicity) through the real kernel; the suite has
  been mutation-tested, so its greens are known to be capable of turning red.

**What we claim, plainly:** the Lean theorems verify the *design*; the replay
semantics are Lean-authored and compiled in. Still unverified, and said so:
the storage/index/codec glue, the C shim, Lean's own C backend, and the
refinement connecting the executable kernel to the abstract model (named open
work in `Exec.lean`). Tests — even lovely ones — are evidence, not proof, and
we label them accordingly.

## If you are building a loom

- **A single-device or embedded weave** — with content-derived ids and
  parents fixed at creation, the store needs no coordination machinery on any
  hardware. Keep node moving log-derived, not stored-parent mutation.
- **A multiplayer weave** — the merge you need is the union in
  `CausalWeave::merge` + `MoveLog::merge`. The part that feels missing from
  every CRDT library is the part that provably *cannot* be a library feature;
  what a library can do is price your choices, which is what this one does.
  Keep the active path per-user. Let concurrent edits surface as visible
  forks — a loom is the one interface where forks are the product. Hold
  equivocating peers accountable with evidence that never expires.
- **UI over replicated state** — design around `view_not_stable`: derived
  views can shrink when older ops sync in. Treat replay output as watchable
  state; consider showing users a skipped op instead of silently dropping it.
- **Text** — nothing here competes with loro's sequence CRDTs; this is the
  structural layer around them, and `Sequence.lean` documents exactly where
  the hard text problems begin.

## How to read our claims

We try to be kind by being precise. "FREE" means *the merge preserves the
invariant, proved, coordination never required for it* — it does not mean an
operation can't violate it locally (validate your ops), and it does not price
metadata growth. Refutations are concrete states, not intuitions. Where a
guarantee needs a cryptographic premise (hashes don't collide, signatures
don't forge), the premise is stated as a premise, never absorbed into a
theorem. And where our miniatures stop short of the real problem — sequences,
nested maps, epochs — the module says so at the top, because an honest
boundary is more useful to you than an impressive blur.

## Building

```sh
lake build              # every proof + the audit gate; Lean core only, no mathlib, ~30s cold
cd rust && cargo test   # compiles the Lean kernel to C and links it (needs elan)
```

## Papers, and thanks

The annotated bibliography — what each paper establishes, what we took from
it by theorem name, and what we deliberately declined — lives in
[`docs/BIBLIOGRAPHY.md`](docs/BIBLIOGRAPHY.md). The short list: Bailis et al.
(the judgement), Shapiro et al. (CRDTs), Gomes–Kleppmann et al. (SEC in
Isabelle), Kleppmann et al. (the move op, interleaving anomalies, BFT CRDTs,
undo/redo), Almeida–Shoker–Baquero (deltas), Almeida–Shapiro (the blocklace),
Whittaker–Hellerstein (segmented confluence), Sanjuán et al. (Merkle-CRDTs).

Thanks to the weaver whose question shaped the whole thing, and to
[universal-weave](https://github.com/transkatgirl/universal-weave) for being
the kind of library worth building companions for. Made by ember + Claude,
with the [dregg](https://dreggnet.com) metatheory humming in the background.

License: Unlicense OR MIT — same spirit as universal-weave.
