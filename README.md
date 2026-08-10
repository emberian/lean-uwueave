# lean-uwueave

**Machine-checked answers to "isn't the hard part of a DAG/tree CRDT just
enforcing the requirements of a DAG/tree?" — plus the Rust that follows them.**

(The lake library and Rust crate keep the identifier spelling `Leanuweave`/`leanuweave`;
the project's name is lean-uwueave, and that was never a typo.)

Built as a companion to [universal-weave](https://github.com/transkatgirl/universal-weave):
a small Lean 4 development that classifies weave/loom invariants by whether they
can be replicated with **zero coordination**, refutes the ones that can't with
concrete two-replica counterexamples, and a Rust crate implementing the fragment
the theorems bless. No mathlib — `lake build` finishes in seconds on a laptop.

## The three-sentence version

1. **The question is never "is my merge a CRDT", it is "does my *invariant*
   survive my merge."** Bailis et al. proved this test (*invariant confluence*)
   is necessary *and* sufficient: if an invariant fails it, **no library,
   however clever, can maintain it coordination-free** — you are choosing among
   escalation (coordinate), arbitration (someone loses), and compensation
   (repair after).
2. **Acyclicity fails the test for arbitrary edge insertion** (`a→b` ∪ `b→a`:
   two legal DAGs, one merged cycle) **but a stronger, edge-local invariant
   passes it and implies acyclicity** — "every edge descends in rank", which
   content-addressing gives you for free because a hash-linked node's parents
   must exist before the child can be named. Append-only weaves get DAG-ness at
   any replication scale with no cycle check at all.
3. **The edits that leave that island — move, split, merge-nodes — go through
   the op-log pattern**: replicate the grow-only set of operations, *derive*
   the structure by deterministic cycle-skipping replay. Convergence and
   DAG-ness are then theorems; the honest price (also a theorem) is that an
   older remote op can retroactively un-apply a move you watched happen.

## The theorems, by file

| File | What it proves |
|---|---|
| `Leanuweave/Confluence.lean` | The judgement: `MergeState` (join-semilattice), `IConfluent`, the constructive `escalation_witness` (a failed invariant always yields a runnable two-replica repro), and the product/pointwise lifts that make field-by-field classification sound. |
| `Leanuweave/Catalog.lean` | G-Set, G-Counter, PN-Counter, LWW, escrow — merge laws proved, keystone invariants classified. Highlights: uniqueness/ceilings escalate (`gset_atMostOne_not_iconfluent`), mutual exclusion escalates (`or_breaks_iconfluence`), balances escalate (`pncounter_nonneg_not_iconfluent`) but **escrow rephrases them free** (`escrow_local_bound_iconfluent`); a single LWW register can never merge-break any invariant (`lww_every_invariant_iconfluent`) yet two of them break relational ones (`lww_cross_field_not_iconfluent`). |
| `Leanuweave/Acyclicity.lean` | **The DAG dichotomy** (sentences 2 above): `acyclicity_not_iconfluent`, `grounded_iconfluent`, `grounded_acyclic`, packaged as `causal_dag_free`. |
| `Leanuweave/Move.lean` | The op-log pattern's guarantee, generically (`derived_view_sec`: order-independence + redelivery-immunity + invariant enforcement), and its price on a concrete miniature (`view_not_stable`). |
| `Leanuweave/Spec.lean` | **A fluid, proof-carrying composition DSL**: schemas are ordinary `×`/`→` types, and a `Verdict` is either an `IConfluent` proof or a counterexample that *transports through the combinators* — the worked example poisons one field of a loom document and gets a whole-document repro out. |
| `Leanuweave/ORSet.lean` | Removable sets both ways: the OR-Set's add-wins guarantee correctly scoped (`orset_present_survives`) and unscoped presence refuted (`orset_present_not_iconfluent` — the both-sides-tombstone anomaly); the causal-length set's presence free by per-key selection (`clset_present_iconfluent`), with the cross-element failure (`clset_cross_element_not_iconfluent`) completing the "selection lattices compose into non-selection lattices" trilogy. |
| `Leanuweave/Causality.lean` | The vector-clock order **is** the lattice order (`vclock_leq_iff`), concurrent merges make strict progress (`concurrent_merge_strict`), and fork/equivocation evidence is monotone-forever (`fork_evidence_iconfluent`) with no unilateral framing (`no_unilateral_evidence`) — the accountable-BFT primitive for multiplayer. |
| `Leanuweave/MVRegister.lean` | The multi-value register as a derived view: the visible set is an antichain (`view_antichain`), concurrent writes both surface (`conflict_surfaces` — the anti-LWW), and resolution is just a write (`resolution_is_a_write`). |
| `Leanuweave/Segmented.lean` | Whittaker-style segmented I-confluence: conservative over the plain judgement (`iconfluent_iff_trivially_segmented`), and the punchline pair — one budgeted invariant, *both* verdicts (`budget_not_iconfluent` / `budget_segmented`): spends free within an allocation, coordination only at re-allocation. |
| `Leanuweave/Weave.lean` | universal-weave's README feature list, feature-by-feature verdicts, plus the loom-specific theorem: a **shared replicated active path is not a CRDT** (`active_path_not_iconfluent`) — make activation per-user (proved free). |
| `Leanuweave/Exec.lean` | The **executable kernel**: the move-log replay (ordering + cycle-skip), authored in Lean, `@[export]`ed, compiled to C by lake. The refinement theorem to `Move.lean`'s abstract model is named open work in its header. |
| `Leanuweave/Audit.lean` | Every keystone's axiom footprint pinned with `#guard_msgs`: a `sorry` or `native_decide` anywhere fails the build. Two theorems (`grounded_acyclic`, `derived_view_sec`) are axiom-free entirely. |

## The Rust (`rust/`)

`leanuweave` wraps the **Lean-compiled kernel** rather than re-implementing it:
`build.rs` runs `lake build`, compiles the emitted C for every module plus a
three-function shim (`shim.c`), and links the Lean runtime. Building the crate
therefore requires a Lean toolchain ([elan](https://elan.lean-lang.org)) — by
design: the semantics have one home.

- **`causal::CausalWeave<T>`** — append-only content-addressed DAG (storage,
  blake3 hashing, indexes: the deliberately dumb jobs Rust keeps). Grounded by
  construction, so `merge` is skip-if-present union with **no cycle check** —
  the theorems are why that's sound. Same-id-different-bytes is refused as
  corruption (`IdCollision`), never silently deduped.
- **`movelog::MoveLog`** — moves as a grow-only op set whose replay
  (ordering + cycle-skip, the parts that must be *right*) is `Exec.lean`'s
  kernel, called through FFI. **No Rust replay implementation exists to
  drift.** Tests replay the Lean witnesses scenario-for-scenario through the
  real kernel, including `view_not_stable`.

**Claim discipline:** the Lean theorems verify the *design*; the replay
semantics are Lean-authored and compiled in. Still unverified: the
storage/index/codec glue, the shim, Lean's C backend, and the refinement of
`Exec.lean` to `Move.lean`'s abstract model (named open work). The tests are
good tests and zero formal evidence.

## If you are building a loom

- **A single-device or embedded weave** — the data layer's verdict is
  `causal_dag_free`: with content-derived ids and parents fixed at creation,
  the store needs no coordination machinery on any hardware, and node moving
  is best kept log-derived rather than stored-parent mutation (`Move.lean`).
- **A multiplayer weave** — the merge you need is the union in
  `CausalWeave::merge` + `MoveLog::merge`. The part that feels missing from
  every CRDT library is the part `acyclicity_not_iconfluent` proves *cannot*
  be a library feature — it is a policy choice, and this repo's job is to
  price the choices. Keep the active path per-user
  (`active_path_not_iconfluent`), let concurrent edits surface as visible
  forks (`conflict_surfaces` — a loom is the one UI where forks are the
  product), and hold equivocating peers accountable with monotone evidence
  (`fork_evidence_iconfluent`).
- **UI over replicated state** — `view_not_stable` is the theorem to design
  around: derived views can *shrink* when older ops sync in; treat replay
  output as watchable state, and consider surfacing skipped ops to the user
  rather than silently dropping their move.
- **Text** — nothing here competes with loro's sequence CRDTs; this is the
  structural layer around them.

## Building

```sh
lake build          # the proofs; Lean core only, no mathlib, ~30s cold
cd rust && cargo test   # builds the Lean kernel to C and links it (needs elan)
```

## Provenance

Written by ember + Claude as a gift to the weaver ecosystem, drawing on the
[dregg](https://dreggnet.com) metatheory's confluence/blocklace developments
(re-proved here mathlib-free from Lean core). Literature: Bailis et al.
(coordination avoidance, VLDB'15) · Shapiro et al. (CRDTs, SSS'11) ·
Kleppmann et al. (move op, TPDS'21; SEC in Isabelle, OOPSLA'17) ·
Almeida–Shapiro (blocklace, 2024) · Whittaker–Hellerstein (segmented
I-confluence, VLDB'19). PDFs of most of these live in the authors' pockets;
ask and we'll point you at them.

License: Unlicense OR MIT, same spirit as universal-weave.
