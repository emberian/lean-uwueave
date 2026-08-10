# leanuweave

**Machine-checked answers to "isn't the hard part of a DAG/tree CRDT just
enforcing the requirements of a DAG/tree?" — plus the Rust that follows them.**

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
| `Leanuweave/Weave.lean` | universal-weave's README feature list, feature-by-feature verdicts, plus the loom-specific theorem: a **shared replicated active path is not a CRDT** (`active_path_not_iconfluent`) — make activation per-user (proved free). |
| `Leanuweave/Audit.lean` | Every keystone's axiom footprint pinned with `#guard_msgs`: a `sorry` or `native_decide` anywhere fails the build. Two theorems (`grounded_acyclic`, `derived_view_sec`) are axiom-free entirely. |

## The Rust (`rust/`)

`leanuweave` (one dependency: blake3) implements the blessed fragment:

- **`causal::CausalWeave<T>`** — append-only content-addressed DAG. Grounded
  by construction (`rank = 1 + max parent rank`; parents must exist to be
  named), so `merge` is skip-if-present union with **no cycle check** — the
  theorems are why that's sound. Same-id-different-bytes is refused as
  corruption (`IdCollision`), never silently deduped: convergence proofs
  assume ids resolve identically, so a collision must be loud.
- **`movelog::MoveLog`** — moves as a grow-only op set + deterministic
  timestamp-ordered cycle-skipping replay (Kleppmann-style). Tests replay the
  Lean witnesses scenario-for-scenario, including `view_not_stable`.

**Claim discipline:** the Lean verifies the *design*; the Rust is an unverified
implementation of it. The witness-mirror tests are good tests and zero formal
evidence — no "translation validation" is claimed, because there is no formal
semantics of Rust to state it in.

## Mapping to the universal-weave roadmap

- **M1 embedded DAG** — the data layer's verdict is `causal_dag_free`: if node
  ids stay content-derived and parents fix at creation, the store needs no
  coordination machinery, on a microcontroller or anywhere else. Node moving
  should be log-derived, not stored-parent mutation (`Move.lean`).
- **M2 multiplayer DAG** — the merge you need is the union in
  `CausalWeave::merge` + `MoveLog::merge`; the DAG-CRDT that "no CRDT library
  supports" is exactly the grounded fragment, and the part genuinely missing
  from libraries is the part `acyclicity_not_iconfluent` proves *cannot* be a
  library feature — it's a policy choice this repo makes explicit. Keep the
  active path per-user (`active_path_not_iconfluent`).
- **M3 UI/UX** — `view_not_stable` is the theorem your UI layer must design
  around: derived views can *shrink* when older ops sync in; treat replay
  output as watchable state, and consider surfacing skipped ops to the user
  rather than silently dropping their move.
- **loro interop** — nothing here competes with loro's sequence CRDTs; this is
  the structural layer around them. The `TODO.md` item "DAG-based documents
  (waiting on Loro to implement DAG CRDTs)" doesn't need to wait: the grounded
  fragment is implementable today (and is, in `rust/`).

## Building

```sh
lake build          # the proofs; Lean core only, no mathlib, ~30s cold
cd rust && cargo test
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
