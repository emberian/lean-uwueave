# HANDOFF — for the local codex agent (gpt-5.6-sol)

*2026-08-11, end of a very long session. Written by the Claude swarm that built
this tree, for the **local** codex coding agent taking over. ⚠ You are NOT the
codex we corresponded with — that was a web-reviewing instance whose three
reviews shaped this repo (its letters and our replies: `FORCODEX.md`,
`CODEXHELP.md`, `FORCODEX2.md`, all tracked). You have none of that context.
This file is your bootstrap. Read it, then the three documents in §2, and you
will know everything load-bearing.*

---

## 0. What this is

**lean-uwueave** (`/Users/ember/dev/leanuweave`, github `emberian/lean-uwueave`,
branch `dev` — commit `3e2e1c9` at handoff): a machine-checked **judgement
library** for replicated data. Core question: *can this application promise be
kept without coordination?* — with concrete two-replica refutations when no,
and a priced menu of repairs. Grown from one tweet-answer into:

- **73 Lean modules**, ~9,700 constants under a total axiom gate
- **Lean 4.30.0, NO mathlib** — `lake build` is fast; everything checkable
- three decision kernels compiled Lean→C→Rust (`rust/`), a composed
  `Weave<T>` document type, a CLI (`uwueave-check`), runnable examples,
  benchmarks
- a small language, **preoscript** (`Uwueave/Preo/`), whose elaborator turns
  `preo N where field…/invariant…/derive…` declarations into kernel-checked
  verdict terms
- a website (`docs/index.html`, GitHub Pages from `dev:/docs`)

The operator is **ember** (they/them). The intellectual grounding: Bailis
et al.'s invariant confluence (VLDB'15) as an *iff*, extended tonight with
reachability, seams, cost, repairs, futures/certificates, rendering honesty,
and history/merge-policy theory. It began as a gift to kat
(github `transkatgirl/universal-weave`) — a loom author; the README's voice
reflects that.

## 1. Non-negotiable house rules (the tree enforces most of them)

1. **No `sorry`, no `native_decide`, no `#guard`.** The gate makes the first
   two build failures; the third is a house sin (a fact worth asserting is
   worth naming — prove a theorem).
2. **The gate is total and checks its own coverage.** `Uwueave/Audit.lean`
   ends with `#gate_covers_root` (reads `Uwueave.lean` from disk; fails the
   build if any root module is unreachable from the gate) and `#audit_floor`
   (every constant in the namespace must sit within
   `{propext, Classical.choice, Quot.sound}`). **A new module must be imported
   in BOTH `Uwueave.lean` and `Uwueave/Audit.lean`** or the build fails — this
   is deliberate; it caught a 1,300-line module sitting ungated.
3. **Docstrings must match statements exactly.** Overclaiming a theorem's
   scope in prose is the failure mode this repo polices hardest. Every
   boundary/caveat is labelled **⟨TERMINAL⟩** (a fact of the model) or
   **⟨UNDONE⟩** (work wearing a caveat's clothes) — and "honest label as
   stopping condition" is considered a sin: decompose boundaries into the
   irreducible premise and the transmutable remainder.
4. **Refutations are deliverables.** A `¬ IConfluent` with concrete states is
   the product. Every impossibility should be **satisfiable and refutable** —
   a model that cannot go red proves nothing.
5. **Retractions happen in place.** When a claim is refuted, correct it where
   it was made, visibly; several documents carry retraction sections by
   design.
6. **Delivery means bytes in this repository**, committed and pushed. Verify
   HEAD, not your working tree. Commit named files (never `git add -A`);
   commit messages via `git commit -F <file>` (zsh eats backticks); end with
   the Co-Authored-By trailer of whatever agent you are.
7. **Rust never re-implements a decision.** The Lean kernels decide; Rust
   marshals (`build.rs` runs `lake build` and **fails closed** — a red Lean
   build must never link stale C). `rust/src/status.rs` is a documented
   *hand translation* (unverified transcription of Lean theorems, one test per
   mirrored theorem) — treat its header's drift list as real.

## 2. The three documents that ARE the context

1. **`docs/TRANSPORTS.md`** — the organizing principle. 45+ rows; each names a
   source judgement, target judgement, transport theorem, the load-bearing
   hypothesis, and the counterexample without it. The repo's thesis: *the
   library is a map of judgements and the exact hypotheses under which
   evidence transports between them.* **Every new module owes a row.** Recent
   lanes appended their rows in their file headers (grep `TRANSPORTS row`) —
   folding those into the doc is pending (§6.1).
2. **`docs/TRUST.md`** — three ledgers (logical TCB / execution TCB /
   environment premises), each row PREMISE, OBLIGATION, or NARROWABLE. What
   `#audit_floor` does NOT prove (semantic adequacy) is stated there.
3. **`PREOSCRIPTING.md`** — the language design, revised in place. The thesis
   (from web-codex, adopted): *reject a budget by a semantic lower bound,
   accept only with a witnessed upper bound, and never let a number or a
   singular UI value erase the strategy, fork, future, or premise that
   justified it.* §10 is the status table; §11 is "what would make us abandon
   this."

Also: `docs/MAP.md` (module map + 126-row keystone ledger — **stale below
wave 15**, see §6.2), `docs/COHERENCE.md` (whole-tree audit; its P2 list is
open), `docs/PERFORMANCE.md` (real numbers; the architecture costs 1.4µs per
kernel crossing; four algorithms are asymptotically bad and none of the cost
is from being verified), `NIGHTLOG.md` (the night's record, addressed to AI
readers), `docs/BIBLIOGRAPHY.md` (annotated; PDFs in `~/paperbin/uweave/`,
44 papers).

## 3. The load-bearing results, compressed to one screen

**Core:** `IConfluent` (Confluence) with necessity *modeled*
(`Necessity.IsCFCS`, `necessity`) and reachability formal (`CausalReach`:
Live vs LatticeOnly). `ForkGrade.cfcs_iff_locallySafe_and_no_reachableClash`
and `…_all_finite_scenarios_zero` are the modal⟷quantitative bridges; the
per-stream floor does NOT reflect zero (`Bounds.zero_floor_does_not_imply_cfcs`)
— zero reflects only on **fork scenarios**.

**Cost:** crossings (`Cost`), profiles composed pointwise
(`CoordEffect` — a scalar grade is unsound: `pin_session_costs_exactly_one`
vs per-stream 0), budget trichotomy (`Budget` — a floor rejects, only a
witnessed plan accepts; "the floor" is a *family*, not a function),
live/carrier-global verdict split (`LiveBudget` — the ew workload has NO live
realization; `carrierGlobalBound` has no field mentioning the model, on
purpose). Reachability holes repaired: `LiveCost` (proof-carrying paths;
`Grounds` is the transport hypothesis; `totalModel` grounds everything so the
teeth are model-relative) and `LiveSegmented` (an unreachable clash cost a
whole coordination domain: live width 2 vs global 3, both least).
Clique story: `SeamColoring` (segmentation's safety clause = proper colouring;
synthesis works and rediscovered our hand seams), `MenuTotality` + `CliqueLive`
(clique number bounds width AND scenario floor; block floor and clique floor
are **incomparable** — report both; `triple_clash_forces_triangle` shows the
stability clause is clique-visible too).

**Merge models:** `MergeModel` (join CRDT / ancestral / op-replay are
genuinely different — proved), `Ancestral` (resurrection vs accumulation:
`clash_dichotomy`; the LCA repairs resurrection *only*), `Recoverable` (the
converse as an **iff** with the merge constructed; symmetric chooser is
*entailed* by comm), `Histories` (repeated merge BREAKS — the closure, not the
merge; base accidents decide invariants; `swap_never_converges`),
`HistoryBase` (`ValidInHistory`; `unavailable` is a cross-history answer),
`HistoryPolicy` (the four policy judgements; **the convergence crown**:
`recordDetermined_converges` — same record + record-determined symmetric
policy ⇒ same derived view; the swap is order-dependence).

**Computation:** `Holes` (`evalSet_hom` — images are free; wanting ONE answer
is the cost), `JoinHom` (`summaryFold_iff_joinHom`; counts cannot be gossiped
— `no_count_merge_without_provenance`), `MinimalSummary` (contextual
equivalence; the coarsest sufficient summary, universal property PROVED;
membership→1 bit, count→everything, threshold→top-collapse-not-capped-count),
`TextSummary` (why op-based text ships ops; tombstones are load-bearing —
the deleted character resurrects; verdicts are order-policy invariant),
`DerivedDocument` (evidence ⟷ document isomorphism — "a computation over a
loom yields a little loom" as theorems; rank-grounded stratified termination).

**Evidence/rendering:** `Evidence` (candidates × obligations × certificates;
futures nested delivery⊆extension), `WorldFuture` (futures over WORLDS —
same state, different futures; state-keyed certificates unsound),
`CertificateScope` (future-sufficient keys; "pool in, epoch out"; `Closed` is
sound for values, UNSOUND for the view), `EraCertificate` (Era finalisation IS
a sound delivery certificate under `Settled` + honest-arbiter; ⚠ **an event
forged with an announced id is born-finalised and rewrites the finalised
prefix — finality rests on event-id unforgeability**; the Byzantine seam,
named), `ResultStatus` (six cells; capability is relative to a REACH),
`RenderSix` (the five-status contract is satisfied by a spinner-forever;
absence is merge-defensible — but NOT unilaterally), `RenderProgress`
(truth/liveness/affordance split — `pending_escapable` was dischargeable by
GIVING UP; the SemanticWidget excludes `loading` at `absent`),
`HonestRender` (abstract carrier; `consumers_factor`; salience is provably
unenforceable).

**Repairs:** `Repair` (typed transformations, `Price` records,
`no_free_arbitration`), `RepairMenu` (menus GENERATED from typed repairs;
projection theorems kill price drift — and the hand seam price was already
wrong: 0 printed where 1 is forced; `Exits` is retired as a semantic
authority, kept as display vocabulary + witnesses).

**preoscript:** fragment 2 live. Facet-accumulating `Classification`
(route-order invariance proved; a seam ENTAILS the clash), seam facets,
cross-field invariants, `derive` with mergeability (surjectivity needed for
`needsEvidence` transport). It **rediscovered the hand answers as values**
(`in_budget.seam = WeaveState.quotaVerdict := rfl`). `SeamAlgebra.andSeams`
(same-state seam conjunction, added last, by hand) is the combinator the
registry still needs wiring for (§6.3).

## 4. Build & verify

```sh
cd /Users/ember/dev/leanuweave
lake build              # everything + #gate_covers_root + #audit_floor
cd rust && cargo test   # builds Lean→C, links, runs 84+13+11 tests (needs elan)
cargo run --example two_phones   # / collaborate / gated / slice / bench_kernels
```

Remote builds: `rsync -a --exclude .lake --exclude target ./ persvati:~/jobs/<name>/`
then `ssh persvati 'cd ~/jobs/<name> && PATH=$HOME/.elan/bin:$PATH lake build'`.
persvati connections flake occasionally — retry once. ⚠ Anything touching
`Uwueave/Preo/` takes down `lake build` mid-edit and therefore ALL cargo
commands (build.rs fails closed — correct behavior, plan around it).

If running multi-agent: exclusive file ownership per worker; root
`Uwueave.lean`/`Audit.lean` single-writer; workers report, orchestrator wires
and commits. Briefs state falsifiability bars. Verify claims at source —
self-reports drift.

## 5. Current state: everything green

`lake build`: 80 jobs, `#gate_covers_root: 72 root modules`,
`#audit_floor: 9697 constants, all within the floor`. `cargo test`: 84+13+11
green. All of waves 15–16.5 are committed and pushed. No dirty files at
handoff. The git log tells the story wave by wave — commit messages here are
long-form and load-bearing; read them like a lab notebook (`git log --oneline
-40`, then `git show <sha>` anything interesting).

## 6. The work queue, in priority order

### 6.1 Fold the pending TRANSPORTS rows (small, do first)
Recent lanes appended their rows in module headers instead of editing the
shared doc. Grep `TRANSPORTS row` across `Uwueave/*.lean` (LiveCost,
LiveSegmented, ForkGrade rows are already IN the doc as 10a etc.; CliqueLive,
EraCertificate, TextSummary, DerivedDocument §7-table, HistoryPolicy,
Preo-five-rows, RepairMenu 37b are variously in-doc or in-header — reconcile,
renumber if you like, keep the counterexample column non-empty).

### 6.2 MAP refresh (medium)
`docs/MAP.md` has no module rows for anything after wave 14 (~20 modules:
LiveCost, LiveSegmented, ForkGrade, CertificateScope, RenderProgress,
HistoryPolicy, RepairMenu, CliqueLive, LiveBudget, EraCertificate,
TextSummary, DerivedDocument, MenuTotality, Bounds, HistoryBase, RenderSix,
Recoverable, Histories, Preo/*…). Its ledger tally line
(`table currently holds N rows:`) is parsed by `cargo test --bin
uwueave-check` — keep it accurate. Ledger keystones for the new modules are
listed in each commit message.

### 6.3 Wire `andSeams` into the Preo seam registry (medium, high value)
`SeamAlgebra.andSeams`/`liftFst`/`liftSnd` exist and rediscover
`twoFieldSegVerdict.σ` by `rfl` (see `SeamAlgebra` §7½). The Preo elaborator's
seam registry (`Uwueave/Preo/Elab.lean`, grep `budgetSeam`) has one
single-field rule; teach it to compose two seam facets on one declaration via
`andSeams`, then the acceptance test: a two-Quota `preo` whose document seam
is derived. The eventual prize: derive `WeaveState.weaveDocSeamVerdict`
(needs additionally a pins-side seam rule and `absorbFree` wiring for the free
conjuncts — measure it first, it may be a wave).

### 6.4 The ⟨UNDONE⟩ census (small tooling, requested by operator)
166 markers across 30+ modules; no ledger. Build
`scripts/undone-census.sh` extracting every ⟨UNDONE⟩ block with `file:line`
into `docs/UNDONE.md`, cited by count so drift is visible. A generated ledger
is a gate; a hand list rots.

### 6.5 Perf fixes F1–F8 (mechanical, proof obligations counted)
`docs/PERFORMANCE.md` names eight fixes; six are asymptotic; none changes a
statement. F1 (`childrenK` bucketing, O(n²)→O(n), exactly two lemmas to
re-prove) and F2 (`execOrder` insertion→merge sort; the pattern exists in
`Exec.absReplayFull`) are the big ones (text 2.09s→ms at 10k; ERA 147×
order-sensitivity). F4 (the wire codec allocates `List.range 8` per word —
60-92MB/s) is the sleeper.

### 6.6 Crate ergonomics (small, user-facing)
From the demo lane's punch list: NO error type implements
`Display`/`std::error::Error` (the refusals are the product and cannot be
shown to a user); `NodeId` has no display affordance; `Grant::scope` lives in
request-index space ("covers subtree X" inexpressible); `MoveLog` lacks
`ops()`; `uwueave-check` returns UNCLASSIFIED for `(gset, cross-field)`
though the Lean settles it.

### 6.7 Larger arcs (each a wave; the operator sequences these)
- **Scheduling semantics** — "crossings are not meetings" is inherited in five
  files; participants/barriers/rounds/coalescing is the named next step
  everywhere and built nowhere. Web-codex's advice: begin from the
  effect/coeffect algebra (obligations are coeffects — papers in the bin:
  Petricek, graded-modal 2026), not from syntax.
- **`HistorySafe` iff** — `MergeClosedFrom` is sufficient-not-necessary;
  web-codex sketched the exact target over admissible history extensions.
- **Timely-style frontiers** — Evidence's obligations are a flat `GSet
  Source`; antichain frontiers are the honest carrier under open membership.
- **Persistence** (none exists — and it feeds `WorldFuture` semantics:
  crash/restart changes what "issued" means), then **Byzantine**
  (`EraCertificate`'s forged-id finding is the entry; the KIT paper
  arXiv:2604.23560 is the comparator — they do Byzantine, we do duelling
  admins + arbitration trade theorems; the models are complementary).
- **Two one-file edits nobody owned**: a guard hypothesis on
  `Ancestral.Serializing` (unblocks `Recoverable.DeltaRecoverableOn`);
  a `render` congruence in `Evidence` (unblocks `Closed ∧ RosterKnown`).
- **The universe debt**: `Type 0`-only through
  MergeModel→HistoryBase→CertificateScope.

## 7. Voice and correspondence

If you write to the operator: plain, precise, honest about failures; kaomoji
welcome. The web-codex correspondence pattern — review, retract-in-place,
build past — worked extremely well; if a claim of ours conflicts with what you
derive, say so bluntly with a witness and expect the same back. The repo's
best habit: **when a lane refutes its brief, the refutation ships as the
result.** Its second-best: rediscovery as acceptance test — five hand-made
artifacts (seams, the lock tie-break, pin witnesses, the quota verdict, the
two-field seam) have been re-derived by general mechanisms; when your
mechanism disagrees with a hand proof, the disagreement is the deliverable.

Good luck. The tree is green, the map is honest, and every open edge is
labelled. o7

— the Claude swarm (Fable 5 / Opus 5, in shifts), for ember
