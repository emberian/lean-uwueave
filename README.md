# lean-uwueave

**When two people change the same thing at the same time on different devices,
something has to happen when their changes meet.** Usually what happens is
decided by accident — whatever the code did — and discovered by users, as a
number that was quietly wrong or an edit that silently vanished.

This is a careful, machine-checked map of that moment. It says which promises
your software can keep with **no coordination at all**, which can never be kept
that way, and — when the answer is *never* — what your actual options are and
what each one costs.

Every "no" comes with a small, concrete story of two devices you can watch fail.
Every price comes with the theorem that justifies it. And the trickiest
decisions ship as *compiled proofs*, not as code someone wrote twice.

## The whole idea, in two phones

**A shared shopping list.** You add eggs; your partner adds bread. Offline. When
the phones sync, you have both — no conflict, no server, no waiting. This works
every time, for any number of phones, and it isn't luck: *"the list only grows"*
is the kind of promise that survives meeting.

**A shared $100 balance.** You spend $80; your partner spends $80. Each phone,
alone, was being perfectly responsible. They sync: $160 spent, and no clever
merge can un-spend it. This is not an engineering gap awaiting a better library
— it's a **theorem** (Bailis et al., 2015) that no coordination-free system can
keep that promise. You weren't bad at this. The universe said no.

Everything here lives between those two phones. And the useful part is that
"the universe said no" is *not* the end of the conversation — it's the start of
a priced menu:

- **Split it up front.** Give each device $50 of its own. Both stay within
  their share, both merge freely, and you only talk when you re-divide.
- **Let someone arbitrate.** A designated referee orders the events; everyone
  agrees on the same winner. Costs trust, and some rollback.
- **Keep both and show them.** Don't pick — surface the disagreement to the
  person, who has context the algorithm doesn't.
- **Change what you promised.** Sometimes "at most one" was never the real
  requirement.

Each of those is a theorem here, and — the part we're proudest of — some of
them **provably don't apply** to your particular problem, so the menu you get is
short and honest rather than a list of vague possibilities.

## Try it

Those two phones are a program. You need [elan](https://elan.lean-lang.org) on
your `PATH` — the decision layers are compiled from the Lean, so the Rust build
insists on a working Lean toolchain rather than linking whatever was on disk
last time. A data-free `RuntimeInit` module names the five native-kernel modules;
the build takes their exact transitive closure from Lake, byte-snapshots it, and
refuses stale, extra, missing, or mixed-generation archive members. The first
build is slow; after that it's incremental.

```sh
git clone https://github.com/emberian/lean-uwueave && cd lean-uwueave/rust
cargo run --example two_phones
```

```
lean-uwueave — the whole idea, in two phones
═══════════════════════════════════════════

━━ 1. the shopping list — the promise that survives meeting ━━

  phone A, offline:  + eggs   [519add]
  phone B, offline:  + bread  [38932b]

  ...the phones sync...

  phone A now holds:  bread, eggs
  phone B now holds:  bread, eggs

  A.merge(B) == B.merge(A):        true   (commutative)
  merging the same delta twice:    true   (idempotent — gossip may repeat)
  still acyclic, no check run:     true   (grounded_acyclic)

  Nothing was lost, nobody waited, and there was no server. This is
  what "FREE" means: the merge provably cannot break "the list only grows".

━━ 2. the shared $100 balance — the promise that cannot ━━

  The rule the app promises its user:  balance >= 0

  start:                       $100
  phone A, offline:  -$80  →   $20    legal on A  (20 >= 0)
  phone B, offline:  -$80  →   $20    legal on B  (20 >= 0)

  ...the phones sync...

  merged:                      $-60   ← the rule is broken
  merged the other way:        $-60   ← and it converges perfectly
  both directions agree:       true   (it is a correct CRDT)
```

That merge isn't a strawman: it's a genuine semilattice join, commutative and
idempotent, and it loses nothing. It still overdraws the account, because the
promise was never one a merge could keep. A third section — trimmed here —
shows the priced exit, where a spend runs out *locally and immediately* instead
of waiting for a peer, and re-dividing the budget is the only thing that needs
a meeting.

Two more examples follow the same shape:
[`collaborate`](rust/examples/collaborate.rs) builds a real document with two
people in it and shows a move that un-happens after a sync (named, in a
per-op trace, rather than silently), and [`gated`](rust/examples/gated.rs)
revokes authority mid-flight and shows the ops still sitting in storage while
the view drops them. [`rust/README.md`](rust/README.md) is the crate tour.

### Ask it about your own schema

The same two promises, handed to the tool instead of narrated
([`rust/examples/two_phones.schema`](rust/examples/two_phones.schema)):

```
field list: gset            # the shopping list
field wallet: pncounter     # the shared balance

invariant list: member      # "an item you added never disappears"
invariant wallet: balance   # "the balance never goes negative"
```

```sh
cargo run --bin uwueave-check -- examples/two_phones.schema
```

```
FIELD   SHAPE      INVARIANT  VERDICT    THEOREM(S)
-----------------------------------------------------------------------------------------------
list    gset       member     FREE       gset_mem_iconfluent — Uwueave/Catalog.lean
wallet  pncounter  balance    ESCALATES  pncounter_nonneg_not_iconfluent — Uwueave/Catalog.lean
```

Every `ESCALATES` comes with the two devices you can watch fail, and with the
exits priced:

```
wallet · balance — ESCALATES
  cites: pncounter_nonneg_not_iconfluent — Uwueave/Catalog.lean
  the two-replica repro:
    Both replicas start from the same 10 credited. Each spends 10 against its
    own decrement key — individually legal, net exactly 0. The merged counter
    has spent 20 against 10: net −10. A bounded shared resource cannot be
    replicated coordination-free.
  ways out:
    - escrow: pre-partition the bound into per-replica quotas. Each replica's
      local bound survives every merge, and the global bound follows by
      summing the quotas.
      (escrow_local_bound_iconfluent — Uwueave/Catalog.lean;
      escrow_global_bound [unlisted] — Uwueave/Catalog.lean)
    - segmented (re-allocation seam): run free within an allocation and
      coordinate only to change the allocation — one invariant, both verdicts,
      with the seam named.
      (budget_segmented — Uwueave/Segmented.lean)
```

`uwueave-check --help` lists the ten shapes and eleven invariant kinds it
knows. A pair the Lean development doesn't settle comes back `UNCLASSIFIED`
rather than guessed — [`rust/examples/loom.schema`](rust/examples/loom.schema)
is a bigger, real schema that deliberately contains one.

## What you can use without reading any proofs

- **A command-line tool.** Describe your app's shared data in a few lines;
  `uwueave-check` tells you which promises are free, which escalate, and which
  are free *within a seam* — each with the theorem name, so you (or a friend, or
  a model) can check the receipt.
- **The counterexamples.** Every impossibility comes with real states — usually
  three lines — that paste straight into your test suite in any language. A
  refutation here is a gift: it's the bug your users would have found, delivered
  early and politely.
- **A Rust crate.** An append-only content-addressed document store,
  collaborative text, node moving, membership and roles — where the delicate
  decisions are compiled from the proofs rather than reimplemented.
- **Four explicit persistence surfaces.** `ArtifactJournal` keeps exact,
  Lean-validated Preoscript artifact-v2 frames inside a checksummed physical
  log; `DocumentJournal` separately persists the current unauthenticated typed
  `MoveLog` subset and validates checkpoints against their mutation prefix;
  `HistoryJournal` stores canonical explicit-id events whose strictly ordered
  parents must already be present, so every accepted prefix is causally closed.
  Exact retries are idempotent, while missing parents and same-id/different-event
  collisions fail loudly. An optional `BufferedHistoryJournal` accepts
  out-of-order delivery into a visible finite in-memory buffer and drains ready
  layers deterministically. Pending entries are deliberately volatile and
  disappear on reopen; only the causally closed prefix is durable. The separate
  `HistoryArrivalJournal` is the durable-arrival endpoint: it records every
  accepted canonical arrival before classification, checkpoints the exact
  accepted/materialized/pending state, and reconstructs pending work on reopen.
  They provide per-record bounds, sequence-addressed retry, locking, sync
  policy, and torn-tail/corruption handling. They do not provide authenticated
  v4 admission, whole-journal resource bounds, multi-record transactions,
  anti-rollback state, or a theorem about the host filesystem. The exact
  boundary is in **[the runtime architecture](docs/RUNTIME.md)**. An explicit
  Lean artifact command now emits real checked `ArtifactDurableBytes`; a Rust
  integration test admits them, appends under `SyncData`, closes/reopens, and
  checks exact recovery. That is tested host evidence, not a claim that
  `writeBinFile`, `sync_data`, or any filesystem survives every crash.
- **A checked language surface.** `preo` declarations now cover ordinary and
  keyed fields, application carriers with explicit planting seeds, invariants,
  derived summaries, retained-world futures, typed protocol terms, and
  proof-carrying sessions. The native `preo_protocol` grammar spells all six
  protocol constructors and emits the exact semantic term, elaboration,
  session, plan, five limits, and witnessed profile bound. Standalone commands
  name fully indexed certificates and accept five-currency budgets only through
  one witnessed plan. Automatic finite verdict search refuses work above its
  explicit 64-state / 4,096-pair caps rather than disguising resource failure as
  an inapplicable route; explicit `classifyFinite` remains total. The elaborator
  is split into bounded phases with transactional surface commands: optional
  probes may decline as data, mandatory emissions fail loudly, and a late
  failure leaves no declarations or extension rows behind. Subprocess canaries
  verify declaration absence and same-name reuse after rollback. The checked
  `preo_export` manifest projects those meanings to canonical first-order
  artifacts, format-v2 framed bytes, and a validated budget-bearing data-only
  Rust representation; none of those transport layers can manufacture a
  verdict, certificate, plan, or permit. `Uwueave.Preo.Quickstart` is the
  executable end-to-end example: one custom application state is explicitly
  projected into a typed environment, bound to one named future and exact-world
  certificate, planned through the native protocol surface, and exported as a
  checked V3 query/result/certificate artifact. Its 71,011-byte canonical frame
  is written, reopened byte-for-byte, concatenated as a two-record logical
  journal, and inspected by the bounded diagnostic-only Lean inspector. The
  companion red gates reject a wrong projection, future, certificate, plan, or
  world at their typed boundaries. `preo_export_v3` now exposes that construction
  as one transactional command. It accepts only an exact authenticated-observation
  adapter, exact checked plan/budget/query/future/world values, explicit work and
  validation bounds, and builds result/effect/disclosure/certificate rows only
  through checked constructors. A bare certified report or structural lookalike
  is refused because neither retains the external authenticity and independent
  running-reach premises. The command is acceptance-green but not yet
  performance-green: its serialized N=16 benchmark measures **6.706 MiB/item**,
  above the existing 4 MiB/item RSS ceiling. Typed expression evidence likewise retains exact
  value/source/child-path attribution; its verified entry point still requires
  the deployment to prove its own source-authenticity relation.

- **Authenticated context is now compositional without becoming magical.**
  Accepted signed events must also occur in an authentic issuance trace.
  Authenticated frontier progress binds the issuer/source, roster, timestamp,
  old/new frontiers, issued pool, and delivered pools to one exact signed event;
  typed-position delivery separately checks causal origin, version reach, and
  an active one-use grant. A canonical 369-byte V4 sidecar retains those checked
  request/context facts as bounded neutral data, but decoding it cannot recreate
  the private checked value. Its `⟨4,162⟩` durable framing is intentionally not
  the `UWV4` signed-request wires and is not a verifier. The legacy 107-byte
  kind-1 fixture still crosses the narrow five-refusal syntax endpoint. A new
  context-bound kind-3 request signs a nonempty opaque context commitment;
  Lean alone decodes it, enforces eight shape and three host-width checks, and
  emits the exact kind-4 projection consumed by later host stages. Rust never
  parses either request wire. A separately pluggable verifier includes a
  concrete keyed-BLAKE3 symmetric-MAC profile scoped to context, document,
  genesis, issuer, and key epoch. Its acceptance is a trusted host attestation,
  retaining the exact scope/signing/signature byte vectors plus unkeyed hashes,
  not a public-key signature proof, EUF-CMA result, authority, membership,
  nonce, execution, or storage decision. A separate `UWAMV401`
  `AuthenticatedMoveJournal` can atomically retain one crate-private
  already-checked record with its nonce/operation scopes, exact execution-base
  binding, and hash-chained prior head. The externally pinned head therefore
  commits to that binding and detects rollback relative to the caller's pin. The landed
  `AuthenticatedRuntime` exposes only raw kind-3 admission and orders Lean
  projection, exact-byte verification, retry/collision classification, pinned
  context under one fixed document/genesis/context/execution binding. The last
  is a domain-separated framed digest of the concrete topology and grant/
  revocation base, not an authenticator. Stable-id resolution must agree in
  both the provider and actual execution weave; independent
  authority and membership checks, concrete Lean move preflight, durable append,
  then in-memory commit. Definite storage refusal is distinct from indeterminate
  I/O. Externally pinned recovery reprojects and reverifies every stored
  request, reruns the historical
  context/policy/execution checks, compares the complete checked record, and
  replays in prefix order. Storage itself still performs none of those checks;
  unpinned reopen is inspection-only, the policy traits and verifier are trusted
  host code, and neither the external pin nor filesystem durability is proved.
  The focused authenticated runtime/projection suite passes **11/11** end-to-end
  tests. The final serialized `CARGO_BUILD_JOBS=1 cargo test --all-targets --
  --test-threads=1` gate passes **177/177** tests in
  **125.72s real** (**10.49s** compilation, **35.60s user**, **37.86s sys**,
  **1,274,494,976 B** maximum RSS); this is regression-path evidence, not
  admission throughput.

- **Authenticated ERA finality now reaches the certificate layer without
  laundering its premises.** One exact signed progress event supplies accepted
  and genuinely issued source/roster identity; a separate complete-announcement
  proof supplies the truthful ERA worlds, cut, issued pool, delivered log, and
  lawful frontier. Together they yield the delivery-scoped settled certificate
  and its user-level seal. The reusable artifact deliberately forgets the
  signature and retains only the exact ERA key plus semantic acceptance: it
  licenses delivery reuse at that key, not verification, new announcements, or
  cryptographic authenticity.

- **Finite repair and history boundaries now return proof-carrying whole
  values.** `FiniteRepairMenu` checks an explicit row bound and strict stable-ID
  order, then returns the least applicable authored ID with its exact typed
  repair, generated menu row, and complete eight-axis `Price`, or proves every
  listed row inapplicable. IDs are deterministic author policy, not a global
  price order or discovery procedure. `FiniteHistoryDelivery` relates one
  authored complete finite history to explicitly successful coherent settled
  replays; different arrival orders then have the same event-set view. It does
  not infer delivery success, authentication, semantic-history convergence, or
  a Lean↔Rust/filesystem refinement.

## Some things we found that surprised us

**Content-addressing gives you acyclicity for free.** Naming things by the hash
of their contents-and-parents — the way git does — means every edge points at
something older, so an append-only document *cannot* contain a cycle. No cycle
check, at any scale.

**Verified-correct and safe are different things.** A merge can be provably
correct against its own specification and still bankrupt you, because the
specification permitted it. We build both a counter that is verified *and*
overdrawing, and one that is safe *because it silently loses your data*.
Checking the data structure is not checking the application.

**Knowing the ancestor repairs one kind of conflict and never the other.** If
some ordering of the two concurrent actions would have been legal, a three-way
merge (git's model) can recover it — a released lock re-appearing, say. If *no*
ordering is legal — both people really did spend the money — then no merge in
existence helps, and you need one of the priced exits above.

**Asking for exactly one answer is what costs.** Computing over data that's
still arriving is free; *insisting* the result be a single value is provably a
coordination requirement. So a UI that shows `47 + (2 peers pending)`, or shows
both candidates, is not a degraded experience — it's the honest one, and the
cheap one.

**A merged document is still a document.** Even when two people's changes break
a rule — two "pinned" items where one is allowed — the result stays well-formed
enough to render, with both sides visible. Conflicts become something you draw,
not something you crash on.

## Reading further

- **[The map](docs/MAP.md)** — every module, what it settles, and a ledger of
  keystone theorems tagged by how general each is and whether its counterexample
  is actually reachable in practice.
- **[The transports](docs/TRANSPORTS.md)** — every judgement crossing, the
  hypothesis that makes it valid, and the witness showing what fails without it.
- **[The preoscript design](PREOSCRIPTING.md)** — the language contract: retain
  futures, strategies, coeffects, witnesses, and promise changes instead of
  collapsing them into badges or scalar costs.
- **[Performance](docs/PERFORMANCE.md)** — measured baselines, source-level
  complexity diagnoses, and the proved-equivalent optimized execution paths.
- **[The generated UNDONE ledger](docs/UNDONE.md)** — every live `⟨UNDONE⟩`
  marker with a source location; `scripts/undone-census.sh --check` gates drift.
- **[The website](https://emberian.github.io/lean-uwueave/)** — the same material
  with diagrams, for people who like diagrams.
- **[Trust](docs/TRUST.md)** — three separate ledgers of what this rests on:
  logic, execution, and environment. Including what our own build gate *cannot*
  prove. The shared `TrustFloor` policy is also exercised by subprocess canaries
  that must reject a custom axiom, `sorry`, `native_decide`, and a vacuous
  namespace; the Preoscript acceptance suite repeats the forbidden-proof cases
  at generated declarations and covers failure honesty and resource caps.
- **[Runtime architecture](docs/RUNTIME.md)** — the shipping FORMAT-v3 path,
  exact RuntimeInit/Lake native closure, five pure-Rust journal domains, checked V3
  Quickstart and bounded diagnostic inspection, exact durability assumptions,
  and the canonical FORMAT-v4 syntax, context-bound projection, and verifier
  boundaries now composed into the raw-only authenticated-move host path and
  externally pinned recovery contract.
- **[The bibliography](docs/BIBLIOGRAPHY.md)** — every paper behind this, what it
  established, what we took, what we declined. Several entries exist to record
  claims of *ours* that the literature refuted.

## Building

```sh
lake build              # every proof + the total axiom gate (Lean core only, no mathlib)
./scripts/trust-canaries.sh # acceptance tests: the trust gate must also go red
./scripts/preo-automation-canaries.sh # positive/red tactic and transactional gates
./scripts/preo-quickstart-canaries.sh # coherent V3 journey + five typed refusals
./scripts/preo-v3-acceptance-canaries.sh # observed V3 export, rollback, floor, caps
./scripts/wave27-acceptance-canaries.sh # signed context/frontier/V4/durable arrival
./scripts/wave30-auth-runtime-canaries.sh # context-bound projection/refusal/floor matrix
cd rust && cargo test   # asks Lake for the exact native closure, verifies it, and links it
```

The current checkpoint is **185** Lean source modules / **186** full-build jobs
(**162** direct proof-root imports excluding `Audit`) with **25,747** constants
checked by the total axiom gate, **731** MAP keystones, and **135** documented transports. The
generated work ledger records **155** `⟨UNDONE⟩`
markers in **153** blocks across **43** source files. The earlier serialized
kind-1 syntax checkpoint passed **148/148** Rust tests in **31.02s** (including
**0.14s** of warm compilation). The final serialized all-target checkpoint is
**177/177** in **125.72s real**, as reported above. Counts are checkpoints; the
commands and fail-closed gates are
the durable contract.

## How to read our claims

We try to be kind by being exact.

**"FREE"** means: merging provably preserves this promise, so coordination is
never required *for that promise*. It does not mean an operation can't break it
locally — validate your inputs — and it doesn't price metadata growth.

**Refutations are concrete states**, not intuitions. **Premises stay premises**:
where a guarantee needs a hash not to collide or a signature not to forge, that
is stated as an assumption and never absorbed into a theorem.

**Boundaries get decomposed, not just declared.** "That's outside our model" is
a stopping condition dressed as honesty, so every boundary here is split into
the part that is irreducibly an assumption and the part that is simply work
nobody has done yet — with the next step named.

And when we get something wrong, the correction lives where the claim lived.
Several parts of this repository exist because outside reviewers took the work
seriously enough to refute pieces of it; those retractions are in the documents,
not buried in the history.

## Papers, and thanks

The full annotated bibliography is [here](docs/BIBLIOGRAPHY.md). The short list:
Bailis et al. (the judgement this is built on), Shapiro et al. (CRDTs),
Gomes–Kleppmann et al. (mechanized convergence), Kleppmann et al. (move
operations, interleaving anomalies, undo/redo), Almeida–Shoker–Baquero (deltas),
Whittaker–Hellerstein (segmented confluence), Hellerstein–Alvaro (CALM),
Kuper–Newton (LVars), Omar et al. (typed holes), Ramesh et al. (Sal), the LoRe
authors, and the Power–Koutris–Hellerstein free-termination line.

Thanks to the weaver whose question started this, and to
[universal-weave](https://github.com/transkatgirl/universal-weave) for being the
kind of library worth building companions for. Made by ember + Claude, with the
[dregg](https://github.com/emberian/dregg) metatheory in the background, and
with review from two other AI systems who made it measurably better by telling
us where we were wrong.

The name is spelled lean-uwueave. That was never a typo.

License: Unlicense.
