# TRUST — three ledgers

*What this repository asks you to believe, sorted by what kind of belief it is.*

This file exists because an external reviewer — **codex** — read our claim that
three boundaries were *terminal* (signature unforgeability, the C backend TCB,
Bailis's full generality) and demolished it, along with a habit it had grown
out of. His two findings, restated so they can be checked against this file:

1. **`#audit_floor` establishes logical hygiene, not semantic adequacy.** The
   gate proves that no proof in this tree leans on anything outside Lean's own
   axiom floor. It cannot prove that any of those theorems is *about* the thing
   we say it is about.
2. **Calling everything "premises" hides where more work would reduce trust.**
   One list mixes a hardness assumption nobody can discharge with an
   engineering obligation someone could close next month. Lumping them makes
   the second look like the first — which is exactly how a boundary stops
   being worked on.

So: three ledgers, not one list. Every row says what it rests on and whether
it is **irreducibly a premise** or a **transmutable obligation with a named
next step**.

`Uwueave/Gated.lean`'s honesty section already labels its own items
⟨TERMINAL⟩ / ⟨UNDONE⟩ — that section is the seed of this file and was more
careful than the briefing document that summarised it: it wrote
"⟨TERMINAL, **at this layer**⟩" where `FORCODEX.md` wrote "terminal". The
qualifier was the whole argument, and it got dropped in transit.

---

## How to read a row

**PREMISE** — no work inside this repository removes it. Either it is a
mathematical assumption the discipline itself rests on (kernel soundness) or a
computational hardness assumption the world has not settled (collision
resistance). A premise is not a defect; an *undecomposed* premise is.

**OBLIGATION** — currently trusted, but closable by identified work. The row
must name the work. "Large" is not a disqualifier; "unnamed" is.

**NARROWABLE** — the third category, which the two-way split hides. The gap
between a theorem's statement and the intent it was written to capture is not
assumed (nothing is asserted) and not closable (there is no formal object on
the far side to prove anything about). It is *narrowed* — by refutable
witnesses, executable differentials, and adversarial readers — and it never
reaches zero. Treating it as a premise makes it sound settled; treating it as
an obligation makes it sound schedulable. It is neither.

Facts below were read out of the tree on **2026-08-11**, mid-wave. Counts move;
mechanisms are what to check.

---

## Ledger 1 — the logical TCB

*What must hold for "the proof went through" to mean anything.*

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Lean's kernel | The soundness of Lean 4's type theory and of the kernel that implements it. Every theorem here is a kernel-accepted term and nothing else. | **PREMISE**, with a transmutable edge | Independent checking. **Lean4Lean** (Carneiro) is a formalization of Lean's metatheory and an independent checker written in Lean — and its development *found a soundness bug in the Lean 4 kernel*, which is the whole argument for doing it. Re-checking this tree under an independent checker is a real, bounded task; it does not remove the premise, it stops one implementation from being its sole custodian. |
| The axiom floor `{propext, Classical.choice, Quot.sound}` | Classical logic with quotients. This is what "a Lean proof" already means; the repo adds nothing to it. | **PREMISE** | None, and none is wanted. Note what the floor is *for*: the audit exists for what it excludes — `sorryAx` (a hole that would otherwise ship as a warning), custom axioms, and `native_decide`, which trusts the compiled evaluator and therefore imports Ledger 2 into Ledger 1. On the pinned Lean 4.30 toolchain the latter dependency is generated under `_native.native_decide.ax_…`, and the executable canary pins that exact family. |
| `#audit_floor` itself | An unverified `elab` metaprogram whose one policy implementation now lives in `Uwueave/TrustFloor.lean`. `Audit` applies it to every constant under `Uwueave`; the Preoscript elaborator calls the same `offFloor` helper before publishing generated proof facets; downstream consumers can use the nonvacuous `#audit_floor_prefix Namespace`. It is not a theorem and still audits Lean from inside Lean. | **OBLIGATION** | The whole-tree command retains its 300-constant vacuity tripwire and currently audits **25,747 constants**. `scripts/trust-canaries.sh` runs seven subprocess fixtures for the exact floor, header parsing, vacuity, custom axiom, `sorry`, and `native_decide`; checked-language suites repeat contaminants at generated boundaries. Wave 30 adds the context-projection refusal/floor matrix. These canaries prove the gates can go red but deliberately share `collectAxioms`, so the remaining step is still a second, differently-shaped checker. |
| Statement ⟷ intended protocol | Reading. Nothing else. `necessity` is a theorem; that it says what Bailis says is a judgement made by humans and models looking at both. | **NARROWABLE** | The house bar already in use: a model must be **satisfiable and refutable**, never vacuous in either direction — `Necessity.lean` carries both (`gset_true_is_cfcs` on one side, `atMostOneBit_necessity` on the other). Extend that bar from models to *statements*: every keystone should have a witness that makes it fire and a neighbouring statement that a witness refutes. |
| Model completeness — a missing operation or failure mode | Per-module "what this does NOT capture" sections, written by the author of the module. | **NARROWABLE**, per row **OBLIGATION** | These lists are good and they are self-reported. `Necessity.lean` names five gaps (multi-hop schedules, liveness, Byzantine replicas, op-based causal broadcast, interactive transactions); `Liveness.lean` names four; `Era.lean` names the hash DAG, causal-closure computation, backdating detection, arbiter lists and timestamps. The transmutable half is that each named gap is a work item with a paper behind it. The narrowable half is the gap nobody listed. |
| Reachability ⟷ the shipping API | `CausalReach.lean` models causal cuts and tags a clash Live or LatticeOnly. `docs/MAP.md`'s reachability axis is derived **only from module docstrings** and refuses to guess — which is honest, and is a docstring-level judgement, not a machine-checked one. | **OBLIGATION** | `KernelCFCS.lean` is the pattern: embed the *shipping* op alphabet into the model (`Necessity.Impl` over `GSet Exec.Op`) so reachability is asked of the ops the kernel actually replays. It exists for the move kernel only. Doing the same for `SeqKernel` and `EraKernel`, and then for the Rust crate's public op vocabulary, converts a docstring axis into a theorem axis. |
| Serialized bytes ⟷ the proved abstract state | Partly proved, and the proved part is real: `replay` is *definitionally* decode → `absReplay` → encode; `replay_encodeRequest`, `decodeBase_encodeRequest`, `decodeOps_encodeRequest`, `decodeGrants_encodeRequest`, and `decodeRevs_encodeRequest` close the input codec against the canonical encoder; `decode_encode_id` and `getWord_encodeView` close the output codec at word level. Separately, budget-empty `Preo.ProjectionV1` preserves its published schema and refuses a nonempty budget list. Budget-bearing `Preo.ProjectionV2.validate` checks V1's structural/resource conditions plus exact action histograms, obligation coverage, plan/session references, canonical five-currency profiles, and witnessed budget limits before the private `ValidatedProjectionV2` reaches deterministic `renderRustSource`. V3 adds distinct schema/query/result/program/certificate/world identities, strictly increasing registries, stable-ID and hole-depth ceilings, and proof-indexed builders. `CheckedResult` consumes the exact certificate-gated report, and disclosure requires its exact selected branch. `Quickstart` assembles one full V3 value only through those builders, proves bounded validation and canonical decode/reopen, and proves its stack-safe executable frame byte-identical to `ArtifactV3Durable.projectionBytes`. `ArtifactV3Surface` exposes the same route transactionally but accepts the report only through `ObservedBoundResult`: authenticity, independent running reach, authored reach, future, certificate, and world index remain in its type. It constructs result/effect/disclosure/certificate rows rather than accepting authored twins. `Preo.ArtifactEmit` separately remains the explicit import-pure V2 selector. | **OBLIGATION**, partly paid | ⚠ The abstract-to-concrete *symbol* bridge (`Move.lean` §3, `absReplay_matches_miniInterp`) holds on the **2-node universe only** — its own header says so. Generalizing that bridge past two nodes, and giving the seq and era kernels the codec closure the move kernel has, is the named work. Projection V2/V3 remains **data only**: no theorem says arbitrary rendered Rust compiles, denotes the source semantics, reconstructs a proof, authorizes an operation, or issues a permit. `ObservedBoundResult` retains a caller-supplied `ObservationBoundary.Authentic` proof; it does not observe or authenticate a deployment. The emitters prove byte identity inside Lean and are tested through the host; they do not prove stdout, path, or filesystem semantics. The V2/V3 inspector is explicitly diagnostic-only and cannot promote decoded rows back into checked evidence. |
| Docstring ⟷ theorem | Authorial discipline plus a house rule ("docstrings must match statements exactly"). No mechanism enforces it. | **NARROWABLE**, with a mechanism seed | There *is* one partial mechanism, and it should grow: `rust/src/bin/uwueave-check.rs` resolves its theorem citations through real namespace structure and checks verdict **polarity** against the Lean statements, so the CLI cannot advertise a verdict the theorem contradicts. That covers citations, not prose. A docstring is an unchecked claim in the same TCB as everything else here. |

**Eight rows: two PREMISE, three OBLIGATION, three NARROWABLE.**

The automation boundary now fails more honestly without changing this ledger's
row count. `Tactics.Core.RouteOutcome` distinguishes `inapplicable`,
`resourceRefused`, and `internalError`; only genuine inapplicability permits the
next route. Automatic exhaustive classification inspects at most 64 states and
4,096 ordered pairs before a typed refusal, while the explicit value-level
`classifyFinite` remains total. The split Preoscript elaborator applies the same
distinction internally: optional route probes may fail as data, mandatory
generated declarations fail loudly, and each surface command runs in an
environment transaction. The executable automation suite checks no verdict,
no pool, explicit and automatic resource caps, wrong goals, internal errors,
declaration presence/absence, and whole-command rollback followed by successful
reuse of the identical name. These are controls on unverified elaborators:
every successful route still has to emit a kernel-checked term, and no cap,
transaction, or diagnostic makes a metaprogram a theorem.

---

## Ledger 2 — the execution TCB

*What must hold for the shipping artifact to behave like the theorems.*

The canonical [Ledger 2 machine manifest](trust/ledger2-v1.json) is checked
against the live debt/receipt lineage, the RuntimeInit/export/shim/FFI surface,
the lexical Rust `unsafe` inventory, and release-facing documentation. Native
runs add a target-specific observation containing exact tool, runtime, closure,
member, and archive identities. CI retains it only after the frozen all-target
suite and a post-suite closure probe succeed; the record describes the build,
not test success. The gate preserves this ledger; it does not
pay any premise or semantic obligation.

This is the ledger codex most wanted broken up, and he is right: "the C backend"
is not one boundary, it is at least five, and only some of them are hard. None
of them is terminal. **Verified compilation is an existence proof, not a
hope** — CompCert is a C compiler with a machine-checked proof of semantic
preservation from source to assembly, and CakeML is a functional language whose
compiler is verified down to machine code. Both are the shape of the thing this
row needs; neither is currently in the pipeline below.

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Lean's C code generator (U-0161) | Lake emits C and native objects from the Lean IR for the exact `Uwueave.RuntimeInit` import closure, including the nine current `@[export]` entry points: request encoding, move replay, request-canonicality audit, sequence replay, ERA resolution, artifact-v2 validation, legacy bounded UWV4 syntax classification, context-bound UWV4 admission projection, and admission-trace checking. Unverified, and the semantic distance from the Lean definitions to those objects is the largest single jump in this repo. One narrower substitution boundary **is paid**: `Exec`'s `getWord`/`pushWord`/`gatedReplayFull`, `SeqKernel`'s `childrenK`/`emitK`, and `EraKernel`'s `responseWords` optimizations are installed by proved `@[csimp]` equalities. `Exec.encodeRequestKernel_eq` also proves that the typed export adapter delegates to `encodeRequest`; neither fact verifies later IR → C lowering. There is no unproved `implemented_by` replacement in the Lean tree. | **OBLIGATION** | Three real routes, in ascending cost: **translation validation** per emitted function (check the C against the IR for the handful of exported kernels, not the whole tree); a **proved exporter subset** (the kernels use a narrow fragment — arrays, `Nat`/`UInt64`, structures, no closures over the FFI boundary); and full verified compilation, which CakeML shows is achievable for a functional source language. ⚠ CompCert does **not** cover this row — it starts at C. |
| The C compiler, archiver, and linker (U-0162) | Lake owns native compilation of every object in the runtime closure; `cc::Build` compiles exactly `shim.c` at `opt_level(2)` and archives that object with Lake's byte-snapshotted objects. Both use the selected host toolchain, and the build refuses cross-compilation or a target other than native `x86_64-unknown-linux-gnu` / `aarch64-apple-darwin`. Every evidence run records the selected compiler command, archiver and explicitly selected Cargo linker with executable hashes and version output. | **PREMISE** for current native evidence | Retain their semantic correctness as external. An identity record is not compiler validation. A binary-distribution correctness claim must allocate a new verified-compilation obligation; CompCert is one possible route for its supported C subset. |
| The Lean runtime (`libleanshared`, U-0163) | Reference counting, the allocator, `lean_alloc_sarray`, `lean_dec_ref`, and module initialization. Linked as a dylib from the toolchain, with an rpath baked in by `build.rs`. The initializer choice is closed mechanically: the data-free `RuntimeInit` directly imports every exported-kernel root, and the shim calls only its generated initializer. Each native observation records the authoritative `lean-toolchain` name, selected Lean executable, and exact `libleanshared` path, bytes, and digest. The ownership contracts are written at the touched Rust and C calls, but the runtime does not check them. | **PREMISE** for current native evidence | Retain allocation, reference-counting, initialization, and exported-call semantics as external. An identity record is not runtime verification. Manual shim construction and lifecycle remain U-0164 rather than being hidden in this premise. |
| `shim.c` (U-0164) | Eleven exported shim functions including init/free, the legacy UWV4 decoder, context-bound projection, and admission-trace checker. The exact reviewed source bytes are pinned. A Clang JSON-AST gate checks the complete function set, call/consumption/reference-release paths, allocation and copy helpers, overflow guards, lane strides, indexes, and typed op/grant field order. Mutation canaries delete a `lean_dec_ref`, alter a bound, and swap a construction lane. One exact native unit crosses every shim endpoint with nonempty typed construction and output ownership; CI rebuilds and runs it under UndefinedBehaviorSanitizer on both supported platforms. The shim still does **not** decide FORMAT-v3/UWV4 bytes, verify a signature, or establish the external Lean runtime semantics. | **PAID** as a mechanically locked adapter | Preserve the exact-source/AST gate, mutation negatives, and two-platform sanitizer run. U-0163 remains the premise for what `lean_alloc_*`, consumption, and `lean_dec_ref` mean; this row checks that the reviewed adapter uses them in the declared pattern. |
| The ABI and the FFI boundary (U-0165) | `rust/abi/uwueave-abi-v1.json` is the one canonical declaration/layout description. Its gate checks all Rust and C declarations and calling signatures, both `repr(C)` record sizes/alignments/field offsets, the exact Ledger-2 export/shim mapping, and the compile-time Rust/C layout assertions. On Ubuntu x86-64 and macOS arm64 it also parses every generated Lean C prototype/definition and extracts the observed shim archive member to enforce its exact defined-global symbol allowlist. Ten source/mutation canaries cover layout, C/Rust signatures, Lean arity, mapping, symbols, construction, bounds, and ownership release. | **PAID** as a declaration/layout contract | Keep the descriptor, source gate, native observations, and mismatch canaries synchronized. This establishes cross-language ABI agreement on the supported matrix; it does not turn Lean lowering, compilation/linking, or `libleanshared` behavior into proved semantics. |
| Rust `unsafe` (U-0166) | All **18 unsafe blocks** and the sole `unsafe fn`, `take_shim_bytes`, are in `rust/src/ffi.rs`; the kernel benchmark uses safe library adapters. Package-wide compiler lints deny unsafe syntax in every Cargo target, the library grants its sole narrow exception to `ffi.rs`, and `unsafe_op_in_unsafe_fn` denies implicit unsafe operations. An independent `syn` gate inventories build, library, binary, example, benchmark, and test ASTs exactly. With the mechanically checked shim and canonical ABI controls above, no successor dependency remains in this source boundary. | **PAID** | Preserve the package lints, narrow module exception, complete AST roots/counts, safe benchmark adapters, and U-0164/U-0165 gates. Miri still cannot follow this FFI, so the native sanitizer/ABI evidence must remain. |
| Lean-owned request encoding | Rust now supplies typed first-parent, operation, grant, and revocation lanes to `uwueave_encode_request`; the exported Lean adapter reconstructs the values and calls `Exec.encodeRequest`. `encodeRequestKernel_eq` states that delegation, and `decodeBase_encodeRequest`, `decodeOps_encodeRequest`, `decodeGrants_encodeRequest`, `decodeRevs_encodeRequest`, and `replay_encodeRequest` close the canonical input codec. Rust no longer owns a FORMAT-v3 byte encoder. The old `requestCanonicalKernel` endpoint remains only as a compatibility/test audit. | **PAID** at the wire-decision boundary | Preserve the single encoder. Rust still chooses the typed node indices and operations it asks Lean to encode; the typed ABI, shim, runtime, and codegen remain the separate obligations above. A second byte-level request encoder in Rust would reopen this row. |
| Storage and index glue (U-0167) | `causal.rs`, `movelog.rs`, `seq.rs`, `era.rs`, `weave.rs`, plus `persistence/{record,artifact,authenticated,document,history}.rs` — `BTreeMap`/`BTreeSet` state, derived indexes, merge plumbing, and five physical journal domains. Property and persistence tests exercise the real crate and kernel across framing, retry, corruption, torn tails, typed reconstruction, checkpoints, causal prefixes, durable pending arrivals, authenticated-record indexing, pin-relative rollback, and collision refusals. | **OBLIGATION** | The tests are good tests and zero formal evidence, which `lib.rs` already says. Keep every semantic decision in Lean where possible, and refine the remaining host codecs, indexes, replay adapters, filesystem operations, and failure observations instead of treating their tests as theorems. The house rule remains "no Rust twin of a decision procedure." |
| Cargo/Lean build freshness and native closure | **Paid as a fail-closed control.** The data-free `Uwueave.RuntimeInit` is the single closure/initializer root and directly imports every exported-kernel module. `build.rs` first requires a full `lake build`, reads Lake's exact RuntimeInit setup metadata, validates its closed schema and required kernels, queries one exact Lake-owned native object for every transitive member, snapshots the bytes, stages stable copies, and asks `cc` to archive only those objects plus the one compiled shim. It then verifies exact archive membership and every extracted Lake-member byte. A final `lake --no-build build` plus no-build path queries recheck the root, setup, closure and objects; before/after snapshots cover every Lean source and the root, Lake/toolchain manifests, Ledger 2 manifest, shim, build script, Cargo manifest and lockfile. Cargo rerun directives cover the same control inputs. Exact closure membership, byte totals, member hashes, and the archive digest are recorded and verified dynamically per build rather than treated as stable source-level fingerprints. | **PAID** | Preserve `RuntimeInit` as data-free and make every native kernel a direct import there. Keep Lake setup metadata as the sole discovery authority, keep the input and byte-stability postconditions synchronized with new build controls, and retain the adversarial validator tests. This closes stale/mixed/extra/missing native-object selection and initializer drift; it does **not** prove Lean code generation, native compilation/linking, the shim, ABI, runtime behavior, or filesystem semantics. |
| Filesystem and crash behavior (U-0168) | `sync_*`, locking, paths, filesystem semantics, power loss, and direct `ArtifactEmit` partial writes are deployment observations. In particular, a direct partial logical frame must satisfy `Durable.TornFrame`; the outer Rust journal instead withholds incomplete outer bodies. | **PREMISE** | Supported deployments must state the conditions yielding complete logical frames plus at most one torn final frame. Tests are observations, not a stable-media or power-loss theorem. |
| v0.2 distribution and native matrix (U-0169) | Version 0.2 is source-only with publishing disabled. Native evidence targets Ubuntu 24.04 x86-64 and macOS 15 arm64. | **SCOPE** | No C-ABI, binary, relocatability, or artifact-upload promise is made. Widening the matrix allocates new obligations. |
| Persistence and durability (U-0170) | The crate ships concrete pure-Rust host journals, but not a filesystem theorem. Artifact, legacy document, causal history, and durable-arrival formats retain their stated boundaries. `RawJournal` wraps inner artifact frames in checksummed `UWARJ` outer records; a torn outer record is withheld rather than passed to logical recovery as a nonempty `Durable.TornFrame`. The separate `AuthenticatedMoveJournal` (`UWAMV401`) stores only crate-private checked kind-3 records with exact request/signing/signature bytes, context and policy versions, the exact execution-base binding, nonce/operation scopes, stable/projection/concrete move lanes, prefix-relative kernel observation, and prior chain head. Nonce/operation indexes update only after append; a domain-separated BLAKE3 body chain binds the ordered record including that execution binding, so the externally pinned head commits to it. | **OBLIGATION**, with concrete physical/authenticated-record/composition rungs **paid** | Mechanically check that scan and append expose exact complete outer bodies plus at most one syntactically valid final outer-record prefix, withhold every incomplete body, and pass accepted inner bytes satisfying `Durable.recover_encodeJournal`. Keep direct emitter partial-write behavior under U-0168. The wider host composition, policy lifecycles, open/write/sync failures, rollback, and filesystem refinement remain open. |

**Twelve semantic rows: three PREMISE, three OBLIGATION, one SCOPE, and five PAID
boundaries.** U-0160 is a separate registry-integrity umbrella, not a thirteenth
execution boundary and not semantic closure. Its implemented receipt records
that the machine-readable gate preserves this exact mapping and rejects stale
ledger claims; the successor rows retain their own states. Canonical request
encoding and build freshness are closed controls.
They do not prove code generation, the external toolchain/runtime premises,
storage glue, or canonical host durability. The shim, ABI, and Rust unsafe rows
are closed controls over those still-explicit external premises.

The persistence row now has stronger executable bridges without changing its
status. The explicit `uwueave-preo-artifact` command emits two real Lean-owned
V2 artifacts; the Rust integration test admits them, appends under `SyncData`,
closes and reopens, compares exact bytes and BLAKE3 observations, and refuses
mutation, truncation, and a wrong version. The checked V3 Quickstart separately
emits a 71,011-byte frame, proves its stack-safe execution bytes equal the
canonical codec, writes and reopens those bytes, and inspects both one frame and
a two-frame logical journal through bounded Lean V2/V3 inspection. The pure
library modules are root/audit covered; `ArtifactEmitMain` and
`ArtifactInspectionMain` remain separately compiled CLI boundaries so their two
root-level `main` declarations never enter one proof aggregate. The final
serialized `CARGO_BUILD_JOBS=1 cargo test --all-targets -- --test-threads=1` gate passed
**177/177 Rust tests** in 125.72s real (10.49s compilation; 35.60s user;
37.86s sys; 1,274,494,976 B maximum RSS). The authenticated-runtime target was
10 tests / 85.31s. That is valuable
implementation evidence, not an atomic-write, stable-media, path-safety, or
filesystem-crash theorem.

The checked-language acceptance boundary is also executable without changing
the ledger totals. `scripts/preo-v3-acceptance-canaries.sh` runs three green
fixtures and fourteen standalone red subprocess fixtures; one guarded refusal
inside the rollback fixture makes fifteen red command cases. The matrix covers
exact observed export, a bare certified report, a structural lookalike, forged
state, out-of-running reach, wrong projection/future/world/certificate/plan,
both command-work and validator-resource ceilings, custom axiom, `sorryAx`,
Lean-4.30 `native_decide`, whole-prefix absence, and same-name reuse. These are
elaboration/transaction tests, not proof that a host observation is authentic.
They also do not erase the open performance result: the serialized N=16
`preo_export_v3` corpus measures **6.706 MiB/item**, above the 4 MiB/item cap.

`scripts/wave27-acceptance-canaries.sh` adds three positive and eighteen
standalone negative Lean fixtures around authenticated frontier/context and
the V4 sidecar, then delegates the unchanged generated-command floor,
resource, and rollback cases to the V3 suite. The new negatives cover forged
signature, source and roster; ordinary/stale/incomplete frontier claims;
unissued position, wrong causal origin, stale version and consumed capability;
wrong V4 schema/origin/roster/version/signature/capability/resource; and the
attempt to use a decoded neutral `Manifest` as private `CheckedManifest`.
Focused durable-arrival tests run in Rust because filesystem persistence is not
a Lean command boundary.

`scripts/wave28-era-certificate-canaries.sh` adds one positive and five
standalone-red subprocess fixtures for the authenticated ERA bridge. The
positive pins the exact `Verification`, genuine issuance, complete
announcement, settled delivery certificate, record-free exact-key reusable
certificate, and role seal. The reds refuse the wrong progress domain,
signature-accepted but unissued input, an incomplete announcement codec, an
unsettled frontier, and a different reusable key. This verifies dependency
shape and refusal boundaries; it does not implement signatures, observe a
network, or extend the certificate across future announcements.

`scripts/wave29-finite-canaries.sh` adds two positive and eight standalone-red
fixtures. The repair positive retains the least authored ID, dependent repair,
generated row, complete `Price`, and exact-list exhaustive refusal; reds reject
a wrong least ID, erased price, inverted refusal, oversize universe, and
noncanonical order. The history positive explicitly supplies a six-version
`FiniteGrowth`, causal and maximally reversed successful `DeliveredGrowth`
values, settlement, event-set/view convergence, and exact retry; reds exercise
stable-ID collision, self-parent, and duplicate-parent refusal. This is
evidence about the finite interfaces, not proof of global search completeness,
network delivery, storage, authentication, or host refinement.

---

## Ledger 3 — environment and model premises

*What must hold about the world for the theorems to bind to a deployment.*

### 3a. Delivery, identity, membership

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Fair delivery | `Liveness.lean`'s `FairOn`: a **finite covering** — every participant's received set is membership-equivalent to the issued set. Under it, every replica reaches `joinAll`; under an unfair schedule there is a constructive starvation witness. | **PREMISE** at the model boundary, with transmutable edges | The model is deliberately not a network. Its own non-capture list names the edges: loss as a probability, RTT, topology dynamics, "eventually" as a temporal modality over infinite traces, and multi-hop epidemic diameter for `n > 2` under pull-only schedules. Each is a theorem someone could write; the coinductive-stream version of fairness is the standard next rung. |
| Identity and authenticity | `Authenticity.lean` names an abstract `SignatureScheme`, genuine issuance, and the trace-relative EUF-style handoff; the authenticated context/frontier and ERA certificate layers preserve their independent semantic premises. `RuntimeAuthV4` retains legacy kind-1 canonical syntax. `RuntimeAuthV4Kernel` gives kind 3 a signed opaque context commitment, exact decode/shape/width/projection, and a distinct kind-4 response. The host has a pluggable verifier and one context/document/genesis/issuer/epoch-scoped keyed-BLAKE3 symmetric-MAC profile. Its `VerificationAcceptance` retains exact scope/signing/signature byte vectors plus unkeyed hashes, but its public constructor performs no verification; it is not a public-key signature or EUF-CMA result. `AuthenticatedRuntime` fixes document/genesis/context/execution scope and orders that evidence with persistent nonce/operation classification, pinned context, resolution, authority, membership, concrete Lean execution, authenticated append and externally pinned historical revalidation. The checked sidecar remains a separate one-way neutral projection under `⟨4,162⟩`. | **OBLIGATION** — the abstract handoffs, context-bound codec/projection, concrete MAC/composition rung, and one-way sidecar are paid only at their stated boundaries; see 3b | Supply a security argument or verified provider and durable authenticated key/history/roster representation; connect scoped verifier acceptance and the ordered host outcome to abstract issuance/authenticity. Verify the deployment-owned context/resolver/authority/membership traits and external-pin lifecycle, and prove host-to-Lean and filesystem refinements. Storage observations remain premises/tests, not proofs. |
| Membership closure | `Era.lean` §8 carries the invited/member/left lifecycle beside §3's role codes. ⚠ Its own docstring records that **§3's promote does not check membership** — an invitation alone does not gate it — so the lifecycle is a second, parallel authorisation predicate rather than a strengthening of the first. `GatedEra.lean` derives membership from causal closure with no signatures and no backdating detection. | **OBLIGATION** | Compose the two authorisation predicates instead of running them in parallel, and prove the composite is what the kernel decides — the same move `Gated.lean` §5 already made once (`kernel_gate_agrees_gatedOps`), which is why this is a known-shaped task rather than an open one. |
| Trusted announcements (Era's arbiter) | ERA's own protocol design: a distinguished peer periodically announces epoch cuts that **order** events without naming winners. Nobody coordinates; replicas never wait; the price is trust in one announcement stream plus rollback of the unfinalised suffix. | **PREMISE** of the protocol — and a smaller one than it looks | The equivocation case is already handled, not assumed away: an event named by several cuts takes the least epoch, so a **concurrently-announcing arbiter degrades to deterministic re-ordering, never divergence** (`resolve_same_sets` holds with no honesty hypothesis). What remains is named: prefix stability under cut growth is *not* claimed, and backdating detection, arbiter lists and transparency are out of scope here — the paper answers them with signatures and fraud proofs, which is Ledger 3b's work, not a new premise. |
| Clock uniqueness and tiebreaks | The kernel's total order is `(lamport, replica, child, dest, cite)` with the request index breaking only fully identical duplicate records, so determinism does **not** depend on replica ids being distinct. `Catalog.lean` §3 records that LWW's *value* tiebreak is load-bearing: without it two writes at the same timestamp make merge non-commutative. | **OBLIGATION**, and narrower than usually stated | Determinism is fine. What breaks under duplicated replica ids is **attribution**: `movelog.rs` identifies one user with one replica id, so two users sharing an id are indistinguishable to every theorem here. That is the identity row again, and it is where the fix belongs — not in the sort. |
| Crash behaviour and recovery | `Durable.lean` proves recovery for canonical framed journals: exact journals and complete appends recover, a torn final frame is a proper prefix, crash-prefix recovery drops it, and recovered record prefixes are monotone. `Preo.ArtifactDurable.Examples.two_frames_then_torn_third` specializes that logical theorem to format-v2 `ArtifactEncoding`; `Preo.ArtifactJournalKernel.scan_encodeJournal`, `scan_append`, `scan_torn_final`, and `scan_stops_at_first_refusal` add exact logical boundaries and first-refusal diagnostics. The Rust journals now supply a concrete, checksummed standard-file implementation with explicit `TornTailPolicy` and `SyncPolicy`: complete corrupt records refuse; a final incomplete record is truncatable only when every present deterministic prefix byte is compatible; exact-sequence retry repeats synchronization; and the 1 MiB artifact ceiling precedes Lean validation. `rust/tests/persistence.rs` exercises all strict truncations, checksum-prefix corruption, wrong tags/noncanonical frames, locks, bounds, retries, typed replay, and false checkpoints; `persistence::record::tests::idempotent_retry_repeats_sync_and_poisons_on_sync_failure` injects the retry-sync failure directly. These are host code and test evidence. `Durable.DeploymentAssumptions` remains uninhabited, and `PersistentRuntime.AtomicBatchObservation` remains uninstantiated. | **OBLIGATION**, with canonical bytes, logical recovery, and a concrete tested host rung **paid** | Establish an explicit refinement from the Rust scanners/codecs to the Lean logical records and from actual filesystem observations to the chosen crash model. Extend failure injection to short writes and open/parent-sync failures, and test real process/power interruption; specify supported filesystems/platforms; harden path and permission handling; bound whole-journal resources; and add authenticated anti-rollback state. No theorem grants filesystem append/rename atomicity, stable-media durability after `sync_*`, resistance to malicious checksum recomputation or clean-suffix deletion, or multi-record atomicity. |
| Byzantine peers | `Byzantine.lean` separates equivocation, forgery, and withholding. `fork_evidence_permanent` and `fork_evidence_iconfluent` make admitted fork evidence permanent under `Gossip`; `AuthenticatedAdmission.authenticIssuer_to_signatureAuthentic` now discharges `fork_evidence_attributes_author`'s `SignatureAuthentic` premise from an `AuthenticIssuer` hypothesis over accepted signed events. `AuthenticatedGatedOp.ofAuthenticIssuer` separately packages an accepted signed move with genuine issuance, holder binding, and the authorization gate, paying the abstract intersection that `unauthenticated_submission_can_pass_the_gate` showed was missing. `not_quiesced_iff_withheld` and `concrete_withholding` still characterize an independent delivery failure. Under `Settled`, grounded announcements, `IdAuthentic`, and issuance, `authentic_issuance_preserves_finality` proves ERA safety; its contrapositive and forged-id witness expose the remaining authenticity boundary. | **OBLIGATION**, with the safety decomposition and abstract authenticated-admission transports **paid** | Establish `AuthenticIssuer`, `IdAuthentic`, and grounded announcements from a concrete signed-byte admission implementation, including an actual EUF-CMA argument, then refine FORMAT v3/`Exec`/FFI and model adversarial transport or a BFT protocol. These theorems do not prove a cryptosystem, Byzantine consensus, censorship resistance, or liveness; withholding remains separate. |

### 3b. Cryptography — the row codex was most right about

The earlier claim was "signature unforgeability is terminal." The tree now
states the missing **logical handoff**, which is real progress and still not a
cryptographic security proof. `Authenticity.SignatureScheme` assumes only
correct verification of honestly generated signatures. `EUFStylePremise` is a
deterministic, trace-relative assertion that no accepted unissued record was
received; it is the conclusion that an external computational reduction must
supply, not an EUF-CMA game or theorem in disguise.

Unforgeability remains a named hardness assumption only after choosing a
concrete scheme, security parameter, adversary and query model. Everything
around that residue is engineering, and engineering is provable. **EverCrypt
is the existence proof**: a verified cryptographic provider whose
implementations carry machine-checked memory safety, functional correctness
against the spec, and secret independence. This repository does **not** claim
EUF-CMA for any concrete primitive.

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Scheme hardness (EUF-CMA) | A deployment must choose a concrete signature scheme and security model. The abstract `SignatureScheme.correct` field proves honest-operation correctness only; the tree has no security parameter, probabilistic adversary, signing-oracle game, or advantage bound. | **PREMISE** at deployment, **not proved here** | Supply an actual computational reduction for the chosen primitive showing that reachable deployment traces satisfy `EUFStylePremise`. Naming that deterministic conclusion does not establish EUF-CMA. |
| The unforgeability handoff | `authenticIssuer_iff_no_received_forgery` equates issuer authenticity with the absence of a received `ForgeryWitness`; `authenticity_violation_extracts_forgery` constructs that witness from any violation; `eufStyle_implies_authenticIssuer` transports the externally supplied premise. The witness includes the exact record, registered public key, successful verification, non-revocation proof, and non-issuance proof. | **PAID** at the abstract model boundary | Preserve the constructive extractor. The computational reduction remains the premise above, while concrete admission and signed-byte refinement remain obligations in their respective rows. |
| Protocol use and domain separation | `grant_event_domain_separated` and `signingMessage_grant_ne_event` separate the object domains; `signingMessage_grant_injective` and `signingMessage_event_injective` bind issuer, key epoch, and every modeled payload field. The carrier is still `List Nat`, not deployed bytes, and the crate's blake3 content-addressing is not refined to these messages. | **OBLIGATION**, with field-level separation **paid** | Define one canonical signed-byte codec, prove it refines `signingMessage` and preserves the separation/injectivity results, then bind the deployed blake3 id encoding to `UniqueAnchor` / `UniqueGrant`. |
| Key rotation and revocation | `accepted_antitone_revocation` proves that growing key revocations can only remove accepted records; `revokeKey_grows` and `revokeKey_rejects` close the one-key update; `rotation_rejects_older_record` proves an old epoch cannot pass the current-key policy after rotation. Historical verification is intentionally separate. | **OBLIGATION**, with the policy model **paid** | Connect the abstract keyring, current epochs, issuance log and grow-only revocations to deployed key storage, signed rotation records, admission, and transport. The model does not provide those mechanisms or prove their durability. |
| Implementation correctness, constant time, parsing | The crate now has a pluggable trusted-host verifier plus one concrete keyed-BLAKE3 **symmetric MAC** profile. Its registry lookup is scoped by context commitment, document, genesis, issuer, and key epoch; the 32-byte comparison accumulates all content differences after a public length check. Lean owns the kind-3 request parser and exact signing bytes. `VerificationAcceptance` retains exact context/document/genesis/signing/signature vectors plus unkeyed hashes and scalar scope, and admission compares the exact values. None of this is a public-key signature, verified cryptographic implementation, EUF-CMA proof, secret-independence theorem, durable key lifecycle, or machine-checked constant-time result; `blake3` remains trusted. The public acceptance constructor exists for external verifier implementations and itself performs no verification. | **OBLIGATION**, with a concrete tested host rung | This is the EverCrypt row: implementation correctness, memory safety and secret independence are *proved* properties in shipping code today. Replace or verify the concrete provider and key storage, then connect its scoped acceptance to the abstract handoff. Keep the single Lean-owned request parser; the host kind-4 response parser must not become a second UWV4 parser. |
| Hash collision resistance | The best-decomposed cryptographic row in the repo. No `InjectiveHash` typeclass exists, deliberately: finite hashes are not injective. The boundary is `UniqueAnchor` / `UniqueGrant` — "this state exhibits no collision" — and each has an extractor turning a violation into a constructive collision witness. `causal.rs` refuses a same-id-different-bytes encounter loudly (`MergeError::IdCollision`) rather than deduplicating silently; `Sequence.lean` correctly names blake3 as the crate's deployed hash. | **PREMISE** (collision resistance) with the abstract handoff **proved** | Bind the model ids and extractor witnesses to the exact deployed blake3 input encoding. Until then the premise applies to the abstract id relation, not automatically to the crate's bytes. |

### 3c. Bailis's generality

`Necessity.lean` proves both directions for **one execution substrate**:
join-semilattice replicas, atomic local `tryApply` seeing only local state,
convergence as `⊔`, safety as global `I`-validity — with satisfiable and
refutable witnesses on both sides so the model is not vacuous either way. It is
a real model, and it is one model.

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| The judgement, for this substrate | `necessity` + `iconfluent_implies_cfcs`, over `Confluence.lean`'s `IConfluent`, not a private redefinition. | Proved — this row is the asset, not the debt | — |
| Richer transaction histories | The model's ops are atomic local transformers; Bailis's interactive multi-round transactions with mid-transaction reads of remote state are named as out of scope. | **OBLIGATION** | Theorem work with a known target — the paper's own model is the specification. |
| Failures and process assignment | Not modelled: no crashes, no process-to-replica assignment, no partial failure inside a run. | **OBLIGATION** | Same. |
| Arbitrary outcome refinement | The model's outcome is a lattice state and its order is the merge's order. Bailis-style safety is `I`-validity of that state. | **OBLIGATION**, and the ambitious one | **Complete CALM** (Hellerstein, arXiv:2602.09435; PDF in `~/paperbin/uweave/`) is the broader semantic target: a specification maps execution histories to outcome sets under a *declared refinement order*, and admits a coordination-free implementation **iff** its outcomes are monotone. It explicitly recovers CALM, CRDTs, HATs and **I-confluence** as instances. So the transmutation is not "prove more about our lattice" — it is to restate the judgement over specifications and recover `IConfluent` as the instance it already is. That is the largest single item on this page and the one most worth doing. |

**Ledger 3 totals: seventeen rows across 3a/3b/3c — four PREMISE, eleven
OBLIGATION, one PAID model-boundary handoff, plus one proved asset row in 3c.**
There is no absent-component row now: durability has both logical and concrete
tested host rungs, and authentication has an abstract transport, a canonical
v4 foundation, and an ordered raw-only host admission/recovery boundary. Their
formal deployment, cryptographic, policy, and filesystem refinements remain
obligations.

---

## The corrected house rule

The old slogan was:

> *An honest label is a stopping condition and therefore a sin.*

It was **right about the danger and wrong about the remedy.** It taught us to
audit caveats for excuses, which worked — an earlier pass killed nine of them.
But it left only two verdicts, *theorem of the model* or *undone work in a
caveat's clothes*, and so it pushed every genuine boundary into the first bin
and then declared that bin closed. "Terminal" became a place to put things.
Three of them went in, and codex got all three back out.

The replacement:

> **Every boundary must be decomposed into its irreducible premise and its
> remaining transmutable obligations. A genuine model boundary is not a sin;
> leaving it undecomposed is.**

What this changes in practice:

- **"Terminal" is never a verdict about a whole boundary.** It is a verdict
  about a *residue*, and you only get to say it after naming what you removed.
  "Signature unforgeability is terminal" was three obligations and an unstated
  hypothesis wearing one word.
- **A row with no next step must say why there is none.** An empty next-step
  column is a claim, and claims are checked at source.
- **Cost is not a verdict.** "That would need a verified compiler" is an
  estimate. It is never a reason to leave the row undecomposed, and the
  existence proofs (CompCert, CakeML, EverCrypt, Lean4Lean) are all things
  someone already built while the estimate was being quoted.
- **Watch the qualifier drop in transit.** `Gated.lean` wrote
  "⟨TERMINAL, at this layer⟩"; the summary wrote "terminal". The summary is
  what got reviewed, and it was the summary that was wrong. When a boundary is
  restated somewhere more visible than its file, the qualifier is the part
  most likely to fall off — and the part that was load-bearing.

Everything above is a claim about this repository on 2026-08-11, checkable by
reading the files it cites. If a row is wrong, that is the good kind of wrong:
say so, and it moves a ledger.

*Written after codex's review, which is the reason this file has three ledgers
instead of one list.*
