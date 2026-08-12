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
| `#audit_floor` itself | An unverified `elab` metaprogram whose one policy implementation now lives in `Uwueave/TrustFloor.lean`. `Audit` applies it to every constant under `Uwueave`; the Preoscript elaborator calls the same `offFloor` helper before publishing generated proof facets; downstream consumers can use the nonvacuous `#audit_floor_prefix Namespace`. It is not a theorem and still audits Lean from inside Lean. | **OBLIGATION** | The whole-tree command retains its 300-constant vacuity tripwire (the current gate sees **24,921** constants), while `scripts/trust-canaries.sh` runs seven subprocess fixtures: the exact three-axiom floor, an indented/root-header regression, and hard failures for an empty namespace, custom axiom, `sorry`, and Lean-4.30 `native_decide`. The Preoscript automation and checked-V3 acceptance suites repeat those three forbidden-dependency cases at generated-declaration boundaries and check rollback/name reuse. The V3 positive prefix separately audits all **48** generated constants. Wave 27 adds independent prefix audits for its authenticated-frontier, world-context, and checked-V4 fixtures, while delegating the unchanged generated-command floor cases to the V3 suite. Those canaries prove that the gates can go red and that root-import coverage is parsed by Lean rather than a line scanner. They deliberately share the `collectAxioms` implementation, so the remaining step is still a *second, differently-shaped* checker — for example an out-of-band `#print axioms` sweep over ledger names. |
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

This is the ledger codex most wanted broken up, and he is right: "the C backend"
is not one boundary, it is at least five, and only some of them are hard. None
of them is terminal. **Verified compilation is an existence proof, not a
hope** — CompCert is a C compiler with a machine-checked proof of semantic
preservation from source to assembly, and CakeML is a functional language whose
compiler is verified down to machine code. Both are the shape of the thing this
row needs; neither is currently in the pipeline below.

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Lean's C code generator | Lake emits C and native objects from the Lean IR for the exact `Uwueave.RuntimeInit` import closure, including the six current `@[export]` entry points: request encoding, move replay, request-canonicality audit, sequence replay, ERA resolution, and `uwueave_preo_artifact_v2_validate_one`. Unverified, and the semantic distance from the Lean definitions to those objects is the largest single jump in this repo. One narrower substitution boundary **is paid**: `Exec`'s `getWord`/`pushWord`/`gatedReplayFull`, `SeqKernel`'s `childrenK`/`emitK`, and `EraKernel`'s `responseWords` optimizations are installed by proved `@[csimp]` equalities. `Exec.encodeRequestKernel_eq` also proves that the typed export adapter delegates to `encodeRequest`; neither fact verifies later IR → C lowering. There is no unproved `implemented_by` replacement in the Lean tree. | **OBLIGATION** | Three real routes, in ascending cost: **translation validation** per emitted function (check the C against the IR for the handful of exported kernels, not the whole tree); a **proved exporter subset** (the kernels use a narrow fragment — arrays, `Nat`/`UInt64`, structures, no closures over the FFI boundary); and full verified compilation, which CakeML shows is achievable for a functional source language. ⚠ CompCert does **not** cover this row — it starts at C. |
| The C compiler and linker | Lake owns native compilation of every object in the runtime closure; `cc::Build` compiles exactly `shim.c` at `opt_level(2)` and archives that object with Lake's byte-snapshotted objects. Both use the available host toolchain, and the build refuses cross-compilation and targets other than native macOS/Linux. | **OBLIGATION** | Compile the emitted C with **CompCert** and link that. The surface is the RuntimeInit closure plus `shim.c`; first determine whether Lean's emitted C sits inside CompCert's supported subset. RuntimeInit makes that experiment reproducible by naming the exact closure, but does not prove either compiler or linker. |
| The Lean runtime (`libleanshared`) | Reference counting, the allocator, `lean_alloc_sarray`, `lean_dec_ref`, and module initialization. Linked as a dylib from the toolchain, with an rpath baked in by `build.rs`. The initializer choice is now closed mechanically: the data-free `RuntimeInit` imports exactly `Exec`, `SeqKernel`, `EraKernel`, and `Preo.ArtifactJournalKernel`, and the shim calls only its generated initializer. The ownership contracts are written at the touched Rust and C calls, but the runtime does not check them. | **OBLIGATION** | Verify the manual reference-count and allocation discipline across the boundary, especially construction of the four typed arrays for `uwueave_encode_request`, construction/consumption of the artifact validator `ByteArray`, release of its owned one-byte result, and the rule that exported kernels consume their Lean arguments. The exact initializer closes omission/drift in module selection; it is not a proof of the initializer, runtime, or ownership discipline. |
| `shim.c` | 225 lines, eight exported shim functions (`init`, `encode_request`, `replay`, `seq`, `era`, `request_canonical`, `preo_artifact_v2_validate_one`, `free`). Initialization calls only the data-free `RuntimeInit` root after `lean_initialize_runtime_module`; Rust serializes it with `Once`. The request path flattens typed records into Lean arrays and calls the Lean encoder; the artifact path copies an exact host frame into a Lean `ByteArray` and reduces the owned one-byte validator result to a scalar. Both paths manage Lean references and C allocation ownership. The shim does **not** decide FORMAT-v3 bytes or decode `ArtifactEncoding`. | **OBLIGATION**, and the cheapest one here | Specify and verify the object construction, bounds, ownership, and copying with VST or Frama-C, or generate the shim. Its surface is still small; the single exact initializer and Lean-owned decisions narrow the obligation but do not verify this adapter. |
| The ABI and the FFI boundary | Handwritten `extern "C"` declarations in `rust/src/ffi.rs` still match `shim.c` by convention. Typed `#[repr(C)]` request inputs have matching C structs, C `_Static_assert`s pin their size and field offsets, a real-ABI test exercises that route, and the artifact validator passes a fresh `ByteArray` to `Preo.ArtifactJournalKernel.validateOneKernel` and consumes its owned one-byte result. Every touched call has an explicit safety contract. Those checks do not prove that the Rust, C, and generated Lean declarations agree. | **OBLIGATION** | Generate both declarations from one header or run bindgen, then verify both typed-array conversion and `ByteArray` ownership against the Lean export signatures. Static assertions detect some C layout drift; they cannot establish cross-language ABI agreement or runtime ownership. |
| Rust `unsafe` | **14 textual occurrences, all of them in `rust/src/ffi.rs`** — no `unsafe` anywhere else in the crate. Every touched call and raw-slice/free step now carries a local `SAFETY` argument, including the artifact validator call. That concentration and documentation are paid controls, not an FFI proof. | **OBLIGATION** | Keep the concentration (any new `unsafe` outside `ffi.rs` is a regression) and verify the C/Lean obligations those comments rely on. Miri cannot follow execution across this FFI boundary, so it cannot close the row. |
| Lean-owned request encoding | Rust now supplies typed first-parent, operation, grant, and revocation lanes to `uwueave_encode_request`; the exported Lean adapter reconstructs the values and calls `Exec.encodeRequest`. `encodeRequestKernel_eq` states that delegation, and `decodeBase_encodeRequest`, `decodeOps_encodeRequest`, `decodeGrants_encodeRequest`, `decodeRevs_encodeRequest`, and `replay_encodeRequest` close the canonical input codec. Rust no longer owns a FORMAT-v3 byte encoder. The old `requestCanonicalKernel` endpoint remains only as a compatibility/test audit. | **PAID** at the wire-decision boundary | Preserve the single encoder. Rust still chooses the typed node indices and operations it asks Lean to encode; the typed ABI, shim, runtime, and codegen remain the separate obligations above. A second byte-level request encoder in Rust would reopen this row. |
| Storage and index glue | `causal.rs`, `movelog.rs`, `seq.rs`, `era.rs`, `weave.rs`, plus `persistence/{record,artifact,document,history}.rs` — `BTreeMap`/`BTreeSet` state, derived indexes, merge plumbing, and four physical journal surfaces. Property tests assert laws over the real crate through the real kernel; persistence tests exercise framing, retry, corruption, torn tails, typed reconstruction, checkpoint rejection, causal-prefix admission, durable pending arrivals, and event-id collision refusal. | **OBLIGATION** | The tests are good tests and zero formal evidence, which `lib.rs` already says. Keep every semantic decision in Lean where possible, and refine the remaining host codecs, indexes, replay adapters, filesystem operations, and failure observations instead of treating their tests as theorems. The house rule remains "no Rust twin of a decision procedure." |
| Cargo/Lean build freshness and native closure | **Paid as a fail-closed control.** The data-free `Uwueave.RuntimeInit` is the single closure/initializer root and directly imports the four exported-kernel modules. `build.rs` first requires a full `lake build`, reads Lake's exact RuntimeInit setup metadata, validates its closed schema and required kernels, queries one exact Lake-owned native object for every transitive member, snapshots the bytes, stages stable copies, and asks `cc` to archive only those objects plus the one compiled shim. It then verifies exact archive membership and every extracted Lake-member byte. A final `lake --no-build build` plus no-build path queries recheck the root, setup, closure and objects; before/after snapshots cover every Lean source and the root, Lake/toolchain manifests, shim, build script, Cargo manifest and lockfile. Cargo rerun directives cover the same control inputs. The current native-closure gate observed **13 Lake objects / 659,152 bytes** before archiving and **14 archive members / 803,520 bytes** including the shim (archive SHA-256 prefix `29cea783`). | **PAID** | Preserve `RuntimeInit` as data-free and make every native kernel a direct import there. Keep Lake setup metadata as the sole discovery authority, keep the input and byte-stability postconditions synchronized with new build controls, and retain the adversarial validator tests. This closes stale/mixed/extra/missing native-object selection and initializer drift; it does **not** prove Lean code generation, native compilation/linking, the shim, ABI, runtime behavior, or filesystem semantics. |
| Persistence and durability | The crate ships concrete pure-Rust host journals, but not a filesystem theorem. `ArtifactJournal` stores canonical V2 frames; `DocumentJournal` stores the unauthenticated typed `MoveLog` subset; and `HistoryJournal` stores causally closed explicit-id events. `BufferedHistoryJournal` remains an optional **volatile** out-of-order view. Wave 27 adds the distinct `HistoryArrivalJournal`: every canonical arrival is durably appended before classification; capacity, accepted/materialized/pending maps, exact state digests, and checkpoints are replayed and validated on reopen. Exact retries are no-write, pending parents survive restart, deterministic drain follows later parent arrival, and collision/capacity/torn/corrupt/version/checkpoint failures preserve the prior prefix. The shared `RawJournal` supplies bounded record lengths, sequence-addressed retry, advisory locking, BLAKE3 checksums, explicit sync policies, poisoning after uncertain I/O, and narrow torn-tail truncation. A focused V4 integration stores the canonical 369-byte sidecar under `SyncData` and intentionally accepts a version-mutated copy as a distinct opaque payload, proving storage is not authentication. | **OBLIGATION**, with canonical artifact bytes, the narrow Lean validator, and concrete journal/test rungs **paid** | Prove or differentially validate the Rust physical formats and replay adapters against their Lean contracts, then state a filesystem/crash model. `HistoryArrivalJournal` now supplies the durable queue missing in Wave 26, but no byte/refinement theorem connects it to `PersistentHistoryRuntime.deliverySchema`; reconcile Lean's duplicate-free parents with Rust's stricter canonical order. Bound total file/record counts; harden path/permission/locking/sync behavior; add short-write and real crash testing; and add authenticated append plus an externally committed head. Bind `HistoryEventId` and opaque payloads to authenticated canonical encodings before treating storage admission as protocol admission. BLAKE3 is unkeyed corruption detection, not authenticity. The stores are one-record-at-a-time, not an `AtomicBatchObservation`, and no `sync_*` return proves stable media or power-loss survival. |

**Ten rows: zero PREMISE, eight OBLIGATION, two PAID boundaries.** That is the
headline of this ledger, and it is the correction codex asked for: *nothing in
the execution stack is terminal.* It is all engineering, some of it large, none
of it impossible. Canonical request encoding and build freshness are closed
controls; neither closure proves the compiler, runtime, shim, ABI, unsafe calls,
storage glue, or a proved/authenticated durable host binding.

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
root-level `main` declarations never enter one proof aggregate. The serialized
Wave-27 `cargo test --all-targets` gate passed **147/147 Rust tests** in 24.08s
(2.59s compile time). That is valuable
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

---

## Ledger 3 — environment and model premises

*What must hold about the world for the theorems to bind to a deployment.*

### 3a. Delivery, identity, membership

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Fair delivery | `Liveness.lean`'s `FairOn`: a **finite covering** — every participant's received set is membership-equivalent to the issued set. Under it, every replica reaches `joinAll`; under an unfair schedule there is a constructive starvation witness. | **PREMISE** at the model boundary, with transmutable edges | The model is deliberately not a network. Its own non-capture list names the edges: loss as a probability, RTT, topology dynamics, "eventually" as a temporal modality over infinite traces, and multi-hop epidemic diameter for `n > 2` under pull-only schedules. Each is a theorem someone could write; the coinductive-stream version of fairness is the standard next rung. |
| Identity and authenticity | `Authenticity.lean` names an abstract `SignatureScheme`, domain-separated signed grant/event messages, `AuthenticIssuer`, a trace-relative `EUFStylePremise`, and `ForgeryWitness`; `AuthenticatedAdmission` transports accepted records only when genuine issuance is separately established. Typed expression evidence retains exact source and `Expr.Hole` path under external `SourceAuthenticity`. Wave 27 adds `AuthenticatedWorldContext`: an issued signed position is joined to exact typed materialization, roster, active unconsumed grant, holder, causal origin and version; consumption is a grow-only tombstone receipt, with a deliberately strict unique-grant-per-candidate premise. `AuthenticatedFrontier` binds an accepted+issued progress event to exact issuer/source, roster, timestamp, frontiers and issued/delivered pools, while lawful delivery remains independent. `RuntimeAuthV4` still supplies the non-shipping canonical signed-request foundation. Its new checked sidecar is a one-way projection from `ReadyForExecution`, shape, grant and context receipts to bounded neutral rows under durable tag `⟨4,162⟩`; it is not the `UWV4` request wire, and decoding cannot recreate checked evidence. | **OBLIGATION** — the abstract handoffs, typed/context attribution, lawful frontier binding and one-way V4 sidecar are paid; see 3b | Choose a concrete signature scheme and authenticated key/history/roster representation, supply an EUF-CMA argument and actual verifier, and bind the opaque sidecar substrate/head/origin/version identities to that deployment. Connect `SourceAuthenticity` and received traces to deployed observations. Decide whether strict one-use grants are the intended capability semantics or design an explicit multi-candidate accounting rule. `VerificationBoundary.Accepts`, storage observations and filesystem behavior remain premises/tests, not mechanisms or theorems. The Rust arrival test deliberately stores a version-mutated sidecar as opaque data, proving storage is not admission. |
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
| Implementation correctness, constant time, parsing | Nothing — there is no signature implementation here, and `blake3` is trusted as a dependency. | **OBLIGATION** | This is the EverCrypt row: implementation correctness, memory safety and secret independence are *proved* properties in shipping code today. Parsing deserves its own mention — a signature verifier's parser is where real deployments break, and it is ordinary verifiable code. |
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
tested host rungs, and authentication has an abstract transport plus a canonical
v4 foundation. Their formal deployment refinements—and shipping authenticated
v4 admission—remain obligations.

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
