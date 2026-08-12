# COHERENCE — does the assembled thing tell one story?

*The original audit of the whole tree, read cold. Fifty-eight Lean modules, ~1,700
theorems, ~2,750 declarations, a Rust crate, five documents and a website —
built in one night by roughly forty lanes that each verified their own file and
none of which read the others. Every claim below is cited to `file:line` and was
checked at source. The original snapshot is retained below because its evidence
still explains the repairs; the current-wave reconciliation immediately below
supersedes its counts and status labels.*

*Read 2026-08-11, spanning `f6f35fe` → `e0937ef`. **The tree moved during the
audit** — wave 13b landed four modules mid-read, and §A.1 is sharper because of
it. Counts move; the mechanisms are what to check.*

---

## Current-wave reconciliation — 2026-08-11

This is the delta audit after the execution encoder, durability, authenticity,
Byzantine, recursive-choreography, structured-evidence, frontier, outcome-spec,
protocol, world-context, and preoscript artifact work landed, followed by the
Cycle-20 authoring foundations, Cycle-21 checked-manifest/result foundations,
the Cycle-22 language-consumer and runtime/persistence foundations, the
Wave-23 automation/trust/native-closure work, and the Wave-24 failure-honest
elaboration, projection, and real-artifact execution work. The new
modules, their root/gate wiring, and their MAP and TRANSPORTS entries are
checkpointed together: a clean checkout cannot receive only one side of that
assembly.

### Current headline

The mathematics added this wave is disciplined about hypotheses. The assembly
was repaired during this audit and is now complete in the live working tree.

| Surface | Live evidence | Current verdict |
|---|---|---|
| Root → gate | `#gate_covers_root` at `Uwueave/Audit.lean:184-211` parses `Uwueave.lean` with Lean's own header parser and checks every direct root import is in the gate environment; the intentionally indented `TrustFloor` import (`Uwueave.lean:1-3`) is an executable regression. `Choreo` is in both (`Uwueave.lean:83`, `Uwueave/Audit.lean:64`). | **The original A.1 defect and the brittle line-scanner follow-up are closed.** |
| Disk → root → gate | There are **148** Lean module files under `Uwueave/`; the root directly imports **127** Uwueave modules excluding `Audit`, while its transitive closure and the audit gate each reach all **148/148**. The executable-only `Preo.ArtifactEmitMain` is an intentional filesystem boundary: `Audit` imports it for trust coverage, while the proof root does not import it directly. The live full gate completed **150 jobs**, reports those **127** root modules covered, and audits **20,801** constants. | **The current-wave assembly defect remains closed, including the executable boundary.** |
| Checkpoint → disk | Cycle 21 adds nine Lean modules and the matching root, audit, MAP, TRANSPORTS, census, and surface changes together. | **The assembly is commit-atomic:** none of the new root imports is left dangling. |
| MAP → disk → gate | The MAP file table has **148 unique rows for 148 files**, with no missing or extra module, and every module is inside the root/gate closure. Its keystone table currently contains **500** theorem rows. | **The former 34-row exposure remains closed.** The table is a reading aid, not a per-name trust gate. |
| TRANSPORTS | The ledger has **116** unique numbered rows, including the explicit ArtifactEmit canonical-byte crossing, checked manifests, budget-bearing V2 validation, communicated choice, composite deltas, contextual compilation, differential evaluation, status effects, temporal fairness, and typed edits. | **The current-wave crossings are paid and their failure boundaries are recorded.** |
| Runtime persistence | `ArtifactFrame::new` bounds a frame at `MAX_ARTIFACT_FRAME_BYTES = 1 MiB`, checks its v2 envelope, and asks the exported Lean `Preo.ArtifactJournalKernel.validateOneKernel` for exact semantic canonicality before `ArtifactJournal` stores the unchanged bytes in checksummed `UWARJ001` records. `DocumentJournal` separately stores canonical typed `MoveLog` mutations and prefix-equal checkpoints in `UWDJRN01`. | **A concrete pure-Rust host rung has landed.** It is not a filesystem theorem, authenticated document admission, multi-record atomic commit, or a refinement of `PersistentRuntime`. |
| Real artifact bytes | `Preo.ArtifactEmit` selects two real checked encodings and its proved-equal stack-safe implementation produces exact `ArtifactDurable.projectionBytes`; the explicit CLI writes only when invoked. The Rust integration test carries both artifacts through Lean validation, `SyncData` append, close/reopen, exact-byte and BLAKE3 comparison, then rejects mutation, truncation, and a wrong version. | **The fixture-to-real-export execution gap is narrowed.** Importing remains I/O-free, and the test is not a filesystem or stable-media theorem. |
| Execution bytes | `Exec.encodeRequestKernel` invokes `encodeRequest` (`Uwueave/Exec.lean:772-782`); Rust supplies typed records (`rust/src/ffi.rs:34-53,85-115`) and no longer owns FORMAT-v3 bytes. `RuntimeAuthV4` now specifies canonical signed-move bytes and layered admission premises, but is deliberately not wired into that shipping path. | The v3 wire-encoder decision is closed; ABI, shim, runtime and codegen remain open. Host persistence has a tested narrow implementation, while formal filesystem/refinement and authenticated v4 admission remain open. |
| Native closure and initialization | The data-free `RuntimeInit` directly imports `Exec`, `SeqKernel`, `EraKernel`, and `Preo.ArtifactJournalKernel` (`Uwueave/RuntimeInit.lean:1-18`). `build.rs` takes Lake's setup description as the sole transitive-closure authority, snapshots and stages the exact native objects, verifies the archive member set and bytes, then rechecks Lake paths, setup, objects, every Lean source, and build configuration (`rust/build.rs:43-150,358-438,575-722`). The shim calls only the RuntimeInit initializer (`rust/shim.c:14-17,54-70`). The full gate observed **13** Lake objects / **655,368 bytes**, a **14**-member archive including the shim / **798,968 bytes**, and **133** Rust tests. | Stale, extra, missing, or mixed-generation native objects and initializer drift now fail closed. Code generation, compiler/linker correctness, ABI, ownership, runtime behavior, and filesystem semantics remain execution-TCB obligations. |

Cycle 20 adds:

`AuthenticatedAdmission` · `FiniteHistory` · `Preo.ArtifactDurable` ·
`Preo.Expr` · `Preo.ProjectionV1` · `RepairSynthesis` · `ScheduleSynthesis`.

Cycle 21 adds:

`ChoreoChoice` · `ClashGraph` · `CompositeDelta` · `ContextCompiler` ·
`Preo.Incremental` · `Preo.ProjectionV2` · `StatusEffects` · `Temporal` ·
`WovenEdit`.

The Cycle-22 runtime/persistence portion adds:

`PersistentRuntime` · `Preo.ArtifactJournalKernel` · `RuntimeAuthV4` · the
pure-Rust `ArtifactJournal` and `DocumentJournal` stores. `PersistentRuntime`
and `RuntimeAuthV4` are contracts/foundations; only the two explicitly bounded,
unauthenticated journal surfaces are host implementations.

Wave 23 adds the trust/build and language-automation layer:

`TrustFloor` · `ListProofs` · `Tactics.Verdict` ·
`Preo.ArtifactData` · `Preo.ArtifactChecked` · `Preo.ArtifactDiagnostics` ·
`Preo.ArtifactDurableCore` · `Preo.ArtifactJournalDiagnostics` · `RuntimeInit`.
The tactic core now distinguishes applied, inapplicable, resource-refused, and
internal-error routes; automatic finite classification is capped at 64 states /
4,096 ordered pairs while explicit `classifyFinite` remains total. The native
`preo_protocol` surface spells all six `Protocol.Term` constructors and emits
the exact term, elaboration, session, plan, five limits, and witnessed profile
bound rather than accepting only an opaque Lean term.

Wave 24 splits the large elaborator and projection surfaces without changing
their public command or declaration names. `Preo.Elab` is now a small facade
over phase modules; optional route probes roll back and return diagnostics as
data, required emissions fail loudly, and the enclosing command transaction
removes both declarations and environment-extension rows after a later
failure. Positive/red subprocess canaries cover the trust floor, route refusal,
resource caps, internal-error loudness, declaration congruence, whole-command
rollback, and same-name reuse. `ProjectionV1` and `ProjectionV2` retain their
production validators/renderers while core data, diagnostics, examples, and
large fixtures live in separate modules, so production imports do not pay for
diagnostic and fixture elaboration. `ArtifactEmit`/`ArtifactEmitMain` provide
the explicit, import-pure boundary to real artifact bytes described above.

The previous checkpoint's twelve modules were:

`Authenticity` · `Byzantine` · `ChoreoRec` · `Durable` · `EvidenceGraph` ·
`Frontier` · `Preo.Artifact` · `Preo.Export` · `Preo.Future` · `Protocol` ·
`Specification` · `WorldContext`.

During the audit, nine modules with 34 MAP keystone rows were outside the
root/gate closure:

| Module | Ledger rows outside the gate |
|---|---:|
| `DerivedDocument` | 6 |
| `Specification` | 3 |
| `Frontier` | 3 |
| `Authenticity` | 3 |
| `Byzantine` | 4 |
| `Durable` | 3 |
| `EvidenceGraph` | 4 |
| `ChoreoRec` | 4 |
| `WorldContext` | 4 |

`Preo.Artifact` and `Preo.Export` also had module and TRANSPORTS rows outside
the root, while `Protocol` and `Preo.Future` account for the other two
then-untracked modules. Root imports at `Uwueave.lean:73-84` and matching audit
imports at `Uwueave/Audit.lean:128-139` put those modules in both closures; the
Cycle-20 imports extend the same checked perimeter to all 98 then-current modules.
The table is retained as exact evidence of what the wiring
repair closed; it is no longer a live exposure.

### Closed findings from the original audit

These are genuinely closed in source, not merely marked closed here:

- **A.1, root module outside the gate:** `Choreo` is imported by both root and
  gate, and `#gate_covers_root` makes that particular mismatch refutable.
- **Current-wave disk modules outside root/gate:** the previous twelve and the
  seven Cycle-20 modules were imported by both root and audit; both transitive
  closures covered the then-current 98/98 modules, and the aggregate Lean check
  passed. The live totals are in the current headline above.
- **B.2, untracked retraction index:** `FORCODEX.md` and `CODEXHELP.md` are now
  tracked; `.gitignore:4-10` records why they must remain so.
- **B.5, ORMap reachability contradiction:** `Uwueave/ORMap.lean:53-56` now says
  the clash **is** jointly causally reachable, agreeing with its §3 and
  `CausalReach.ormap_clash_joint`.
- **B.6, LoRe retraction:** `Uwueave/Holes.lean:92-99,278-292,607-610` now carries
  the correction where the novelty claim lived.
- **C.1–C.3, MAP breadth and the two namespace misfilings:** the module table is
  now complete at 98/98, and `kernel_gate_agrees_gatedOps` / `applied_set_not_antitone`
  are filed under `Gated` / `ExecRefine`. The table briefly outran the root
  during this wave; that wiring gap is now closed too.
- **D.1, successor pointers:** the predecessor headers now point to the landed
  repair, future, frontier, evidence-graph, authenticity, recursive-choreography,
  protocol and summary rungs while retaining their deployment qualifiers.
- **E.5, crossings called meetings:** `Exits.lean:104-115` retracts the unit,
  and `Scheduling` supplies the separate coeffect/schedule model. The one legacy
  theorem name is explicitly retained for compatibility.
- **Execution request marshalling:** Rust’s handwritten request encoder is gone.
  `Exec.encodeRequestKernel_eq` is the typed-adapter equality, while
  `decodeBase_encodeRequest`, `decodeOps_encodeRequest`,
  `decodeGrants_encodeRequest`, `decodeRevs_encodeRequest`, and
  `replay_encodeRequest` close the canonical request codec. This closes one
  decision boundary, not the execution TCB.

### Source-header successor reconciliation

The new modules narrow or close the model-level item shown. Their predecessor
headers now say so, without declaring the deployment half closed.

| Predecessor claim | Landed successor | Honest reconciliation |
|---|---|---|
| `Choreo.lean:142-148` formerly left recursion and deadlock progress wholly UNDONE. | `ChoreoRec.lean:4-14`, `projection_sound_approx`, `guardedBarrierLoop_progresses`, `mismatched_barrier_is_deadlocked`. | Recursion through finite approximants and **one-step local** progress landed. Fairness, eventual delivery and temporal deadlock-freedom remain. |
| `DerivedDocument.lean:89-95` formerly said internal evidence edges were not built. | `EvidenceGraph.lean:4-23`, `wellFormed_iconfluent`, `flat_encodeEvidence_is_projection`. | Typed nodes/edges and endpoint integrity landed and refine the flat document. Cryptographic/content-addressed identity did not. |
| `Evidence.lean:150-154` and `WorldFuture.lean:165-170` formerly stopped at a flat frontier. | `Frontier.lean:4-33`, `world_complete_values_stable`. | A genuine antichain model and a narrow values-stability bridge landed. Authenticated progress, timestamp storage in `ResultEvidence`, render stability and revelation of the issued pool did not. |
| `WorldFuture.lean:156-164` formerly had no capabilities or known merge bases. | `WorldContext.lean:4-30`, `delivery_projects`, `delivery_lifts`, and the three independent hidden-axis witnesses. | The context model now carries active grants, a causal cut and version base/head. Authentication and automatic origin/version attribution remain explicitly UNDONE (`WorldContext.lean:42-51`). |
| `Gated.lean:88-96` formerly pointed only to collision extractors as a future signature pattern. | `AuthenticatedAdmission.authenticIssuer_to_signatureAuthentic`; `AuthenticatedGatedOp.ofAuthenticIssuer`; `Byzantine.unauthenticated_submission_can_pass_the_gate`. | Accepted signed events now derive the model-level attribution premise, and signed moves combine issuance, holder binding and `gatedOps`. FORMAT-v3/`Exec`/FFI authentication and a concrete EUF-CMA proof remain absent. |
| `EraCertificate.lean:127-139` formerly left event-id finality entirely to plumbing. | `Byzantine.authentic_issuance_preserves_finality` and `finality_failure_refutes_id_authenticity`. | The conditional carrier theorem **has** landed under `Settled`, grounded announcements, `IdAuthentic`, and `Issuance`. Hash/signature binding, fraud-proof detection and announcement authentication remain deployment work. |
| `Scheduling.lean:76-77` formerly said there was no surface syntax. | `Protocol.lean:1-24` supplies a deep semantic AST and checked elaboration; Preo accepts typed protocol terms, checked session forms, and `preo_budget` consumes an actual five-currency `ProfileUpperBound`. | Witnessed budget acceptance is paid. A custom nested protocol parser, integrated pretty budget block, and arbitrary schedule generator remain absent. |

The older `Evidence` → `WorldFuture` and `JoinHom` → `MinimalSummary` omissions
are now repaired as well. A successor documenting its predecessor is not enough;
the reader usually enters through the predecessor.

### Hypothesis audit of the new modules

No new theorem/docstring scope overclaim was found in the headline results.
The load-bearing hypotheses are stated where they matter:

- `Specification.coordinationFree_iff_historyMonotone_and_fiberDirected`
  requires `Total P` (`Specification.lean:183-194`), and the converse is kept
  separate without it.
- `ChoreoRec.projection_sound_approx` retains exactly `Choreo.ReadsAgree`
  (`ChoreoRec.lean:184-192`); the header explicitly denies fairness and eventual
  delivery.
- `Frontier.world_complete_values_stable` requires `WorldFuture.Wf`, frontier
  completeness, and settlement of every issued event (`Frontier.lean:506-522`),
  and concludes stability of `Evidence.values`, not `render`.
- `Byzantine.authentic_issuance_preserves_finality` requires `Settled`,
  `AnnouncementsGrounded`, `IdAuthentic`, and `Issuance`
  (`Byzantine.lean:277-303`). `authenticity_and_delivery_are_independent`
  explicitly prevents this safety result from being read as liveness.
- `Durable.recover_crashPrefix` consumes an explicit `TornFrame`; its header and
  `DeploymentAssumptions` manufacture no filesystem-prefix, append, rename,
  flush or power-loss guarantee.
- `WorldContext.delivery_lifts` requires the projected delivery, `Frozen`, and
  `Admits` (`WorldContext.lean:235-248`); projection is unconditional and lifting
  is not.
- `Preo.Export` states an API-shape boundary, not an impossibility theorem:
  decoded verdict tags are first-order data and no wire-to-proof constructor is
  exposed (`Preo/Export.lean:269-293`).
- `Preo.ArtifactJournalKernel.validateOne_projectionBytes`,
  `scan_encodeJournal`, `scan_append`, and `scan_stops_at_first_refusal` are
  logical exact-byte/scan laws. `PhysicalRecord.Valid` parameterizes its digest;
  it does not prove Rust's BLAKE3 calls or filesystem behavior. The Rust adapter
  is a test-backed refinement candidate, not a theorem.
- `PersistentRuntime.replay_success_retry`,
  `validateCheckpoint_eq_true_iff`, `checkpoint_suffix_replay_equiv`, and
  `AtomicBatchObservation` describe deterministic retry, checked checkpoints,
  and allowed batch observations over lists. No theorem instantiates them with
  `RawJournal`; the current host appends one physical record at a time.
- `RuntimeAuthV4.signingBytesV4_injective`, `decodeBounded`,
  `replica_is_signed_issuer`, and `WellLayered` close a canonical model boundary
  only. `VerificationBoundary.Accepts`, resolution, authorization, membership,
  append, and durable observation remain explicit premises; there is no
  shipping v4 Rust/FFI endpoint or concrete signature implementation.

### Judgement and interface collisions after the wave

One former headline must be retired: the current tree no longer has “exactly
one judgement.” It still has exactly one central **lattice** judgement,
`Confluence.IConfluent`, but it now deliberately has adjacent judgements:

- `Necessity.IsCFCS` is about reachable executions of an implementation.
- `Specification.CoordinationFree` is algebraic common refinement of arbitrary
  outcome fibers. Its docstring explicitly denies implementation existence and
  reachability (`Specification.lean:135-145`), and
  `invariant_coordinationFree_iff` ties its singleton-outcome instance back to
  `IConfluent`. TRANSPORTS row 4a records the totality boundary. This is a
  disclosed layering, not an accidental synonym.
- `Evidence.DeliveryFuture`, `WorldFuture.DeliveryFuture`, and
  `WorldContext.DeliveryFuture` reuse one short name at three layers, but the
  projection/lift theorems make the relation explicit. This is the good form of
  duplication.

Two former seams are now tied at their model boundaries:

1. `AuthenticatedAdmission.authenticIssuer_to_signatureAuthentic` transports
   accepted signed event records to Byzantine attribution through an explicit
   event codec, while `AuthenticatedGatedOp.ofAuthenticIssuer` adds holder and
   authorization evidence. Concrete cryptography and FORMAT-v3 admission remain
   deployment obligations rather than being smuggled into this theorem.
2. `Preo.ArtifactDurable.artifactCodec` gives the complete first-order
   `ArtifactEncoding` a canonical byte codec and format-v2 frame. `preo_export`
   now reaches that exact encoding and the budget-bearing Projection V2.
   `ArtifactJournal` retains those exact bytes and delegates canonical payload
   validation back to Lean rather than adding a semantic Rust codec. The
   surviving boundaries are the Rust/C/Lean ABI, physical-format refinement,
   filesystem/crash behavior, resource exhaustion, path hardening, and
   authenticated/anti-rollback storage.

### Execution-boundary reconciliation after the Lean encoder change

The implementation, source headers, MAP and `docs/TRUST.md` now agree:

- `Exec.lean`, `Gated.lean`, and MAP record ten rows: eight open execution
  obligations and two paid controls.
- The Rust byte marshaller is gone; production obtains canonical FORMAT-v3
  bytes from `Exec.encodeRequestKernel` over typed lanes.
- `Uwueave.RuntimeInit` is the data-free native root for `Exec`, `SeqKernel`,
  `EraKernel`, and `Preo.ArtifactJournalKernel`. Lake reports that exact
  transitive closure, `build.rs` archives and byte-verifies only its objects plus
  the shim, and `rust/shim.c` calls only the RuntimeInit initializer.

The FFI surface is still closed by name, but the old count is obsolete. There
are now **six** Lean exports: request encoding, replay, canonical compatibility
check, sequence, ERA, and exact-one Preoscript artifact-v2 validation. All six
have C callers; the request canonical checker is a test/audit endpoint, while
the encoder and artifact validator are on production paths.
The typed ABI, record flattening, Lean object ownership, C allocation, runtime
initialization and C/code generation remain trusted engineering. “Lean owns the
wire encoder and artifact semantic validator” must not be shortened to “the FFI
is proved.”

### Current prioritized action list for root

**P1 — turn landed foundations into end-to-end consumers**

1. Carry the native `preo_protocol` product (exact term, elaboration, session,
   plan, limits, and profile bound) into checked export/planning consumers. Its
   six-constructor authoring grammar is now real; arbitrary schedule synthesis
   and a pretty inline budget block remain separate work.
2. Generate useful repair and schedule catalogs instead of searching only
   caller-supplied entries; keep full prices/profiles and exhaustive refusal
   evidence through the surface.
3. Exercise Projection V2 and `ArtifactJournal` through downstream applications,
   then validate the physical codec/recovery behavior against the Lean contract
   and an explicit filesystem model. Separately implement the `RuntimeAuthV4`
   verifier/resolver/authority/membership/storage pipeline before claiming the
   shipping kernel receives authenticated operations. `DocumentJournal` remains
   an unauthenticated legacy/runtime substrate, not that pipeline.

---

## Original audit — executive summary (historical snapshot)

Everything from this heading onward is the retained original reading. Its
citations explain why the repairs were made; its counts, defect totals and
prioritized list are superseded by the current-wave reconciliation above.

**Mostly coherent — and the exceptions cluster in exactly the places the repo is
proudest of.**

The mathematics is one story and a good one. There is exactly **one** judgement —
`IConfluent` at `Uwueave/Confluence.lean:129`, over `MergeState` at `:49` and
`Invariant` at `:120` — and every verdict in the tree is stated against it or
against its seam refinement (`SegmentedIConfluent`, `Uwueave/Segmented.lean:43`).
Nobody re-defined the central object. Nobody invented a private synonym. Five
lanes read the tree looking for a false theorem and **none found one.**

**Citation integrity is the strongest result here.** Across **756 cross-module
`Module.name` citations in Lean docstrings, zero names dangle**; 640 more across
the documents and website, also zero. Roughly 250 were then checked
*semantically* — does the cited theorem say what the citer claims — and the large
majority hold, several of them impressively (`Uwueave/Gluing.lean`'s cross-repo
archaeology into `breadstuffs/metatheory` is verbatim right on every checkable
line, including a `grep -c` of "four times"). For a tree assembled by forty
non-communicating lanes, that is genuinely surprising, and it is why the defects
below are findable at all.

The defects are almost never in the theorems. They are in the **prose layer and
the module topology**. Four shapes recur, and each makes the repo look more
finished than it is:

- **A correction that reached three files and missed the fourth.** The reachability
  retraction landed in `ORSet` and `CausalReach` and not in `ORMap`'s header — which
  now contradicts its own §3 (§B.5). The "terminal TCB" retraction reached
  `docs/TRUST.md` and the website and missed the map (§B.1). The LoRe retraction
  reached the bibliography and missed the file making the claim (§B.6). "Crossings
  are not meetings" reached four modules and skipped the one that made the error
  (§E.5).
- **A qualifier lost in transit.** A theorem carrying `WF` + `UniqueGrant` cited as
  unconditional; a sufficient hypothesis narrated as "exactly when"; "TERMINAL at
  this layer" becoming "TERMINAL". The repo named this class itself at
  `docs/TRUST.md:206-210` and then committed it a dozen more times (§E).
- **Every pointer runs one way.** Downstream files point up, thoroughly and well.
  **No upstream file points down** — not `Holes`→`Evidence`, not
  `Evidence`→`WorldFuture`, not `JoinHom`→`MinimalSummary`, not `Exits`→`Repair`.
  A reader entering at the older file cannot learn they are reading a superseded
  reading (§D.1).
- **Two lanes solving the same problem, neither aware.** Two prices, two
  composed-floor theorems, two `loomVerdict`s with opposite verdicts, two
  field-kind interfaces that structurally contradict each other (§D).

**Defect count: 53 defects, 26 observations.**

| Severity | Count | Meaning |
|---|---|---|
| **P0** | 3 | A gate that cannot go red, or a retracted claim still shipping on the front door |
| **P1** | 15 | A reader is actively misled about coverage, scope, or what a theorem says |
| **P2** | 35 | Stale prose, mis-attribution, dropped qualifier, name collision, dead machinery |
| Observations | 26 | Deliberate layering — some said out loud, some not |

**The three that should not survive the week:**

1. **`Uwueave/Choreo.lean` is outside the trust gate** — 1,305 lines, 53 theorems,
   **four keystone-ledger rows**. And a lane edited `Uwueave/Audit.lean`'s import
   list *during this audit* and still missed it.
2. **`docs/MAP.md:61` still ships the exact claim `docs/TRUST.md` exists to
   retract** — "the terminal TCB". Four defects in one sentence. It reached
   TRUST.md and the website; it missed the document `README.md:93` points at first.
3. **The retraction index is not in the repository.** `FORCODEX.md` and
   `CODEXHELP.md` are `.gitignore`d and untracked, and 27 references across 13
   tracked files point into them — including the one indexing all eight retracted
   novelty claims.

---

## The story, in one page

It can be stated, and it composes. Here it is.

> **A replicated structure has a merge; an application has invariants. Ask whether
> the merge preserves them. That single question — I-confluence — is necessary and
> sufficient for coordination-freedom, so a `no` is not an engineering gap but a
> bound. The library's job is to answer the question for real structures, hand back
> a runnable counterexample when the answer is `no`, and then price the ways out.**

Six tiers. "Load-bearing" = three or more in-tree importers.

```
TIER 0  the judgement          Confluence   (MergeState · Invariant · IConfluent
                                             · escalation_witness)
          │
TIER 1  the catalog            Catalog ←11  the widest hub in the tree
          ├─ Acyclicity ─ Move ─ Sequence
          ├─ ORSet ─ ORMap · Delta ─ Liveness
          ├─ Causality ─ MVRegister ─ Undo
          ├─ Segmented · Nary · RALin · Necessity ─ CausalReach
          └─ Authority · Era · Tactics.Core
          │
TIER 2  composition            Spec ←7   Verdict-carrying DSL: a schema's answer
          │                              is a proof or a transported clash
          ├─ Seams ─ SeamAlgebra ─ Cost
          ├─ Ceiling      four refutations proved to be one theorem
          └─ Tactics      the verdict as a value
          │
TIER 3  the executable stack   Exec ─ ExecRefine ←6
          ├─ SeqKernel ─ Fugue      @[export] uwueave_seq_kernel
          ├─ EraKernel              @[export] uwueave_era_resolve
          ├─ Gated ─ GatedEra       @[export] uwueave_replay_kernel
          ├─ KernelCFCS                       uwueave_request_canonical
          └─ MergeModel
          │
TIER 4  the quantities         Cost ←6
          └─ Budget · CoordEffect · SeamColoring · Exits · Repair
          │
TIER 5  replicated computation Holes ←3
          ├─ Evidence ─ WorldFuture ─ ResultStatus
          ├─ JoinHom ─ MinimalSummary
          └─ Gluing
          │
TIER 6  the demos              Weave ─ WeaveState ─ Wellformed
                               Choreo                 (root-only — §A.1)

                 Audit         imports 46 of 55 root modules. The gate.
```

The spine is short and real: `Confluence → Catalog → {Move, Segmented} → Spec`.
Everything downstream instantiates a verdict (tiers 1–2), executes one (tier 3),
quantifies one (tier 4), lifts one from data to computation (tier 5), or
demonstrates the whole thing (tier 6).

**Where the story frays — the structural finding.** Tiers 4 and 5, the entire
output of waves 9 through 13, have **no in-tree consumer at all**. Twenty modules
are imported by exactly one file: `Uwueave/Audit.lean`, which imports them *only
so the gate can see them*. `Uwueave/SeamColoring.lean`,
`Uwueave/MinimalSummary.lean`, `Uwueave/WorldFuture.lean` and
`Uwueave/Gluing.lean` are **100% terminal — every declaration in each is unused
outside its own file**, including their headline theorems
(`segmented_iff_properColoring`, `delivery_future_is_not_state_indexed`,
`guardGluing_iff_iconfluent`).

For a catalog, leaves being leaves is correct. But it means three things:

- the import graph carries almost no information about what the recent work is
  *for*;
- `Uwueave/Audit.lean`'s hand-maintained import list is the only thing holding
  twenty modules inside the build perimeter — which is exactly how §A.1 happened,
  twice;
- and the modules that *were* meant to compose — `Exits` and `Repair`, `Cost` and
  `SeamColoring` and `CoordEffect`, `Repair` and `MergeModel`, `Spec` and `Choreo`
  — solved overlapping problems in parallel without importing each other, which is
  where every §D duplication comes from.

The document that was meant to carry the missing information is
`PREOSCRIPTING.md` §10. §C.2 is about what happened to it.

---

## §A — The gate

### A.1 ⚑ P0 — `Uwueave/Choreo.lean` is outside `#audit_floor`, and the fence was repaired around it

`#audit_floor` is elaborated exactly once, at `Uwueave/Audit.lean:133`. It reads
`getEnv` and filters `env.constants` by the `` `Uwueave `` prefix
(`Uwueave/Audit.lean:117-118`). The environment there holds **only `Audit.lean`'s
transitive imports**.

`Uwueave/Choreo.lean` is not among them. Nothing in the tree imports Choreo; its
only importer is the root aggregator, `Uwueave.lean:52`. Its **100 declarations
and 53 theorems** — including all four of its keystone-ledger rows,
`docs/MAP.md:159-162` (`projection_sound`, `coordination_free_iff_iconfluent`,
`seam_coordination_free`, `atMostOne_sync_cannot_be_dropped`) — are invisible to
the walk.

What the tree says about that, in four places:

- `Uwueave/Audit.lean:4-6` — "walks **every constant in the `Uwueave`
  namespace** — not a curated list".
- `docs/MAP.md:5-8` — "a stray `sorry` or `native_decide` **anywhere in the
  tree** goes red, zero-lag, no list to maintain. (Coverage is **total by
  construction**...)"
- `docs/MAP.md:94` and `:243` — "every row is covered by `#audit_floor`'s total
  gate — there is no per-row trust column to read." Four of those rows are not.
- `README.md:108` — "`lake build` # **every proof** + the total axiom gate".

All four are false for 1,305 lines. There is no live breach — a
`sorry`/`native_decide` sweep is clean tree-wide, Choreo included — but the gate
**cannot go red** there, and `lake build` only *warns* on `sorry` (no
`warningAsError`, no `leanOptions` anywhere in `lakefile.toml`), so CI stays green
through a hole in any of those 53 theorems.

**The vacuity tripwire cannot catch it.** It fires below 300 constants
(`Uwueave/Audit.lean:129`) and the walk sees 3,778 (`docs/TRUST.md:63`) — a count
that is itself Choreo-free and that nobody noticed was short. A blind spot of 2.6%
clears the emptiness check by a factor of twelve.

**And the fence was repaired around it, mid-audit.** Between `f6f35fe` and
`e0937ef` a lane landed `Uwueave/ResultStatus.lean` and **edited
`Uwueave/Audit.lean`'s import list to add it** (45 → 46 imports). Choreo was still
missed. Three further modules — `Uwueave/Histories.lean`,
`Uwueave/HonestRender.lean`, `Uwueave/Recoverable.lean` — are on disk, untracked,
and in **neither** the root nor the gate as of this reading. Those three are live
lanes mid-work and are not counted as defects; they are counted as evidence that a
hand-maintained perimeter reproduces this gap once per wave.

**Fix: one line — `import Uwueave.Choreo` in `Uwueave/Audit.lean`.** The
structural fix is the real one: **make the gate assert that its import closure
covers the root's**, so the next module added to `Uwueave.lean` and not to
`Audit.lean` fails the build instead of quietly leaving the perimeter.

*This is the repo's own named class. `docs/TRUST.md:63`: "A gate that cannot go
red is not a gate; a gate that can only go red one way is halfway there." The gate
has a third state nobody looked for — a region where it cannot go red at all.*

---

## §B — Retractions that did not propagate

The stated discipline is `README.md:129-132`: "when we get something wrong, the
correction lives where the claim lived... those retractions are in the documents,
not buried in the history." It mostly held — the three `Holes.lean` retractions,
the scalar coordination grade, the Choreo occupied-junction, and three of four ERA
corrections all landed cleanly (§ *What did not go wrong*). Where it did not:

### B.1 ⚑ P0 — `docs/MAP.md:61` still ships "the terminal TCB"

`docs/TRUST.md:5-8` opens by naming the claim it exists to demolish:

> This file exists because an external reviewer — **codex** — read our claim that
> three boundaries were *terminal* (signature unforgeability, **the C backend
> TCB**, Bailis's full generality) and demolished it.

`docs/TRUST.md:99-103` states the replacement: "Ten rows: zero PREMISE, nine
OBLIGATION, one absent component... *nothing in the execution stack is terminal.*"

`docs/MAP.md:61` still reads:

> Format v2 returns a per-op applied/skipped trace... Sole remaining open, stated
> in its header: C-backend trust — **the terminal TCB**, named, not undone work.

Four defects in one sentence:

1. **"terminal"** — the retracted word, for the retracted row.
2. **"not undone work"** — contradicted by nine named OBLIGATIONS with named next
   steps at `docs/TRUST.md:88-97`.
3. **"stated in its header"** — false. `Uwueave/Exec.lean` contains no occurrence
   of "terminal", and its header lists **two** opens, not a sole one
   (`Uwueave/Exec.lean:160-167`).
4. **"Format v2"** — the shipping format is **v3**, and v2 requests are explicitly
   refused (`Uwueave/Exec.lean:10`, guard at `:568`).

The correction *did* reach the website (`docs/index.html:1867`). MAP.md is the
document `README.md:93` sends readers to **first**, and it was missed.

### B.2 ⚑ P0 — the retraction index is not in the repository

`FORCODEX.md` and `CODEXHELP.md` are listed in `.gitignore` and **not tracked**.
Twenty-seven references across thirteen tracked files point into them:

| File | refs |
|---|---|
| `docs/BIBLIOGRAPHY.md` | 14 |
| `Uwueave/CoordEffect.lean`, `Uwueave/JoinHom.lean`, `Uwueave/Repair.lean`, `docs/TRUST.md` | 2 each |
| `Uwueave/Choreo.lean`, `Uwueave/Cost.lean`, `Uwueave/Holes.lean`, `Uwueave/MergeModel.lean`, `PREOSCRIPTING.md`, `docs/MAP.md`, `docs/index.html` | 1 each |

The one that matters most is `docs/MAP.md:11-14`:

> An external review found **eight claims of ours that the literature refutes or
> narrows**; they are retracted where they were made and **indexed in
> `FORCODEX.md` §0.5**.

A reader who clones this repository cannot reach that index. Nor `FORCODEX.md`
§4.7 (cited at `Uwueave/Choreo.lean:63` as the source of that file's retraction),
nor `CODEXHELP.md` §0.1 (cited at `Uwueave/CoordEffect.lean:5-6` and
`Uwueave/Repair.lean:171-172` as the errata that killed the scalar coordination
grade and the "meetings" currency).

The asymmetry is visible: the *grok* correspondence is tracked in full
(`docs/grok/GROKREVIEW.md`, `GROKJOB.md`, `GROKDONE.md`, `GROKCLAPBACK.md`); the
*codex* correspondence, which produced more of the tree's corrections, is ignored.
Whichever way it resolves — track them, or move §0.5, §4.7 and §0.1 into `docs/` —
right now the retraction ledger points outside the repository.

### B.3 P1 — `Uwueave/Gated.lean:150` still labels the C backend ⟨TERMINAL⟩

> **Below the Lean, the usual TCB.** ⟨TERMINAL for this repo⟩ The Rust
> marshaller's bytes ... and Lean's C backend.

`docs/TRUST.md:88-97` decomposes that boundary into nine OBLIGATIONS with named
next steps. This is the substitution `docs/TRUST.md:196-199` forbids: "'Terminal'
is never a verdict about a whole boundary."

Sharper: `docs/TRUST.md:24-28` **cites Gated.lean's honesty section as the seed of
the whole file**, praising it for writing "⟨TERMINAL, at this layer⟩" where the
summary wrote "terminal". It praises line 74 and does not notice that line 150 of
the same file makes the unqualified move.

(`Uwueave/Gated.lean:151` drops a qualifier of its own: the marshaller is "checked
at runtime", where `Uwueave/Exec.lean:161-163` correctly says "asserted in debug
builds" — `rust/src/movelog.rs:322` is a `debug_assert!`, compiled out of release.)

### B.4 P1 — `Uwueave/Exec.lean:160` asserts "no undone work" where TRUST names nine

> **Still open**, and not claimed — **the list is now exactly the TCB, no undone
> proof work hiding in its clothes**

Same boundary, one file over. Ledger 2 of `docs/TRUST.md` is nine rows of undone
work about precisely this list.

### B.5 P1 — `Uwueave/ORMap.lean` contradicts itself about causal reachability

- `Uwueave/ORMap.lean:53-55` (header honesty note) — "as in `ORSet.lean`, the
  presence refutation's state pair **may not be jointly reachable** under causal
  delivery of operations."
- `Uwueave/ORMap.lean:144-146` (§3 docstring, same file) — "under tag-scoped
  rem-after-add the projected clash **is jointly causally reachable**
  (`CausalReach.ormap_clash_joint`); **Live** for that reading."

Flat contradiction in one file. `Uwueave/ORSet.lean:85-87` carries the settled
version ("**Live** for that protocol reading, not LatticeOnly") and
`Uwueave/CausalReach.lean:22-24` records the retraction by name ("the ORSet
docstring's 'may not under causal delivery' does not hold for that protocol
reading"). The correction landed in two files and skipped the third.

This has a downstream consequence. `docs/MAP.md:34-39` states that the
reachability axis is "derived **only from the modules' own docstring honesty
notes**", and `docs/MAP.md:211` tags `ormap_present_not_iconfluent` **Live** — so
the ledger silently picked ORMap's §3 over ORMap's header. Collateral:
`Uwueave/ORMap.lean:56-58` ("The doomed-update pair, **by contrast**, IS
reachable...") now contrasts with nothing.

### B.6 P1 — the LoRe retraction never reached the file making the claim

`docs/BIBLIOGRAPHY.md:790-795` is explicit:

> `FORCODEX.md` §4.3 proposed three verdicts on one program ... and asserted
> "nobody currently offers all three", calling the third "the piece nobody has".
> **LoRe is essentially that combination, shipping, three years earlier**, and the
> claim is gone.

`Uwueave/Holes.lean:92` still reads "the piece §4.3 of the design memo **said
nobody has**", and `Uwueave/Holes.lean:537` "This is the leg the design memo (§4.3)
**said nobody has**". `Holes.lean`'s own "⚠ Three retractions" section
(`Uwueave/Holes.lean:186-236`) carries three other corrections and omits this one —
the one about the theorem the file calls its own novel leg. The hedge ("the memo
*said*") does not survive: the memo no longer says it.

### B.7 P1 — `Uwueave/Evidence.lean:786` is refuted by `Uwueave/WorldFuture.lean:573`, unmarked

`Uwueave/Evidence.lean:783-786`, the docstring of `futures_not_interchangeable`:
"they are nested, and the smaller one is **the one a CRDT can observe**."

`Uwueave/WorldFuture.lean:570-576`, `delivery_stability_is_not_state_indexed`:
"An interface that computes 'is this settled?' from what the replica holds is
**computing something that does not exist**", proved as `¬ ∃ P : ResultEvidence
… → Prop, ∀ w, P (observe w) ↔ FreeTermination DeliveryFuture renderW w`.

`Uwueave/WorldFuture.lean:131-141` carefully addresses two *other* sentences of
Evidence's; it does not address this one, which is the sharper and the false one.
`Uwueave/Evidence.lean` contains **zero** occurrences of "WorldFuture".

### B.8 P2 — `Uwueave/Confluence.lean` never learned that `Necessity` and `Nary` exist

Two open gaps the root judgement declares, both closed elsewhere, neither
correction returning:

- `Uwueave/Confluence.lean:132-135` — "That theorem quantifies over systems and
  lives in the paper, **not in this Lean**". `Uwueave/Necessity.lean:5-14` builds
  exactly that model and says it was written *because* Confluence refused it.
- `Uwueave/Confluence.lean:23-25` — "Where a proof genuinely wants mathlib (the
  escrow/quota-partition refinement over `Finset` sums) we say so and leave the
  mathlib-derived version cited rather than vendored." `Uwueave/Nary.lean:36` does
  that refinement in-tree: "**No mathlib / Finset.** Same core-only substrate as
  Catalog." The named exception no longer exists.

### B.9 P2 — the "four costumes" count is five, and one file claims the other says so

`Uwueave/Ceiling.lean:4-11` — "Four refutations ... wearing four costumes."
`Uwueave/Holes.lean:756-757` — "wearing its **fifth** costume, **and the file says
so plainly**." Ceiling says nothing of the kind.
`Holes.determinacy_not_iconfluent` (`Uwueave/Holes.lean:781-787`) is a real fifth
instance. Repeated stale at `Uwueave/Exits.lean:749-750` ("four costumes across
four files" — the four *instances* all live in `Ceiling.lean` §3; only their
*originals* live in four files) and `Uwueave/Repair.lean:1070`.

This is the failure `Uwueave/Audit.lean:31` names by its own name: "counts
advertised in prose rotted on schedule."

### B.10 P2 — `Uwueave/Seams.lean:114-117` missed correction 1

`Uwueave/Seams.lean:50-56` retracts the reading that ERA's epoch "carries an
arbitration result" — "**The arbiter never names a winner**." Every other §1 site
got a ⚠ (`Seams.lean:101-103`, `152-155`, `195-200`, `325-327`).
`sole_unpinned_not_segmented`'s docstring did not, and still asserts unmarked:
"which is ERA's actual design: the epoch exists to carry an arbitration result."
Milder residue at `Uwueave/Seams.lean:221-223`.

### B.11 P2 — `Uwueave/Ceiling.lean:34-36` cites a mechanism that was deleted

"The originals stay in their home files, where they carry the narrative and the
`Audit.lean` **pins**." There are no per-theorem pins:
`Uwueave/Audit.lean:18-37` records that the 113 `#guard_msgs` pins were deleted on
2026-08-10 and replaced by the total walk. The narrative reason still stands; the
pin reason is dead.

---

## §C — The map is not the territory

### C.1 P1 — `docs/MAP.md` is titled "every module" and covers 38 of 55

`docs/MAP.md:1` — "# The map — every module, what it settles".

Sixteen modules have no row. **Fourteen have no presence in MAP at all** — no
module row, no ledger row:

`Budget` · `CoordEffect` · `EraKernel` · `Evidence` · `Exits` · `Gated` ·
`JoinHom` · `MergeModel` · `MinimalSummary` · `Repair` · `ResultStatus` ·
`SeamColoring` · `WeaveState` · `Wellformed` · `WorldFuture`

(plus `Fugue`, which has one ledger row at `docs/MAP.md:173` and no module row.)

That is roughly 13,000 lines and the whole tier-4/tier-5 spine. Two of the absent
files describe themselves as the library's capstones:
`Uwueave/WeaveState.lean:2,11` — "the library's demo of itself... The question the
library exists to answer"; `Uwueave/Wellformed.lean:41` — "the theorem Grove has
and we lacked". Neither is on the map.

Worse, `docs/MAP.md:68` (the Holes row) instructs the reader to "see
`JoinHom.lean`" — a module with no row. A reader following `README.md:93` ("**[The
map](docs/MAP.md)** — every module") learns none of this exists. The ledger's
self-count is accurate (126 claimed at `docs/MAP.md:95`, 126 present), so this is
not rot in the ledger — it is a table that stopped at wave 8 while the tree ran to
wave 13.

### C.2 P1 — the only index for the new modules is a design doc's status table, and it says "in flight"

Ten of the absent modules appear in exactly one place: `PREOSCRIPTING.md` §10
(`PREOSCRIPTING.md:335-353`). Seven are marked **"in flight"** — `Repair`,
`CoordEffect`, `Budget`, `MergeModel`, `SeamColoring`, `MinimalSummary`,
`WorldFuture` ("proved / in flight").

Every one is landed, complete, and inside the axiom gate.
`Uwueave/Budget.lean` is 656 lines with a proved trichotomy; `Uwueave/Repair.lean`
is 1,167 lines with a priced monoid. The column plausibly means "the *language
feature* is in flight, the module is done" — but nothing says so, and this is the
only index a reader has.

Four modules — `EraKernel`, `Gated`, `WeaveState`, `Wellformed` — appear in
**neither** MAP nor `PREOSCRIPTING.md` §10. `Gated` is a shipping authorization
gate inside the move kernel; `EraKernel` is one of four `@[export]`ed C entry
points.

### C.3 P1 — three ledger claims that do not hold

- `docs/MAP.md:174` — `kernel_gate_agrees_gatedOps` | **Exec**. Declared at
  `Uwueave/Gated.lean:657`, namespace `Uwueave.Gated`. Wrong file *and* wrong
  namespace — and it is `Gated`'s only appearance in MAP, filed under another
  module's name.
- `docs/MAP.md:175` — `applied_set_not_antitone` | **Exec**. Namespace-correct,
  file-wrong: `Uwueave/ExecRefine.lean:1626`.
- `docs/MAP.md:69` — "`stampedHole` proves the iff is *not a renaming*
  (`Glues` and `IConfluent` come apart **exactly when** `Spanning` fails)."
  **Overclaim.** The ⟸ direction of `guardGluing_iff_iconfluent`
  (`Uwueave/Gluing.lean:264-265`) is `intro hic x d₁ y d₂ ha₁ ha₂ _; exact hic _ _
  ha₁.2 ha₂.2` — it never touches `hsp`. `Spanning` is **sufficient, not
  necessary**. `Uwueave/Gluing.lean:247-249` states it correctly ("`Spanning` is
  **not** removable"); MAP sharpened it into a false biconditional.

Every other one of the 126 ledger rows resolves to the named module.

### C.4 P2 — the module/namespace split produces bad citations in three places

`Uwueave/MergeModel.lean:60, 540, 547, 553, 561, 580, 590, 600` cite
`ExecRefine.absReplay_…`. Those declarations live in `Uwueave/ExecRefine.lean:961`
et seq. inside `namespace Uwueave.Exec` — and MergeModel's own *code*
(`:544, 551, 559`) correctly writes `Exec.absReplay_…`. Same root cause as §C.3's
first two rows. Worth one convention, stated once.

### C.5 P2 — `docs/MAP.md:51`'s ORSet row omits the module's second half

No mention of §3 — `orset_ew_present_iconfluent`, `removeAll`, or the remove-shape
dichotomy that `Uwueave/ORSet.lean:36-43` calls half the module.
`orset_ew_present_iconfluent` appears in no MAP row at all.

### C.6 P2 — `Uwueave/WeaveState.lean:496` points at a README paragraph that does not exist

"## §6. The report — the whole document at a glance ... **This table is what the
README points at.**" `README.md` (153 lines) contains **zero** mentions of
WeaveState, `weaveDocVerdict`, or the report table.

---

## §D — Duplicate and near-duplicate concepts

Sorted by whether the duplication is **said out loud**, because that is the line
between deliberate layering and accidental divergence.

### D.1 ⚑ P1 — every pointer runs one way. This is a class, not an instance.

Downstream files point up, thoroughly and correctly. **No upstream file points
down.** Verified by grep:

| Successor → predecessor | Backward pointer |
|---|---|
| `WorldFuture` → `Evidence` (`WorldFuture.lean:4-8, 32-46, 96-141`, plus `extension_image`/`delivery_image` as iffs at `:625, :643`) | `grep -c WorldFuture Uwueave/Evidence.lean` = **0** |
| `Evidence` → `Holes` (`Evidence.lean:4-6`) | `grep -c "Evidence\|WorldFuture" Uwueave/Holes.lean` = **0** |
| `MinimalSummary` → `JoinHom` (`MinimalSummary.lean:5-12`, quoting JoinHom's own boundary sentence) | `grep -c MinimalSummary Uwueave/JoinHom.lean` = **0** |
| `Repair` → `Exits` (`Repair.lean:25-37`, the model paragraph) | `grep` for `Repair` in `Uwueave/Exits.lean` = **0** |
| `Choreo` → `Holes`'s ⟨UNDONE⟩ choreography item (`Choreo.lean:3` is verbatim `Holes.lean:161`'s slogan) | `Holes.lean:160-163` still says "Not here; a sibling lane builds beside this one" |

The consequence is uniform: **a reader entering at the older file cannot learn
they are reading a superseded reading.** `Uwueave/Holes.lean:348-351`'s `World`
carries no warning that a second `World` exists one import away.
`Uwueave/Holes.lean:387`'s `Partial α := GSet α` carries no note that
`Uwueave/Evidence.lean:16-17` calls that carrier a conflation.
`Uwueave/Holes.lean:164-170` still lists the `Stable`→`Era` bridge as ⟨UNDONE⟩
prose with no pointer to `Evidence.closed_freezes` (`Uwueave/Evidence.lean:816`),
which narrows it.

**One forward sentence per predecessor closes the whole class.**

### D.2 OBSERVATION (exemplary) + P2 — two prices

`Uwueave/Exits.lean:238` gives `Exit.price : Exit S → Nat`, returning `0` for
`arbitration`, `exposedFork` and `rollback`. `Uwueave/Repair.lean:181-219` gives a
seven-field `structure Price` with a commutative monoid and a per-field justifying
theorem.

**`Uwueave/Repair.lean:25-37` is the best paragraph in the repository for this
audit's purposes.** It names the sibling, names the shape difference, names the
theorem that separates them (`crossings_cannot_see_the_difference`), and closes
"Nothing here imports `Exits.lean`." Every §D entry that is an OBSERVATION rather
than a DEFECT is one because some file did what that paragraph does.

Two things are still wrong. The pointer is one-directional (§D.1). And the prose
names the wrong pair: `Uwueave/Repair.lean:30-33` says the menu "prices
`arbitration` and `fork` both at `0` and warns ... that the two zeroes are not the
same zero". The actual note at `Uwueave/Exits.lean:76-82` distinguishes
**`arbitration`/`rollback`** from `seam`/`fullCoordination`; `fork`'s zero is in
the *same* currency as escrow's (`fork_price_zero`/`escrow_price_zero`, both
`zero_price_of_iconfluent`).

### D.3 P1 — two field-kind interfaces that structurally contradict each other

`Uwueave/MergeModel.lean:8-26` exists to establish one thesis, quoted from
`PREOSCRIPTING.md:195-201`: "**`MergeState` cannot be mandatory** ... a field-kind
interface with one mandatory `MergeState` would have erased our own theorem —
every MRDT field would have had to present a join it provably does not have."

`Uwueave/Repair.lean:520-532` declares `structure Promise` with `mergeState :
MergeState State` as a **mandatory field**, and `:512-513` calls it one of "six
fields ... every one is read". `Uwueave/Repair.lean:581-591`'s `Discharge` offers
exactly `IConfluent` / `SegmentedIConfluent` / `escalates` — both join-only. An
MRDT promise cannot be a `Promise`; an ancestral discharge cannot be a `Discharge`.

Neither file imports or mentions the other. Two "what a field kind must carry"
designs, landed the same night, mutually exclusive on their central decision.

Compounding it: `Uwueave/MergeModel.lean` never touches `clash_dichotomy`
(resurrection / accumulation) even though it imports `Ancestral`, and the whole
cost/exits/repair cluster is join-model-only — `Cost.crossings`,
`Cost.SegmentFree`, `Exit.Applies`, `Budget.Plan`, `CoordEffect.Strategy` all take
`SegmentedIConfluent`, defined on `MergeState` (`Uwueave/Segmented.lean:40-42`).
`MergeModel.IConfluentIn` (`Uwueave/MergeModel.lean:218`) has no segmented, cost,
or exit analogue. `MergeModel.lean:123-124` names this ⟨UNDONE⟩ — but `Exits` and
`Repair` were written *after* and neither notices.

### D.4 P1 — two `loomVerdict`s, same name, opposite verdicts

| | `Uwueave/Spec.lean` | `Uwueave/Choreo.lean` |
|---|---|---|
| `LoomDoc` | `:361` `GSet Nat × ((Nat → LWW) × Escrow Bool)` | `:908` `GSet Nat × Necessity.BitSet` |
| `loomInv` | `:368`, `quota`-parameterised, three conjuncts | `:911`, no parameter, two conjuncts |
| `loomVerdict` | `:375` — **`.free`** | `:1021` — **`.coupled`** |

Choreo imports Spec (`Uwueave/Choreo.lean:160`) and does not `open Uwueave.Spec`,
so the shadowing is silent. `Uwueave/Choreo.lean:893-905` never mentions that "the
loom document" already exists under that exact name with the opposite verdict. A
reader grepping `loomVerdict` finds FREE and COUPLED for two things both called
"the loom document schema", with nothing connecting them.

**By contrast, Choreo's `Verdict` duplication is exemplary and should be the
model**: `Uwueave/Choreo.lean:812` is a genuinely different type (three
constructors, indexed by roster/invariant/choreography), announced at `:38-40` and
`:799-804`, and **tied by a theorem** — `toSpecVerdict` (`:846`) demotes and
`toSpecVerdict_isFree` (`:872`) proves the two `isFree`s agree.

### D.5 P2 — `SeamColoring` and `CoordEffect` prove the same composed floor twice

- `SeamColoring.jointCost` (`Uwueave/SeamColoring.lean:831-833`) and
  `CoordEffect.Profile.comp` at a two-element strategy space
  (`Uwueave/CoordEffect.lean:147`) compute the same number.
- `SeamColoring.perStream_minimisation_is_unsound`
  (`Uwueave/SeamColoring.lean:875-885`) and `CoordEffect.pin_indep_min_unpayable`
  (`Uwueave/CoordEffect.lean:508-516`) are the same statement by two different
  proofs.
- `SeamColoring.no_seam_frees_both_via_coloring` (`:856`) re-proves
  `Cost.no_seam_frees_both` (`Uwueave/Cost.lean:965`) and does not replace it.

Neither file mentions the other; both import only `Cost`.

### D.6 P2 — `LinkedWF` twice, same type, different invariant, in a file that `open`s the other

`Uwueave/SeamAlgebra.lean:759-760` and `Uwueave/Cost.lean:626-627` both declare
`def LinkedWF : Invariant TwoFieldDoc := LinkedInv (SchemaWF tightBound)
(BudgetInv 10) Prod.fst Prod.fst _` — identical name, identical type, identical
first four arguments, **different fifth** (`allocOf` vs `linkAlloc`).
`Uwueave/Cost.lean:159` `open`s `Uwueave.SeamAlgebra`, so both are in scope and
Lean silently resolves to the local one.

The *reason* is disclosed well (`Uwueave/Cost.lean:617-621`). The *collision* is
not disclosed at all. Downstream, a `grep linkedWF` returns
`SeamAlgebra.linked_flagDay_segmented` (`:772`) and `Cost.linkedWF_segmented`
(`:687`) — about different documents. And `Uwueave/Cost.lean:88-95`'s ⚠ headline
finding ("the link does not lower the floor"), presented at
`Uwueave/Cost.lean:773-778` as a correction to `SeamAlgebra` §7's punchline, is
proved about *Cost's* linked document, not SeamAlgebra's. Nothing says so.

### D.7 P2 — `run_eq_joinAll` shadowed across an `open`

`Uwueave/Delta.lean:405` (`joinAll s (deltasOf ms s) = run ms s` — the sender's
state reconstructs) and `Uwueave/Liveness.lean:134` (`runDeliveries c sched r =
joinAll (c r) (received r sched)` — delivery is a fold at the target). Two
different facts, one name. `Uwueave/Liveness.lean:55` **opens `Uwueave.Delta`**, so
Delta's is in unqualified scope at exactly the point Liveness declares its own;
every bare use (`Liveness.lean:168, 190, 333, 351, 353`) resolves locally by
current-namespace precedence. It compiles. It is still a collision across an
`open`.

### D.8 P2 — three lemma names collide across `EraKernel` and `ExecRefine`

`Uwueave.EraKernel.size_foldl_pushWord` (`Uwueave/EraKernel.lean:487`) and
`Uwueave.Exec.size_foldl_pushWord` (`Uwueave/ExecRefine.lean:1147`) are **different
theorems with the same short name** — the first over `List UInt64`, the second over
`List Int` through `ofI`. Same for `getWord_foldl_pushWord_lt` (512 / 1163) and
`getWord_foldl_pushWord` (522 / 1173). EraKernel imports ExecRefine. This
elaborates only because ExecRefine's are `private` and EraKernel's `open`
(`Uwueave/EraKernel.lean:124`) is selective.

The real duplication is against a *third* trio: `EraKernel.lean:487/512/522` are
**literal α-renamed copies** of `ExecRefine.lean:1660/1669/1679` — forced (those
are `private`) and **unacknowledged**. The section header that should say so
compares against the wrong trio (`Uwueave/EraKernel.lean:481-485`).

**Contrast `Uwueave/ExecRefine.lean:1547-1549`**, which duplicates
`Move.mergeSort_pair` (`Uwueave/Move.lean:211`) byte-for-byte and *says so*.

### D.9 P2 — `sublist_flatMap_of_mem` is byte-identical in two files, both `private`

`Uwueave/Sequence.lean:564-574` and `Uwueave/SeqKernel.lean:685-695` are identical
character for character. Both `private`, so neither can ever be reused across the
boundary by construction. It is a pure `List` lemma with no CRDT content, in two
files that cite each other constantly.

### D.10 P2 — namespace scattering, and a latent ambiguity

`Uwueave/MinimalSummary.lean` puts its entire general theory in the **bare
`Uwueave` namespace** — `CtxEquiv` (`:149`), `Sufficient` (`:231`), `CtxQuot`
(`:340`), `ctxMk`, `ctxJoin`, `ctxAnswer`, `ctxFactor`, `decodeSummary` — opening
`namespace MinimalSummary` only at `:460` for the §4–§6 witnesses.
`Uwueave/JoinHom.lean` does the same **inconsistently**: `JoinHom`, `MonotoneLeq`,
`UpClosed`, `IncrementallyMergeable`, `RequiresEvidence`, `ResultDetermined` are
`Uwueave.*` (before `namespace JoinHom` at `:282`), while `ReplicatesEvidence`,
`SummaryFoldAgrees`, `Fourth` are `Uwueave.JoinHom.*`. `Uwueave/Repair.lean:322`
writes bare `IncrementallyMergeable` and `:328` writes
`JoinHom.ReplicatesEvidence`, confirming the split is real and arbitrary. Also
`Uwueave.JoinHom` is simultaneously a **definition** (`:133`) and a **namespace**
(`:282`).

Concretely: `Uwueave.Sufficient` (`MinimalSummary.lean:231`) collides with
`Uwueave.Delta.Sufficient` (`Uwueave/Delta.lean:374`). Four files `open
Uwueave.Delta` alongside `open Uwueave`; none currently imports `MinimalSummary`,
so nothing fires today. `Uwueave.lean` imports both.

### D.11 P2 — the definite article, three times

`Uwueave/SeqKernel.lean:112-113`, `Uwueave/EraKernel.lean:105-106` and
`Uwueave/Fugue.lean:169-171` each state that *the* export surface stays at exactly
one symbol. Locally each is true about its own kernel; collated, the tree has
**four** `@[export]`s.

### D.12 OBSERVATIONS — duplications checked and found clean

- **`Uwueave/Wellformed.lean` vs `Uwueave/WeaveState.lean` — FALSE POSITIVE, and
  the tree's best-handled duplication.** `WovenDoc := WeaveState.WeaveDoc × (Text
  × Horizon)` (`Wellformed.lean:189`) makes WeaveState's schema a literal factor,
  and every re-declared accessor **delegates**: `nodes d := WeaveState.nodes d.1`
  (`:196`), same for `bookmarks` (`:198`), `contents` (`:200`), `grants` (`:202`),
  `pins` (`:204`). `NodeId`/`User` are labelled "restated so this file reads
  standalone" (`:171, :174`). Relation stated at `:77-84` and *used* — `:474, :476,
  :480` reuse `WeaveState.pinA_atMostOne`/`pinB_atMostOne`/`pins_clash` rather than
  reinventing them. **No second document model.**
- **`Evidence`'s and `WorldFuture`'s futures are one notion at two indices, not two
  notions.** `WorldFuture.DeliveryFuture` (`:320-323`) and `ExtensionFuture`
  (`:328-333`) are *defined in terms of* `Evidence`'s, each a strict strengthening;
  `FreeTermination`, `SoundEvaluator`, `CanonicalEvaluator` are **shared**.
  `WorldFuture.lean:98` explicitly disclaims supersession and backs it with
  `extension_image`/`delivery_image` as iffs. The forward disclosure is exhaustive
  and good; only the backward pointer (§D.1) and one refuted sentence (§B.7) are
  missing. *(One genuine duplicate: `extension_stable_implies_delivery_stable` is
  re-proved at `WorldFuture.lean:409-412` while its docstring at `:407` calls it
  "transported". Neither copy has any consumer.)*
- **Two `World`s** — `Uwueave/Holes.lean:351` (`abbrev World := List Val`) vs
  `Uwueave/WorldFuture.lean:243` (`structure World (α)`). Unrelated types;
  `WorldFuture.lean:32-46` carries an explicit "⚠ `World` here is NOT
  `Holes.World`". Disambiguation is real — from one side.
- **`Grant`** — `Uwueave/Exec.lean:232` (`structure`) vs `Uwueave/Authority.lean:102`
  (`abbrev … := Nat × Nat × Nat`). Bridge real (`Gated.grantSetOf`,
  `Uwueave/Gated.lean:464`), described correctly at `Uwueave/Exec.lean:228-229`.
  Safe by qualification discipline only: `Uwueave/Gated.lean:180` `open`s Authority.
- **`Cut`** — `Uwueave/CausalReach.lean:50` (downward-closed op set) vs
  `Uwueave/Era.lean:205` (arbiter epoch announcement). Two genuine notions; neither
  file mentions the other's.
- **`wf_iconfluent`** — `Uwueave/Sequence.lean:146` and `Uwueave/Authority.lean:131`.
  Every cross-module citation found is qualified or unambiguous;
  `Uwueave/Wellformed.lean:324` and `:327` cite both, three lines apart, both
  qualified. The MAP Module column disambiguates and the CLI resolves by
  fully-qualified name (`rust/src/bin/uwueave-check.rs:12-14`). *Residual nit: the
  two ledger rows have identical `Theorem` cells, so `#print axioms
  wf_iconfluent` — the command `Uwueave/Audit.lean:34` advertises — is ambiguous.*
- **`Uwueave/Holes.lean`'s §0 G-Set lemmas** (`gset_ext :291`, `gset_mem_or :306`,
  `gset_leq_iff_subset :314`) are general `Catalog` material living in
  `Uwueave.Holes` and consumed by three other modules — self-flagged at `:276-277`.

---

## §E — Contradictions

### E.1 P1 — `ExecRefine` §7 says the input codec does not exist; `ExecRefine` §8 proves it

`Uwueave/ExecRefine.lean:996-999`:

> What is *not* proved here is the input-side mirror (`decodeBase`/`decodeOps`
> against a bytes-level encoder — **the kernel does not contain such an encoder;
> the Rust side owns request encoding**).

Contradicted 650 lines later by §8 of the same file (`:1645-1658`), by
`decodeBase_encodeRequest` (`:1859`), `decodeOps_encodeRequest` (`:1885`) and
`replay_encodeRequest` (`:2056`) — and by `Exec.encodeRequest`
(`Uwueave/Exec.lean:516`), which *is* the kernel-side canonical encoder the
paragraph says does not exist. The file's own header (`:41-46`) gets it right.
**The sharpest single contradiction in the tree.**

### E.2 P1 — `Uwueave/Spec.lean`'s flagship example bypasses the DSL, and its docstring says the opposite

`Uwueave/Spec.lean:186-188` states §2's premise: "a schema author assembling a
report should cite `gsetMemFree 0` and `mutexClash`, **not re-state proofs**."
`Uwueave/Spec.lean:371-373` describes the flagship: "built entirely from **catalog
verdicts** and the two lifts ... Read the term: it *is* the schema's
classification report."

The term (`:375-380`) contains **zero** §2 verdict values and **zero** §1
combinators:

```lean
.free (product_iconfluent (gset_mem_iconfluent 0)
        (product_iconfluent (pi_iconfluent …) (escrow_local_bound_iconfluent quota)))
```

— raw `Confluence`/`Catalog` theorems, exactly the "re-state proofs" the file says
not to do. Relatedly, the DSL's four *lift* combinators — `andFree` (`:67`),
`prodFree` (`:78`), `keyedFree` (`:101`), `gsetNotMemFree` (`:203`) — have **zero
consumers tree-wide**, including in Spec's own §4 examples,
`Uwueave/WeaveState.lean` and `Uwueave/Tactics.lean`.

### E.3 P1 — `Uwueave/Gated.lean:117-127` calls done work "unstarted"

> **Conflicting grant issuance is not arbitrated.** ⟨UNDONE⟩ ... composing that
> arbitration with this gate ... is real work, **unstarted**.

`Uwueave/GatedEra.lean:7` — "This file is that work, done" — delivering
`ge_deterministic` (`:214`), `ge_duel_resolved` (`:328`), `ge_finalised_stable`
(`:456`). `Uwueave/Gated.lean:69-72` states the file's own rule for exactly this
case: "the recipe was executed, and the item is gone rather than reworded."

(`Uwueave/GatedEra.lean:4-5` then *misquotes* the sentence it answers:
"Conflicting grant **operations**" for Gated's "Conflicting grant **issuance**",
inside quotation marks.)

### E.4 P1 — the shipping ERA kernel runs the ungated resolver, and its non-claims list does not say so

`Uwueave/EraKernel.lean:10` and `:68` state the decision layer is `Era.resolve`
**verbatim**. `Uwueave/Era.lean:76-82` states that `resolve` leaves two doors open
— `departed_rejoins_unchecked` (`Era.lean:1250`) and `promote_admits_nonmember`
(`Era.lean:1121`) — closed **only** by `lifeAuthorised`/`resolveGated`
(`Era.lean:1261`, `:1316`), which the kernel does not call.

`Uwueave/EraKernel.lean:100-117` is an otherwise scrupulous four-item non-claims
list. Neither open door is on it. `docs/TRUST.md:117` independently records the
same gap, so the fact is known in the tree — it just never reached the file that
ships it.

### E.5 P1 — `Uwueave/Exits.lean` priced in a currency the tree retracted — **RESOLVED 2026-08-11**

`Uwueave/Exits.lean:235` — "**The price of an exit, in meetings.**"
`Uwueave/Exits.lean:226-228` — "§3. The price, **in meetings**". Eleven
occurrences (`:33, 39, 77, 78, 96, 153, 165, 226, 228, 235, 292, 305`).

Contradicted by:

- `Uwueave/Cost.lean:112-116` — ⟨UNDONE⟩ "**Crossings are not meetings.** ... How
  many peers must attend ... is not modelled."
- `Uwueave/Repair.lean:169-173` — "there is deliberately **no** `meetings` field
  ... (`CODEXHELP.md` §0.1 erratum 3 is us getting that wrong in print)."
- `Uwueave/Budget.lean:59-64`, `Uwueave/CoordEffect.lean:90-98`,
  `PREOSCRIPTING.md:109-122` — all corrected.

Four sibling files repeated the disclaimer while the source and website still
printed the old scalar. The follow-up sweep corrected all five `Exits` display
strings and the website table/examples in place: seam projections now say
**crossings**, arbitration shows its typed `arbiterCuts`/rollback/trust bill,
and the site cites `Scheduling.no_crossing_count_determines_least_meetings`.
The historical theorem name `arbitration_needs_no_meeting` remains for API
stability and keeps only its valid negative meaning: replicas do not directly
agree with one another when an arbiter supplies the decision.

### E.6 P1 — `Uwueave/Exits.lean` §4.8 conflates two mechanisms and drops a quantifier

- **Dropped ∀.** `ancestral_exit_test`'s statement (`Uwueave/Exits.lean:601-608`)
  has right disjunct `¬ AncestralConfluent M g.impl I` — for **the given `M`**. Its
  docstring (`:598-600`) says "or **no effect-faithful merge** is ancestrally
  confluent at all ... that exit is dead **for every merge**." Same drop at
  `:110-112`. The ∀-form is a different theorem,
  `Ancestral.serialization_clash_defeats_every_merge`.
- **Wrong exit.** `Uwueave/Exits.lean:122-125` — "`ancestral_exit_discriminates`
  below proves the **stronger-metadata** half in both directions." It does not:
  no `Exit.strongerMetadata` and no `Exit.Applies` appears in it.
  `Exit.strongerMetadata.Applies` (`:216-218`) demands a join-homomorphism, and
  `Ancestral.join_is_ancestral_merge_iff_trivial` (`Uwueave/Ancestral.lean:239`)
  proves an `AncestralMerge` is a join only on a one-point carrier.
  `Uwueave/Ancestral.lean:722-738` says the metadata escape is what a two-way CRDT
  does **instead of** having an LCA; Exits attaches it to the branch where the LCA
  *is* the fix.
- **Uninstantiable premise.** `Uwueave/Exits.lean:1156-1160` and `:122-126` claim
  the ceiling and the balance are "both accumulation clashes in
  `Ancestral.clash_dichotomy`'s sense", but neither `Cost.pinInv` nor
  `Exits.balanceInv` has a `Guarded`, `AncestralMerge` or `Serializing` instance
  anywhere in the tree.

### E.7 P1 — `Uwueave/WorldFuture.lean` misdiagnoses its own witness, in four places

`Uwueave/WorldFuture.lean:124-126, :130, :713-715, :775-778` all attribute the
completeness gap to **wellformedness**: "a world with no futures satisfies it
vacuously ... `World α` contains such worlds, because wellformedness is a
hypothesis"; "the gap is exactly the **ill-formed carrier junk**".

The refuting witness `wRosterUnknown` (`:754-759`) **is wellformed** — `observe =
exactW`, `pool = (cand47, srcsAB, srcsA)`, and `srcsA ⊑ srcsAB` holds
componentwise, so `delivery_refl` applies and it *does* have futures. What it lacks
is `RosterKnown`: `no_sealed_future_of_wRosterUnknown` (`:761-765`) discharges
`h.2.2`, the `RosterKnown` conjunct. The true cause is that `SealedFuture`
(`:339-340`) **bakes `RosterKnown w` into the relation**, destroying reflexivity —
a design choice the header never surfaces. Four docstrings blame wellformedness for
a roster failure.

### E.8 P2 — `Uwueave/Confluence.lean:174-177` cites a module that does not contain the phenomenon, and `Spec` refutes the example

Confluence names `Uwueave.Weave` as where cross-field invariants "bite", offering
`node.parent ∈ nodes` as an example.

- `Uwueave/Weave.lean` contains exactly one refutation,
  `active_path_not_iconfluent` (`:100`), and it is **not** cross-field:
  `IsActivePath` (`Weave.lean:89-90`) is a predicate on a **single** `GSet Nat`,
  which the file itself (`:94-95`) calls "the exact disjunction-trap shape of
  `Catalog.or_breaks_iconfluence`" and `Uwueave/Tactics.lean:373-378` groups with
  `or_breaks_iconfluence` in the same single-`GSet Nat` probe pool. Weave has no
  product-state theorem at all. The same mis-citation is the motivating exhibit for
  `Verdict.cross` at `Uwueave/Spec.lean:141-142`.
- `Spec.pointsAtExisting_iconfluent` (`Uwueave/Spec.lean:489-498`) proves the
  `node.parent ∈ nodes` shape **is** I-confluent, and `Uwueave/Spec.lean:464-473`
  says so ("The reflex says relational = doomed... The reflex is wrong here").

### E.9 P2 — `Uwueave/Exits.lean` contradicts itself about `Exit.Applies`

`Uwueave/Exits.lean:493` — "This is the content behind `Exit.Applies`'s **`True`**
for `exposedFork`." `Uwueave/Exits.lean:200-201` — "Unconditional, but **not**
`True`: the row carries `branches_iconfluent`, so nothing is discharged over an
empty premise." `:206-208` — "neither is inhabited by `trivial`." The definition
(`:220-221`) is `IConfluent (S := S → Prop) (fun bs => ∀ s, bs s → I s)`.

Line 493 is draft residue that falsifies the file's own load-bearing "no row is
vacuous" argument.

### E.10 P2 — `Uwueave/SeamAlgebra.lean` contradicts its own headline within eight lines

`:76-79` states the one-line reading — "one coordination point exists iff one of
the fields is coordination-free" — a claim about *all* seams. `:82-90`,
immediately below, concedes it "does **not** rule out every conceivable coarsening
of the pair seam that still reads both fields". The boundary paragraph is right;
the one-liner is what gets quoted.

Separately, `:56-58` states `left_only_seam_iff` dropping a conjunct: the theorem
(`:526-530`) is `… ↔ (SegmentedIConfluent τ IA ∧ IConfluent IB)`; the header omits
the "`τ` is a seam for field A" half. Stated correctly 450 lines later at `:510-512`.

### E.11 P2 — the sort key is four fields in the contract and five in the definition

`Uwueave/Exec.lean:66-67` — "`(lamport, replica, child, dest)` order".
`Uwueave/Exec.lean:238-239` — "(lamport, replica, child, dest, **cite**)", with
`:243-244` warning "⚠ `cite` is a sort key, not decoration ... an order that
ignored it would tie two *distinct* ops". `opLt` (`:251-260`) has five branches;
`rust/src/movelog.rs:98` is right. Stale four-key text also at
`Uwueave/ExecRefine.lean:667` (where `opKey` at `:681-683` is a five-element list)
and `Uwueave/Move.lean:204-206`.

### E.12 P2 — a distinguishability claim false in the degenerate case

`Uwueave/Exec.lean:536-537` — "there is no `n + m` for which the empty response is
a valid one". A canonical v3 request with `n = 0, m = 0` passes the magic guard and
`replay` (`:538-544`) returns `ByteArray.empty` — byte-identical to the refusal;
`rust/src/movelog.rs:334-339` accepts it. Louder version at `Uwueave/Exec.lean:19-20`.

### E.13 P2 — `docs/TRUST.md:96` lists a fixed hazard as live

> ⚠ `rust/build.rs` runs `lake build`; **if that build fails but `Uwueave.c` is
> already on disk, the crate compiles and links the stale C anyway**
> (`build.rs:25-31`) ... a **live integrity hazard**, not a theoretical one

`rust/build.rs:30-38` panics on a failed `lake build`, and `rust/build.rs:25-29`
credits "(Found by the docs/TRUST.md pass, 2026-08-11.)" — the fix landed and its
instigating row was never updated. The row's second half ("`lake build` does not
emit `SeqKernel.c` / `EraKernel.c` until the root module imports them") is stale
too: `Uwueave.lean:24` and `:26` import both.

The same stale note lives in three more files: `rust/src/lib.rs:48-51`, `:66-69`
and `rust/shim.c:36-38`, `:46-49`. Behaviourally harmless — the shim's re-init is
guarded — but three files instruct a workaround for a closed hazard.

(Related: `docs/TRUST.md:91` asserts "`rust/src/lib.rs` and `FORCODEX.md` both
describe a 'three-function shim'". Only `FORCODEX.md:246` does, and the shim has
six functions: `rust/shim.c:25, 63, 75, 81, 97, 113`.)

### E.14 P2 — citations naming a conditional theorem for an unconditional claim

- `Uwueave/ExecRefine.lean:1622-1625` — "no op is applied whose authority the
  substrate does not carry (`Gated.kernel_gate_agrees_gatedOps`)".
  `kernel_gate_agrees_gatedOps` (`Uwueave/Gated.lean:657-661`) requires `WF ρ`,
  `UniqueGrant` **and** `op ∈ ops.toList`. The hypothesis-free theorem that says
  what is claimed is `kernel_admits_only_authorised` (`Uwueave/Gated.lean:646-648`),
  and `:642-645` says so: "**No hypotheses** ... This is the half that matters for
  safety."
- `Uwueave/Exec.lean:172-173` and `:355` cite `kernel_gate_agrees_gatedOps` /
  `kernel_gate_agrees` with neither hypothesis named. `WF` never appears in
  `Uwueave/Exec.lean` at all.

`Uwueave/Gated.lean` is the most scrupulous file in the cluster about its own scope
qualifiers. **The damage is done entirely by its citers.**

### E.15 P2 — two more dropped qualifiers about `Gated.gated_antitone`

- `Uwueave/Exits.lean:437-438` — "`Gated.lean` sells 'late **arrivals** only ever
  remove moves from effect'". `Uwueave/Gated.lean:279-281` says "late
  **revocations**", and `gated_monotone_grants` (`Uwueave/Gated.lean:320-325`)
  proves the grants channel has the opposite sign. False in two of three channels.
- `Uwueave/Repair.lean:429-431` attributes whole-lattice shrinkage to
  `gated_antitone`'s "shape". `Promise.Shrinking` (`Uwueave/Repair.lean:549-550`)
  quantifies over the whole `⊑`; `gated_antitone` (`Uwueave/Gated.lean:285-287`) is
  antitone in the revocation component with grants and log held fixed.

### E.16 P2 — a docstring advertising evidence its theorem does not contain

`Uwueave/KernelCFCS.lean:375-377` claims the fact holds "**through the kernel
encoding on the 2-node base**", citing `Move.absReplayFull_both_statuses`. The
theorem beneath it (`:378-384`) is `⟨move_kernel_cfcs, Move.view_not_stable⟩` —
second conjunct purely about `Move.miniInterp`, with no `absReplay`, no status
block, and no use of the cited lemma (which exists at `Uwueave/Move.lean:319` and
does say what is claimed).

### E.17 P2 — `Repair.fork.relation` and `Repair.weaken.relation` are the same value

`Uwueave/Repair.lean:981` and `:1092` both read `PromiseRelation.changedObservation.comp
PromiseRelation.weakened`. `fork_is_changed_observation_and_weakened` (`:996-1002`)
proves `fork.relation` differs from four other named relations and never notices it
equals `weaken.relation`. `Uwueave/Repair.lean:227-230` says "What weakening costs
is recorded in the **relation**" — but the relation cannot separate the legitimate
fork from the illegitimate weakening.

### E.18 P2 — `Uwueave/Catalog.lean:67-70` claims a ceiling result the tree does not have

"any *ceiling* on a grow-only structure escalates", offered as the reading of `card
≤ k`. Nothing proves `card ≤ k` for `k ≥ 2`; `Ceiling.uniqueness_ceiling`
(`Uwueave/Ceiling.lean:96`) generalizes only to at-most-one-per-selector-key.
Repeated as settled at `Uwueave/Ancestral.lean:829`.

### E.19 P2 — `Uwueave/Choreo.lean`'s `realloc` theorem promises a contrast the file never exhibits

`Uwueave/Choreo.lean:37-38` and `:706` say `realloc_desynced_breaks` is "the write
that moves `σ` and **dies without its barrier**". But `realloc`
(`Uwueave/Choreo.lean:1257`) is described in its own docstring as "A
**barrier-free** re-allocation choreography", there is no barriered version,
`desync` is never applied to it, and `realloc_desynced_breaks` (`:1265`) does not
mention `desync` in its statement. Contrast `loom` (`:985`), which genuinely gets
both halves (`loom_synced_legal` `:998`, `loom_desynced_broken` `:1006`, the latter
actually using `desync loom`).

### E.20 P2 — `PREOSCRIPTING.md` gives two answers about where futures live

`PREOSCRIPTING.md:31-32` files both `delivery-future` and `extension-future` under
`Evidence.lean` as **state** relations. `PREOSCRIPTING.md:174-180` (§5.4) says
`DeliveryFuture` "**cannot** be defined from the state alone", pointing at
`Uwueave/WorldFuture.lean`. One document, two answers, in the section whose whole
thesis is "you cannot write a stability claim without naming which future you
mean" — the rule should now be "which future **and which world**".

### E.21 P2 — `PREOSCRIPTING.md`'s `BudgetVerdict` block does not match the tree

`PREOSCRIPTING.md:99-104` presents a ```lean``` block with `| rejected (floor :
budget < unavoidableFloor)`. `Uwueave/Budget.lean:264` is `| rejected (n : Nat)
(forced : ForcedFloor wl n) (over : budget < n)`. The constructor a reader would
copy does not typecheck, and the omitted field is the `ForcedFloor` **witness** —
the file's stated reason to exist (`Uwueave/Budget.lean:257-259`).

### E.22 P2 — three citations that name something that does not exist

- `Uwueave/Weave.lean:63` — "the `CrossCanonical` failure". Backticked in a header
  where every other backticked name resolves. No `CrossCanonical` declaration
  exists in Lean or Rust; the only other occurrence in the repo is a prose comment
  at `rust/src/causal.rs:261`.
- `Uwueave/Choreo.lean:99-102` claims `Dregg2/Coordination.lean` contains
  `deadlock_freedom`. It contains `deadlock_freedom_by_design`
  (`breadstuffs/metatheory/Dregg2/Coordination.lean:692`). *(Every other Dregg2
  claim in that paragraph checks out exactly — `Projectable`, `projection_sound`
  `:373`, `NoRec` `:435`, and the "first half is `Iff.rfl`" claim, which is
  literally `⟨Iff.rfl, …⟩` at `Dregg2/Spec/Choreography.lean:266`.)*
- `Uwueave/Exec.lean:277` — "the same answer **the visited-set guard** gives."
  There is no visited-set guard; `chainHits` (`:278-285`) is pure fuel.

### E.23 P2 — smaller attribution and scope slips

- `Uwueave/Exits.lean:100-103` credits the fork paper to Schiefer, Litt and
  Jackson; `Uwueave/Exits.lean:485` credits "**Kleppmann's** slogan".
  `docs/BIBLIOGRAPHY.md:845` and `docs/index.html:2008` say Schiefer/Litt/Jackson.
- `Uwueave/MVRegister.lean:15` attributes the undo result to "Kleppmann,
  PaPoC'24"; `Uwueave/Undo.lean:3-8` and `docs/BIBLIOGRAPHY.md:312-313` give it
  correctly as **Stewen & Kleppmann**.
- `Uwueave/MinimalSummary.lean:577-578` — "must distinguish everything, **with no
  hypothesis on the summary at all**". The theorem's second explicit argument is
  `hg : Sufficient g JoinHom.card`. The intended (true) contrast is "no *structural*
  hypothesis"; the header at `:69-71` states it correctly.
- `Uwueave/Evidence.lean:159` — "the price is the same trust in the arbiter that
  **`Era.lean`'s §5.1**" prices. `Era.lean` has no §5.1; §5.1 is the *paper's*, as
  `Uwueave/Era.lean:992` makes clear.
- `Uwueave/Wellformed.lean:233-236` and `:135-137` cite
  `Sequence.wf_unique_anchor_not_iconfluent` as refuting `UniqueAnchor`; the
  theorem (`Uwueave/Sequence.lean:215`) refutes the **conjunction** `WF 5 ∧
  UniqueAnchor` at the fixed bound `n = 5`. The conclusion happens to be true; the
  theorem as cited does not say it.
- `Uwueave/Choreo.lean:917` cites `Catalog.gset_monotone_iconfluent` for the
  genesis conjunct; `Uwueave/Choreo.lean:1086` correctly cites
  `gset_mem_iconfluent` for the identical fact. Two docstrings, one file, two
  theorems for one claim.

---

## §F — Citation integrity

**This is the check that came back best, and it should be said plainly.**

| Surface | Checked | Dangling |
|---|---|---|
| Lean docstrings, cross-module `Module.name` | 756 | **0** |
| `README.md`, `docs/MAP.md`, `docs/TRUST.md`, `PREOSCRIPTING.md`, `docs/BIBLIOGRAPHY.md` — qualified | 28 | **0** |
| same, bare snake_case names | 332 | **0** |
| `docs/index.html` `<code>` theorem names | 280 | **0** |
| `docs/MAP.md` keystone ledger rows resolving to the named module | 126 | **2** (§C.3) |
| Semantic spot-checks (does it *say* what the citer claims) | ~250 | 23 mismatches (§B, §E) |

Every apparent name miss was, on inspection, a structure field, an inductive
constructor, a projection, a C symbol or a Lean builtin. The verified-correct
semantic list is long: all 22 cross-module names in `Uwueave/Exec.lean`'s
claim-discipline block; all four of `Uwueave/Ceiling.lean`'s "verbatim"
restatements, statement-identical to their originals at the originals' own
witnesses; every one of ~35 theorem names in `Uwueave/Fugue.lean`'s "What is
proved" block; ~90 in the CRDT cluster with 80+ exact; `Uwueave/Wellformed.lean`'s
inline restatement of `Sequence.WF` matching `Uwueave/Sequence.lean:137-139`
conjunct for conjunct; `Uwueave/Gluing.lean`'s entire cross-repo archaeology into
`breadstuffs/metatheory`, verbatim right on every checkable line.

The mechanism deserves credit: `rust/src/bin/uwueave-check.rs:10-23` documents a
test suite that resolves every CLI citation "through the file's real namespace
structure to a fully-qualified name — **display names are not keys**", checks
ledger membership **in both directions**, and asserts **verdict polarity** against
the Lean statement as written. It is the only mechanism in the tree that
mechanically couples prose to theorems, and it is what `docs/TRUST.md:68`'s
"Docstring ⟷ theorem" row should be grown from.

**What the count does not measure** is whether the cited theorem says what the
citer claims — and that is where every §E defect lives. **The names are sound; the
readings drift.** §B.3, §C.3, §E.7, §E.14, §E.15, §E.16 and §E.6 are one shape: a
correct name carrying a claim one qualifier wider than the statement.

---

## §G — Orphans and dead ends

**Modules with no in-tree importer other than the aggregator or the gate: 20.**
`Choreo` (root only — §A.1), and nineteen imported solely by `Uwueave/Audit.lean`:
`Budget`, `CausalReach`, `CoordEffect`, `EraKernel`, `Exits`, `Fugue`, `Gluing`,
`KernelCFCS`, `Liveness`, `MergeModel`, `MinimalSummary`, `Nary`, `RALin`,
`Repair`, `ResultStatus`, `SeamColoring`, `Traces`, `Wellformed`, `WorldFuture`.

For a *catalog* this is mostly correct. Three things make it worth stating.

1. **`Uwueave/Audit.lean`'s import list is a hand-maintained perimeter fence** with
   no check that it matches the root. That is an undocumented load-bearing role,
   and §A.1 is what it costs — twice, in one wave.
2. **Four modules are 100% terminal** — every declaration unused outside its own
   file, including the headline theorem: `Uwueave/SeamColoring.lean`
   (`segmented_iff_properColoring` `:340`, and the synthesizers `greedySeamFor`
   `:585` / `synthesizeSeam?` `:614` — while `Cost`, `Exits`, `Budget` and
   `CoordEffect` all still hand-write their seams), `Uwueave/MinimalSummary.lean`,
   `Uwueave/WorldFuture.lean` (`delivery_future_is_not_state_indexed` `:539`,
   `certificate_reuse_is_unsound` `:874` — so nothing in the tree is built on the
   world-indexing correction), and `Uwueave/Gluing.lean` (`guardGluing_iff_iconfluent`,
   `HoleVerdict`, `GluesWithin` — despite `HoleVerdict.toVerdict` `:536` being built
   for a `Spec`/`Tactics` hand-off that does not exist).
3. **P2 — machinery presented as an interface, with one instance: its own.**
   `Repair.Promise`/`Price` (`:181, :520`), `MergeModel.MergeModel`/`IConfluentIn`
   (`:179, :218`), `Budget.Workload`/`Plan` (`:142, :165`),
   `CoordEffect.Profile`/`Strategy` (`:142, :382`), and `Exits.Exit`/`ExitMenu`
   (consumed only by Exits' own three menus). As exhibits, fine; they are presented
   as interfaces.

**Declaration-level:** 1,915 of 2,746 declarations (70%) are referenced by no other
Lean file. Almost all are private helpers and exhibits, which is correct.
Individually notable dead ends:

- `Uwueave/WeaveState.lean:139, :149, :163` — `fst_iconfluent`,
  `at_key_iconfluent`, `keyed_cross_iconfluent`, announced at `:100-109` as generic
  kit ("`Spec.lean`'s lift kit is one rung short for realistic records, so this file
  adds three ∀-general one-line lifts"). None appears in `Spec.lean` or
  `Confluence.lean` where the rest of the lift kit lives, and none is used outside
  `WeaveState.lean` — including by `Uwueave/Wellformed.lean`, the only module that
  imports it, which inlines `Spec.pointsAtExisting_iconfluent` directly at `:297`.
  **General-purpose lifts filed under the demo.**
- `Uwueave/Delta.lean` §6 — `DeltaMutator` (`:330`) and `ofInflationary` (`:352`)
  are consumed only by `Uwueave/Choreo.lean`; everything proved *about* them
  (`mutator_delta_sound` `:367`, `joinAll_deltas_eq_state` `:418`,
  `sufficient_delta_not_least` `:523`, all four instances) has no consumer anywhere.
  **The interface's guarantees never reach the one program that uses the interface.**
- `Uwueave/Ceiling.lean:118-121` `addDelta_uniqueOn` — the general-selector form
  the §2 header promises, declared and never used; its two siblings are consumed.
- `Uwueave/SeamAlgebra.lean:771-773` `linked_flagDay_segmented` — called "the
  file's punchline" at `:769-770`, used by nothing, while `flagDaySegVerdict`
  (`:805-810`) re-derives the same segmentation and *is* what §7 consumes.
- `Uwueave/Cost.lean:381-410` — the whole Event/schedule apparatus supports one
  theorem, `interleaving_stays_in_fiber` (`:410`), advertised as §4's headline at
  `:60-65` and cited by nothing. Same for the entire §7 linked-document apparatus
  (`:626-784`), unconsumed even by `Uwueave/Budget.lean`, which builds
  `unlinkedWorkload` from §7's *unlinked* half (`Budget.lean:386`).
- `Uwueave/Sequence.lean:544, :608` — `linearize_count_one` and
  `linearize_anchor_precedes`, two of the four headline view guarantees advertised
  at `:58-78`, have no consumer.
- `Uwueave/Evidence.lean` — 50 of 104 declarations have no consumer outside the
  file, including `closed_iconfluent` (`:341`), `render_canonical` (`:1073`) and all
  of §11 (`:1099-1164`).
- `Uwueave/ExecRefine.lean` — 111 file-local declarations, 98 theorems, **zero**
  cited in any document.

**Non-orphan, and worth recording: the FFI surface is bijective.** All four
`@[export]`s have exactly one Rust caller and every Rust `extern` resolves to an
`@[export]`: `uwueave_replay_kernel` (`Uwueave/Exec.lean:547` → `rust/shim.c:63` →
`rust/src/ffi.rs:10` → `rust/src/movelog.rs:327`), `uwueave_request_canonical`
(`Exec.lean:561` → `movelog.rs:322`), `uwueave_seq_kernel`
(`Uwueave/SeqKernel.lean:192` → `rust/src/seq.rs:290`), `uwueave_era_resolve`
(`Uwueave/EraKernel.lean:450` → `rust/src/era.rs:296`). **The "authored in Lean,
compiled to C, called from Rust" claim in all four kernel headers is accurate.**

### G.1 OBSERVATION — an axiom claim asserted four times, checked zero

`Uwueave/Exec.lean:105-106`, `Uwueave/ExecRefine.lean:63-64`,
`Uwueave/SeqKernel.lean:64-65` and `Uwueave/EraKernel.lean:73-74` each assert
"axioms ⊆ `{propext, Classical.choice, Quot.sound}`". No `#print axioms` appears
anywhere in `Uwueave/`. The claim is *true* — it is what `#audit_floor` enforces —
but it is stated as a per-file fact four times over, in prose, in the one place
where the tree has a real mechanism and could point at it instead. (The `no sorry /
native_decide / #guard` half is independently verifiable and holds.)

### G.2 OBSERVATION — `Uwueave/ExecRefine.lean` runs §7 → §9 → §8

`:992` (§7), `:1219` (§9), `:1645` (§8). The header's own ordering (`:41`, `:48`)
is the sane one. Navigation only.

---

## §H — What a new reader will get wrong

Three, with the one-line fix each.

**1. "The gate covers everything."** `docs/MAP.md:5-8` says coverage is "total by
construction", `docs/MAP.md:94` says "every row is covered", and `README.md:108`
says `lake build` checks "every proof". A reader will assume a `sorry` anywhere is
a build failure. It is not, for `Uwueave/Choreo.lean` — 53 theorems and four
ledger rows outside the walk — and `lake build` only warns on `sorry` (§A.1).
→ **Fix: `import Uwueave.Choreo` in `Uwueave/Audit.lean`** — then a check that
Audit's import closure covers the root's, so it cannot recur. It already has.

**2. "The map is the module list."** `docs/MAP.md:1` promises "every module". A
reader following `README.md:93` sees 38 of 55 and misses the entire priced-exit /
typed-repair / synthesis spine — fourteen modules with zero presence, including
both files that call themselves the library's capstone (§C.1). They will never
reach `Exits`, `Repair`, `Budget`, `MergeModel`, `WeaveState` or `Wellformed` from
either the map or the import graph, because nothing imports those either (§G).
→ **Fix: change `docs/MAP.md:1`'s subtitle to say what it covers, and add a
one-line "wave 9–13 modules, indexed in `PREOSCRIPTING.md` §10" pointer** — then
backfill the rows.

**3. "Terminal means terminal."** A reader who opens `docs/MAP.md` before
`docs/TRUST.md` — the order `README.md:93-100` puts them in — learns that the C
backend is "the terminal TCB, named, not undone work" (`docs/MAP.md:61`), and
`Uwueave/Gated.lean:150` confirms it with ⟨TERMINAL for this repo⟩. They will never
discover that this is the repo's most thoroughly retracted claim, with nine named
next steps waiting at `docs/TRUST.md:88-97`.
→ **Fix: replace `docs/MAP.md:61`'s last clause with "C-backend trust — nine
decomposed obligations, `docs/TRUST.md` Ledger 2", and requalify
`Uwueave/Gated.lean:150`.**

*Runner-up, and the one that would embarrass us fastest in public: a reader who
takes `Uwueave/Exits.lean` at its word learns that arbitration costs **zero
meetings** (`:78, :235`) — a claim the tree retracts in four other files and prices
as a trusted announcement plus a rollback window (`Uwueave/Repair.lean:369-376`).*

---

## Prioritized fix list

**P0 — this week**

1. `import Uwueave.Choreo` in `Uwueave/Audit.lean`; then make the gate assert its
   import closure covers the root's. The fence was hand-repaired mid-audit and
   still missed Choreo; only the structural check ends this. (§A.1)
2. Rewrite `docs/MAP.md:61` — four defects in one sentence. (§B.1)
3. Decide `FORCODEX.md` / `CODEXHELP.md`: track them, or move §0.5, §4.7 and §0.1
   into `docs/`. (§B.2)

**P1 — before anyone new reads this**

4. **One forward sentence per predecessor** — `Holes`→`Evidence`,
   `Evidence`→`WorldFuture`, `JoinHom`→`MinimalSummary`, `Exits`→`Repair`,
   `Holes`→`Choreo`. Closes a whole class for five lines of prose. (§D.1)
5. `Uwueave/ORMap.lean:53-55`: apply the reachability retraction that landed in
   `ORSet` and `CausalReach`. The MAP ledger is currently reading around it. (§B.5)
6. Sweep "meetings" out of `Uwueave/Exits.lean` (11 sites). (§E.5)
7. Requalify `Uwueave/Gated.lean:150` and `Uwueave/Exec.lean:160` against
   `docs/TRUST.md` Ledger 2. (§B.3, §B.4)
8. `docs/MAP.md`: retitle, add the sixteen missing rows, fix the three bad ledger
   claims at `:69`, `:174`, `:175`. (§C.1, §C.2, §C.3)
9. Delete `Uwueave/ExecRefine.lean:996-999`'s last sentence; §8 refutes it. (§E.1)
10. `Uwueave/Gated.lean:117-127`: the item is done — remove it, per the file's own
    rule at `:69-72`. (§E.3)
11. Add `departed_rejoins_unchecked` / `promote_admits_nonmember` to
    `Uwueave/EraKernel.lean`'s non-claims list. (§E.4)
12. `Uwueave/Holes.lean:92, :537` — the LoRe retraction never arrived. (§B.6)
13. `Uwueave/Evidence.lean:786` — mark the sentence `WorldFuture.lean:573`
    refutes. (§B.7)
14. `Uwueave/WorldFuture.lean:124-130, :713-715, :775-778` — the completeness gap is
    a `RosterKnown` failure, not a wellformedness failure. Four docstrings say the
    wrong thing about the file's own theorem. (§E.7)
15. `Uwueave/Exits.lean` §4.8: restore the quantifier and stop calling the ancestral
    test a `strongerMetadata` result. (§E.6)
16. Reconcile `Repair.Promise`'s mandatory `mergeState` with `MergeModel.lean`'s
    thesis, or state in both files which one governs. (§D.3)
17. Rename one of the two `loomVerdict`s, or relate them the way
    `toSpecVerdict_isFree` relates the two `Verdict`s. (§D.4)
18. Either make `Uwueave/Spec.lean:375-380` use the §2 verdict values its docstring
    claims, or change the docstring — and decide whether the four unused lift
    combinators are DSL surface or dead code. (§E.2)

**P2 — a tidying pass**

19. Sort key four → five: `Uwueave/Exec.lean:66-67`, `Uwueave/ExecRefine.lean:667`,
    `Uwueave/Move.lean:204-206`. (§E.11)
20. Citation qualifiers: `Uwueave/ExecRefine.lean:1622-1625` →
    `kernel_admits_only_authorised`; `Uwueave/Exec.lean:172-173`, `:355` → name `WF`
    + `UniqueGrant`; `Uwueave/Exits.lean:437-438` and `Uwueave/Repair.lean:429-431` →
    "revocations", not "arrivals". (§E.14, §E.15)
21. Refresh `docs/TRUST.md:91`, `:96`; drop the stale build notes in
    `rust/src/lib.rs:48-51`, `:66-69` and `rust/shim.c:36-38`, `:46-49`. (§E.13)
22. `Uwueave/Exits.lean:493` (the `True` that is not `True`); `:100-103` vs `:485`
    (two sets of authors). (§E.9, §E.23)
23. `Uwueave/Repair.lean`: `fork.relation` = `weaken.relation`. (§E.17)
24. Disclose the `LinkedWF` collision at `Uwueave/Cost.lean:625`, and say which
    document `:773-778`'s correction is about. (§D.6)
25. De-privatize `Uwueave/ExecRefine.lean:1660-1698` and delete EraKernel's three
    copies — or say at `Uwueave/EraKernel.lean:481-485` why the copy is forced.
    Hoist `sublist_flatMap_of_mem` out of `Sequence`/`SeqKernel`. (§D.8, §D.9)
26. `Uwueave/Liveness.lean:134` — rename, or qualify the `open`. (§D.7)
27. Update the "four costumes" count at `Uwueave/Ceiling.lean:4-11`; remove "the
    file says so plainly" from `Uwueave/Holes.lean:756-757`; drop the dead pin
    reference at `Uwueave/Ceiling.lean:34-36`. (§B.9, §B.11)
28. Backport `Necessity` and `Nary` into `Uwueave/Confluence.lean:23-25`, `:132-135`.
    (§B.8)
29. `Uwueave/Confluence.lean:174-177` and `Uwueave/Spec.lean:141-142`: cite a module
    that actually holds a cross-field refutation. (§E.8)
30. `Uwueave/SeamAlgebra.lean:76-79` and `:56-58` — make the headline carry its own
    boundary; restore the dropped conjunct. (§E.10)
31. `Uwueave/Catalog.lean:67-70`, `Uwueave/Ancestral.lean:829`: `card ≤ k` for `k ≥
    2` is not proved anywhere. (§E.18)
32. `Uwueave/Seams.lean:114-117`, `:221-223` — correction 1 never landed. (§B.10)
33. `Uwueave/KernelCFCS.lean:375-377`: use `Move.absReplayFull_both_statuses` in the
    statement or stop advertising it. (§E.16)
34. `PREOSCRIPTING.md:99-104` (`BudgetVerdict`), `:31-32` vs `:174-180` (which file
    holds the futures). (§E.20, §E.21)
35. Names that do not exist: `CrossCanonical` (`Uwueave/Weave.lean:63`),
    `deadlock_freedom` (`Uwueave/Choreo.lean:101`), the visited-set guard
    (`Uwueave/Exec.lean:277`). (§E.22)
36. `Uwueave/Choreo.lean:1257-1271` — either build the barriered `realloc` the name
    promises, or rename the theorem. (§E.19)
37. `Uwueave/MergeModel.lean`'s eight `ExecRefine.absReplay_*` docstring citations
    name a namespace that does not exist; `docs/MAP.md:51` omits ORSet §3.
    (§C.4, §C.5)
38. Namespace hygiene: `Uwueave/MinimalSummary.lean` and `Uwueave/JoinHom.lean`
    scatter general theory between bare `Uwueave` and their own namespaces
    inconsistently; `Uwueave.JoinHom` is both a definition and a namespace. (§D.10)
39. `Uwueave/WeaveState.lean:496` — the README does not point at that table; and
    `:139, :149, :163`'s three ∀-general lifts belong in `Spec.lean`. (§C.6, §G)
40. "*The* export surface" is four symbols: `Uwueave/SeqKernel.lean:112-113`,
    `Uwueave/EraKernel.lean:105-106`, `Uwueave/Fugue.lean:169-171`. (§D.11)

---

## What did not go wrong, and is worth knowing

An audit that finds nothing has failed. So has one that reports only failures.

- **One judgement, defined once.** `IConfluent` at `Uwueave/Confluence.lean:129`,
  `MergeState` at `:49`, `Invariant` at `:120`. Fifty-eight modules, not one private
  redefinition. This is the single most likely thing to have gone wrong in a
  forty-lane build, and it did not.
- **756 cross-module citations, zero dangling names**, and ~250 checked
  semantically with the large majority exact. (§F)
- **A bijective FFI surface**, with "authored in Lean" true at all four entry
  points. (§G)
- **The CLI mechanically couples prose to theorems** — namespace-resolved,
  ledger-checked in both directions, polarity-asserted
  (`rust/src/bin/uwueave-check.rs:10-23`). The one place a docstring cannot silently
  outrun its receipt.
- **Four paragraphs that are the fix for whole sections of this audit:**
  - `Uwueave/Repair.lean:25-37` — names its sibling, the shape difference, the
    theorem that separates them, and that it does not import it. Six pages of §D
    would not exist if every file did that.
  - `Uwueave/Choreo.lean:812/846/872` — a deliberate second `Verdict`, announced,
    and **tied to the first by a theorem** (`toSpecVerdict_isFree`). The model for
    §D.4.
  - `Uwueave/Wellformed.lean:77-84, :171-204` — builds on `WeaveState` by
    delegating rather than re-modelling, labels every restatement, and *reuses* the
    predecessor's witnesses. The one place a vocabulary appears twice and the second
    copy is provably the first.
  - `Uwueave/Gated.lean:642-648` — splits its own theorem into the hypothesis-free
    half and the conditional half and says which matters for safety. The model for
    §E.14's fix, written by the file that gets cited wrongly.
- **`Uwueave/Exits.lean:981-987`** is how a scope drop should be handled: it drops
  the `WF 9` conjunct from `Authority.sole_admin_not_iconfluent`, flags that it did,
  and **proves the reason** (`arbKeep_can_orphan`, `:1093`).
- **The retractions that *did* propagate.** All three `Holes.lean` retractions
  (monotone ≠ join-preserving; gossip under finite closed scope; freeze/cut/arbiter
  — checked against every `.md` and every `.lean`, no un-retracted survivor); the
  scalar coordination grade at `Uwueave/CoordEffect.lean:5-12`; Choreo's
  occupied-junction at `:61-63` and `docs/MAP.md:71`; three of four ERA corrections
  from `Era.lean` back into `Seams.lean` §1, near-verbatim.

Most corrections landed where the claim was made. The ones still walking around are
**the C backend**, **meetings**, **ORMap's reachability**, and **LoRe** — and three
of those four are walking around in a front-door document.

---

*Written by a lane that read the whole tree and none of it twice. Every claim above
is cited; if a citation is wrong, that is the good kind of wrong — say so, and it
moves a row.*

⚑ *Standing caution, because this file is exactly the kind of document that grows
the defect it audits: **`docs/COHERENCE.md` has no mechanism.** It is a reading,
dated, of a tree that moved four modules while it was being written, and its counts
will rot on the same schedule every count in `docs/MAP.md` rotted on —
`Uwueave/Audit.lean:31` predicted this in advance. The parts worth keeping are the
mechanisms: the gate-equals-root check in fix 1, and the polarity suite in
`uwueave-check` that fix 8 should be modelled on. The prose is a snapshot.*
