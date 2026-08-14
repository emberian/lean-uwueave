# Runtime architecture and durability contract

This document is the implementation map for turning Uwueave's proved kernels
into a durable, authenticated runtime. It describes what is present now, what
is only a Lean contract, and what must be built next. It deliberately keeps
four properties separate:

- **Authenticity:** which key signed these exact bytes?
- **Authorization:** may that authenticated issuer perform this action in the
  referenced document state?
- **Durability:** which accepted records are observed after reopen?
- **Liveness:** will an eligible request eventually be admitted, executed,
  stored, and replicated?

No checksum establishes authenticity. No signature establishes authorization
or durability. No successful `sync_*` call is a filesystem crash proof. None
of the current Lean files contains an EUF-CMA reduction or a liveness theorem.

Status words used below:

- **Implemented** means code exists in this repository and is exercised at
  its stated boundary.
- **Contract** means Lean specifies the obligation, but the host does not yet
  refine or instantiate it end to end.
- **Next** means proposed architecture, not a compatibility promise.

## 1. What ships today: legacy FORMAT-v3 and one authenticated move path

The original public Rust path remains deterministic but unauthenticated:

1. `Weave::record_membership` accepts a bare `EraEvent` into
   `EraGroup::record`. `Weave::record_cut` similarly records an unsigned cut.
2. `Weave::move_node` performs a local ERA-role check, constructs a `MoveOp`
   whose `replica` equals the supplied actor, cites founding universal grant
   `1`, and calls `MoveLog::record`.
3. `Weave::view` resolves membership with `EraGroup::resolve`, role-filters the
   stored move set, and asks `MoveLog::replay_traced` for the derived move
   result.
4. `MoveLog::replay_traced` sends typed base, move, grant, and revocation lanes
   through `rust/src/ffi.rs::encode_replay_request`. The exported Lean adapter
   `Uwueave.Exec.encodeRequestKernel` calls the canonical
   `Uwueave.Exec.encodeRequest`; Rust does not independently spell FORMAT v3.
5. `Uwueave.Exec.replay` applies the grant/revocation gate, total order, and
   cycle-avoiding fold, then returns overrides plus one status per submitted
   move. Rust converts those derived values into `WeaveView`.

The exact implementation surfaces are `rust/src/weave.rs`,
`rust/src/movelog.rs`, `rust/src/ffi.rs`, `Uwueave/Exec.lean`, and
`Uwueave/Gated.lean`. FORMAT v3 is the word format documented by
`Uwueave.Exec.magicV3`, `requestWords`, `encodeRequest`, and `replay`.
Requests contain a structural base, `Exec.Op` records, grants, and
revocations. Move records contain `(lamport, replica, child, dest, cite)`.
They do **not** contain a document id, genesis id, operation id, nonce, key
epoch, signature algorithm, signature, or commitment to the full substrate
from which the caller selected its lanes.

Important gaps in that legacy path:

- `MoveLog::record`, `MoveLog::issue`, and `MoveLog::revoke` remain public
  direct mutation APIs. Merge imports structurally valid set members; it does
  not authenticate them.
- `replica` is an asserted numeric actor, not a verified identity. The local
  `Weave::check` role decision is not proof that the bytes later reaching the
  kernel were signed by that actor.
- `Weave::new` installs `Grant::universal(1)`. Within `Weave`, the FORMAT-v3
  authority gate is therefore deliberately permissive and the independent
  ERA-role filter supplies the operative move policy.
- The kernel judges only the grants and revocations marshalled into a request.
  FORMAT v3 does not bind a request to an authoritative substrate commitment.
- Grant scope is a dense child-index ceiling. It is not yet a stable durable
  capability over content identities.
- Rust membership resolution calls `EraGroup::resolve`; the invitation/life
  discipline modeled by `Uwueave.Era.resolveGated` is not this public path.
- FORMAT v3 refuses a bad magic with an empty response. A canonical request
  with no nodes and no operations also has an empty response, so that one
  shape needs out-of-band distinction.

`Uwueave/Authenticity.lean` and `Uwueave/AuthenticatedAdmission.lean` provide
model-level signing, genuine-issuance, event transport, and grant-holder
composition. They explicitly do not authenticate the shipping FORMAT-v3/FFI
path. Their `SignatureScheme`/`AuthenticIssuer` premises are not an EUF-CMA
proof for a deployed primitive.

Separately, `AuthenticatedRuntime` now exposes the raw kind-3 move path detailed
in §5.2. It verifies and persists one context-bound move before committing it
to its owned execution state. That additive wrapper does not authenticate or
remove the public legacy `Weave`, `MoveLog`, grant/revocation, membership, ERA,
causal, sequence, or other mutation surfaces. A deployment must expose only the
appropriate wrapper and policies; the presence of the authenticated move path
does not relabel existing data or APIs.

### 1.1 Native closure and initialization

**Implemented as a fail-closed build control, not a compiler proof.**
`Uwueave/RuntimeInit.lean` is a deliberately data-free native root. It directly
imports exactly the five exported-kernel modules:

- `Uwueave.Exec`
- `Uwueave.SeqKernel`
- `Uwueave.EraKernel`
- `Uwueave.Preo.ArtifactJournalKernel`
- `Uwueave.RuntimeAuthV4Kernel` (which imports `RuntimeAuthV4`)

That import list owns two decisions together: the one generated initializer the
C shim calls and the transitive native-object closure the Rust crate links.
`rust/build.rs` does not scan `.lake/build/ir` or compile whatever C happens to
be present. It requires a full `lake build`, queries the exact RuntimeInit C
target, reads and validates Lake's generated setup description, and asks Lake
for one native object for every module in that declared closure. The build
rejects a wrong setup identity/schema, plugins/dynamic libraries it has no
policy for, missing required kernels, foreign or duplicate modules, escaped or
mismatched paths, duplicate object results, and cross-compilation. Native macOS
and Linux are the only admitted targets.

Before archiving, each Lake object is read through a stability check, retained
as bytes, and copied to a stable staging path. `cc` compiles exactly one C
source, `shim.c`, and archives that object with only the staged Lake objects.
The postcondition lists the archive, requires exactly one shim member plus the
complete unique Lake member set, extracts every Lake member, and compares its
bytes to the staged snapshot. A final `lake --no-build build` and exact no-build
queries must return the same RuntimeInit target and object paths; the setup,
closure, every object, every Lean source, `Uwueave.lean`, Lake/toolchain files,
shim, build script, Cargo manifest, and lockfile must also be unchanged.

`rust/shim.c` first calls `lean_initialize_runtime_module`, then only
`initialize_uwueave_Uwueave_RuntimeInit(1)`. Rust serializes that process-global
initialization with `Once`; failure aborts rather than exposing a partly
initialized runtime. The current native-closure gate observes 15 Lake-owned
objects (1,049,544 bytes before archiving) and 16 archive members including
the shim (1,249,984 bytes including the archive index; SHA-256
`1b0deb1bcfcaa79f66ba7f880a340605a9055e655820888a2ebcb6110b528d8e`).

This closes stale, extra, missing, and mixed-generation object selection plus
initializer drift. It does **not** prove Lean's IR-to-C lowering, either native
compiler or the linker, C/Rust/Lean ABI agreement, reference ownership, runtime
behavior, or filesystem semantics. Those remain the separate execution-TCB
rows in `docs/TRUST.md`.

## 2. The pure-Rust persistence and inspection surfaces

The runtime now has five deliberately different pure-Rust journal domains under
`rust/src/persistence/`. They share a private physical record mechanism, not a
semantic wire format.

### 2.1 ArtifactJournal: physical storage for exact logical artifacts

**Implemented.** `rust/src/persistence/artifact.rs::ArtifactJournal` stores
one unchanged canonical Preoscript artifact frame per physical record. A
logical artifact frame is exactly
`Uwueave.Preo.ArtifactDurable.projectionBytes`:

```text
D5 4A 02 A1 (00 payload-byte)* 01
```

The logical import/export stream is only the concatenation of those frames.
Use `decode_artifact_frame_stream` and `encode_artifact_frame_stream`; the
physical journal file itself is **not** that stream and must not be handed to
an artifact decoder.

`ArtifactFrame::new` checks the v2 outer envelope in Rust and then calls the
narrow Lean export
`Uwueave.Preo.ArtifactJournalKernel.validateOneKernel` through
`rust/src/ffi.rs::preo_artifact_v2_validate_one`. Rust does not reconstruct
`ArtifactEncoding` and does not own a second semantic decoder. Before that FFI
call, the host enforces the separate 1 MiB
`MAX_ARTIFACT_FRAME_BYTES` ceiling; this limits the `ByteArray`-to-list
allocation in the current Lean validator independently of the physical-record
limit.

The corresponding Lean contract is
`Uwueave/Preo/ArtifactJournalKernel.lean`:

- `validateOne` accepts exactly one canonical frame.
- `scan` returns `Record` values with exact half-open byte offsets and a
  `Stop` of clean EOF, torn final suffix, or corruption.
- `scan_encodeJournal`, `encodeJournal_append`, `scan_append`, and
  `scan_stops_at_first_refusal` state canonical scan and append behavior.
- `PhysicalRecord.Valid` parameterizes the outer digest/version/domain
  obligation without claiming that Lean implements BLAKE3 or a filesystem.

The repository now also has an explicit real-byte producer rather than only
handwritten frame fixtures. `Uwueave.Preo.ArtifactEmit` names the generated
`SemanticExport.ArtifactDurableBytes` and the complete Projection-V2 example.
Its executable implementation uses a stack-safe encoder proved equal to
`ArtifactDurable.projectionBytes`; importing the module performs no I/O.
`tools/uwueave-preo-artifact` invokes `ArtifactEmitMain` only on request and
writes the selected bytes to stdout or one caller-selected path.

`rust/tests/artifact_emit.rs` crosses the resulting host boundary end to end:
both real artifacts pass `ArtifactFrame::new`, are appended under `SyncData`,
then survive close/reopen with exact bytes and pinned BLAKE3 observations. The
same test refuses a semantic mutation, a torn frame, and a wrong version. This
is stronger execution evidence than a reconstructed fixture, but the boundary
remains exact: the Lean equality covers the logical bytes; Rust tests the
command, validator, journal, and reopen behavior; neither proves stdout,
`writeBinFile`, `sync_data`, or the host filesystem correct under a crash.

The checked V3 path is exercised separately by `Uwueave.Preo.Quickstart`.
Unlike a row fixture, it begins with one custom `AppState`, an explicit
`State → Expr.Env` projection, and an inferred typed query; binds the result to
one named world future and exact-index certificate; consumes the native
protocol/planning/budget surfaces; and constructs V3 query, result, and
certificate rows only from proof-indexed builders. Its stack-safe executable
frame is proved equal to `ArtifactV3Durable.projectionBytes`; the gate writes
and byte-reopens the exact **71,011-byte** frame and the exact **142,022-byte**
two-frame logical journal. Wrong projection, future, certificate, plan, and
world fixtures must all fail to compile.

`ObservedBoundResult.attachAtWorld` adds the deployment-facing premise without
pretending to observe a deployment. The caller supplies one exact
`ObservationBoundary.Authentic` proof, membership in a separately authored
running reach, membership in the binding's authored world reach, and the exact
world-indexed certificate. `preo_export_v3` accepts only that wrapper plus the
exact checked plan, budget, query, future, world, branch, command-work limit,
and validator config. It computes result status/effect/visibility/disclosure
and certificate rows through checked builders, then commits the complete prefix
only after V3 validation. The validator now bounds stable-ID magnitude and hole
path depth and requires strictly increasing world/query/result/certificate
registries in addition to its existing row/reference/resource checks.

The dedicated acceptance runner has three green fixtures and fifteen red
command cases. It rejects a bare certified report and a structural lookalike,
forged state, out-of-running reach, wrong projection/future/world/certificate/
plan, both command and validator resource ceilings, custom axiom, `sorryAx`,
and Lean-4.30 `native_decide`; a guarded late refusal proves complete prefix
absence and successful same-name reuse. Its positive generated prefix audits
48 constants on the repository trust floor. This establishes elaboration
honesty, not authenticity of any host observation. Nor is acceptance a
performance claim: the command's serialized N=16 benchmark currently measures
6.706 MiB incremental peak RSS per item, above the existing 4 MiB/item ceiling.

### 2.2 Bounded diagnostic-only artifact inspection

**Implemented as pure inspection, not authority.**
`ArtifactInspectionV1.inspectFrame` and `inspectJournal` accept canonical
logical V2/V3 frames, version-dispatch through the existing Lean codecs, run
the bounded Projection V2/V3 validators, and return deterministic JSON with
schema `uwueave/preo-inspection/v1` and authority `diagnostic-only`. Caller
bounds cover input bytes (default 1 MiB), records (64), rows (256), and
references per row (256). A torn/corrupt suffix, wrong version, resource excess,
or structurally invalid decoded artifact refuses the whole request; no partial
JSON or checked source is reconstructed.

`tools/uwueave-preo-inspect` invokes `ArtifactInspectionMain` explicitly in
frame or logical-journal mode. The thin Rust wrapper may extract exact logical
frame bodies from an `ArtifactJournal`, but it has no semantic decoder. The
proof root and `Audit` import only `ArtifactInspectionV1` and `ArtifactEmit`:
`ArtifactInspectionMain` and `ArtifactEmitMain` are separate executable build
boundaries with root-level `main` declarations and must not be aggregated into
one proof module.

### 2.3 DocumentJournal: the typed MoveLog journal

**Implemented, with intentionally narrow coverage.**
`rust/src/persistence/document.rs::DocumentJournal` stores canonical typed
`DocumentEntry` records:

- `Move(MoveOp)`
- `Grant(Grant)`
- `Revocation(u64)`
- `Checkpoint { covers_through, log }`

Open validates every checksummed body, decodes it canonically, and rebuilds
state by calling the public `MoveLog::record`, `issue`, and `revoke` APIs. A
checkpoint must equal the exact mutation prefix it claims to cover.
`replay_into` may start a `DocumentReplay` consumer at the newest validated
checkpoint and then feed the remaining mutations. `recovered_move_log` is the
authoritative substrate from which `replay` or `replay_traced` derives a view.

This is a storage identity, not a user identity. These entries are still
unauthenticated legacy/runtime inputs. Causal nodes, sequence edits, ERA
events/cuts, key changes, bookmarks, activation, spend, and seam changes do
not yet have `DocumentEntry` variants.

### 2.4 HistoryJournal: causally closed explicit-id events

**Implemented, with identity deliberately separated from authenticity.**
`rust/src/persistence/history.rs::HistoryJournal` stores events containing one
application-assigned 32-byte ID, a strictly increasing (therefore duplicate-
free and canonical) parent list, and opaque payload bytes. A parent must
already occur in the accepted prefix before its child can be appended. The
implementation keeps no hidden out-of-order buffer, so every accepted physical
prefix is causally closed.

An exact retry is a no-write idempotent success. A self-parent, reordered or
duplicate parents, a missing parent, malformed bytes, or the same ID with
different parents/payload is refused. Recovery rechecks those conditions from
the complete checksummed prefix, and independent journals receiving a causally
valid event set in different topological orders converge to the same
`id → event` map. The physical marker/domain are `UWHIST01` and
`uwueave.history-journal.v1`.

The Lean `PersistentHistoryRuntime` layer separately proves finite causal
append, exact checkpoint/suffix replay, and event-set convergence. No theorem
yet refines the Rust host bytes or filesystem observations to that model. The
32-byte host ID is a uniqueness claim, not a signature or proved content hash;
a deployment needing unforgeable history identity must authenticate or
content-address a canonical event representation before admission.

### 2.5 Buffered history delivery: two intentionally different authorities

**Implemented with an explicit non-refinement boundary.** Lean
`HistoryRuntime.DeliveryState` separates causally materialized events from an
explicit pending list and written capacity. `DeliveryValid` is exactly
`pending.length ≤ capacity`; empty is valid, drain never increases the pending
length, and every successful `receive`/`receiveAll` transition preserves the
bound. Receive is retry-idempotent across both stores, collision-refuses one ID
with different event content, rejects self/duplicate parents, buffers a
missing-parent event only when capacity permits, and deterministically scans
finite pending layers after a ready append. A six-event fixture—root,
left/right, two sibling merges, and one tip—settles both causal and fully
reversed arrival orders with capacity five and proves the same event-set view.

`PersistentHistoryRuntime.deliverySchema` makes the arrival sequence
authoritative, including arrivals still pending in `DeliveryState`. Its
coherence relation states that an accepted arrival occurs exactly in the
materialized or pending side; checkpoint/suffix replay can therefore retain a
buffered prefix and later settle it.

Rust's `BufferedHistoryJournal` has a different contract. It wraps the durable
causally closed `HistoryJournal`, keeps missing-parent events in a bounded
in-memory `BTreeMap`, and appends only ready events. Draining uses deterministic
ID order; retries, same-ID/different-content collisions, and buffer-full are
explicit. The buffer is deliberately **volatile**: reopen reconstructs the
checksummed causal prefix and starts with no pending entries, which the focused
test asserts.

`HistoryArrivalJournal` is the separate durable-arrival endpoint. It appends
every canonical arrival before classifying it as materialized or pending,
records the written capacity in each record, and supports exact state-digest
checkpoints over accepted/materialized/pending maps. Reopen replays the exact
arrival sequence, validates capacity and checkpoints, restores pending entries,
and later drains them deterministically when parents arrive. Exact retry is
no-write; collision, capacity, torn/corrupt/version, and checkpoint mismatch
refusals preserve the prior reopenable prefix. The focused acceptance suffix
runs all four recovery/refusal tests. This is a tested host endpoint, not yet a
Lean↔Rust refinement or filesystem theorem.

The remaining gaps are exact: Lean requires only duplicate-free parent lists,
where Rust requires strictly increasing canonical parent IDs; application IDs
are equality keys, not authentication; there is no Lean↔Rust event codec or
host-byte refinement; and no theorem covers filesystem or power-loss behavior.
The logical callbacks now name exact receive/reopen replay obligations, but no
byte codec theorem connects them to `HistoryArrivalJournal`. Parent-order and
authentication differences remain as below.

### 2.6 Shared physical record format

**Implemented.** `rust/src/persistence/record.rs::RawJournal` wraps each
semantic body in:

```text
8-byte store marker
u64 little-endian contiguous sequence
u64 little-endian body length
32-byte domain-separated BLAKE3 header checksum
body bytes
32-byte domain-separated BLAKE3 body checksum
```

The artifact marker/domain are `UWARJ001` and
`uwueave.artifact-journal.v1`; the document marker/domain are `UWDJRN01` and
`uwueave.document-journal.v1`; the history marker/domain are `UWHIST01` and
`uwueave.history-journal.v1`. The BLAKE3 dependency is an integrity control,
not an authenticity claim or a proof that corruption is impossible.

The sequence-addressed append API has useful retry semantics:

- appending at the next sequence returns `AppendStatus::Appended`;
- retrying the same sequence with byte-identical content returns
  `AppendStatus::AlreadyPresent`;
- different bytes at an existing sequence are `SequenceConflict`;
- skipping a sequence is `SequenceGap`.

After an append or sync I/O error the handle is poisoned because write outcome
is uncertain. The caller must close, reopen, inspect the recovered sequence,
and retry the same sequence and bytes. A successful append of one record is
not an atomic multi-record batch facility.

Coverage lives in `rust/tests/persistence.rs`, including exact logical
artifact streams, all configured sync policies, every strict final physical
record truncation, corrupt middle records, allocation limits, writer locking,
idempotent sequence retries, typed MoveLog reconstruction, checkpoint-prefix
validation, and separation of physical corruption from malformed typed
entries. These are implementation and fault-injection tests, not hardware
failure proofs.

## 3. Logical records, physical bytes, and authority

These layers must remain explicit:

| Layer | Bytes or values | Authority |
| --- | --- | --- |
| Artifact logical stream | Exact concatenation of `projectionBytes`, including bytes selected by the explicit Lean artifact emitter | Canonical compiled artifact records |
| Artifact physical file | Checksummed `UWARJ001` records containing unchanged logical frames | Physical recovery evidence only |
| Document logical journal | Ordered typed `DocumentEntry` values | Presently MoveLog mutations; checkpoint is validated acceleration |
| Document physical file | Checksummed `UWDJRN01` records containing canonical entry bodies | Physical recovery evidence only |
| History logical journal | Canonical explicit-id events whose parents are already accepted | Causally closed host prefix; IDs remain unauthenticated |
| History physical file | Checksummed `UWHIST01` records containing canonical event bodies | Physical recovery evidence only |
| FORMAT v3 request | Lean-owned execution request bytes | Derived execution input, never journal authority |
| FORMAT v4 legacy request | Canonical kind-1 signed-request bytes from `RuntimeAuthV4` | Syntax compatibility/audit path; not context-bound admission |
| FORMAT v4 context request | Canonical kind-3 bytes and exact kind-4 projection from `RuntimeAuthV4Kernel` | Implemented admission-input boundary; later runtime stages remain separate |
| Derived views/statuses | replay outputs, roles, trees, traces | Cache/output only; never recovery authority |

Authoritative recovery starts from accepted operation/event records in order.
A view, trace, index, materialized tree, or role map is disposable. A
checkpoint is also not independent authority: it is usable only after exact
prefix validation. In the current `DocumentJournal`, a checkpoint is stored
as a physical typed record and contains complete MoveLog sets, but it does not
license state different from the preceding mutation prefix.

The pure Lean model `Uwueave/PersistentRuntime.lean` makes this distinction
precise:

- `RecordSchema.step` is deterministic admission and transition.
- `Cursor.accepted` retains complete chronological records.
- `applyRecord` makes an exact record retry a no-op and refuses a different
  record that reuses an accepted nonce.
- `replay` refuses at the first invalid record; it never skips a bad middle.
- `CheckedBatch` separates semantic admission from storage atomicity.
- `AtomicBatchObservation` permits only `old` or `old ++ batch` after an
  unsuccessful/crash-ambiguous attempt; `SuccessfulBatchObservation` permits
  only `old ++ batch` after reported success.
- `CheckpointValid`, `validateCheckpoint`, and
  `checkpoint_suffix_replay_equiv` require exact-prefix reconstruction before
  suffix replay.
- `RuntimeImage` and `reopenImage_cache_irrelevant` exclude caches from
  recovery authority.

This is currently a **contract**, not a refinement theorem for
`RawJournal`. In particular, the standard-file journal appends one physical
record at a time and does not yet instantiate the multi-record
`AtomicBatchObservation` premise.

## 4. Locking, sync, torn writes, and corruption

The runtime's physical assumptions are deliberately modest:

- Open obtains `File::try_lock` as an exclusive advisory writer lock. Correct
  exclusion depends on the operating system and every writer honoring the
  same locking protocol. This is not distributed consensus.
- `JournalOptions::default` refuses a torn tail, requests `SyncData`, and caps
  a physical body at 64 MiB.
- Artifact validation has a stricter fixed 1 MiB pre-FFI frame ceiling. Neither
  limit currently bounds total journal bytes or record count, and open still
  materializes the complete physical file; streaming and total-resource limits
  remain deployment work.
- `TornTailPolicy::Truncate` is opt-in. It truncates only one syntactically
  plausible incomplete final physical record to the last complete boundary,
  then applies the configured sync policy.
- A bad marker, non-contiguous sequence, invalid header checksum, invalid body
  checksum, oversized length, malformed typed body, or invalid checkpoint is
  corruption and is refused. Recovery never scans past it and never silently
  truncates a complete corrupt record, even at EOF.
- `SyncPolicy::{Buffered, Flush, SyncData, SyncAll}` has exactly the meaning of
  the corresponding Rust `std::fs::File` operations. Creating a new file under
  `SyncAll` also syncs its parent directory, including the `.` parent of a bare
  relative path. Directory syncing is platform-shaped and currently tested on
  Unix; Windows portability remains open. Actual persistence depends on the
  filesystem, mount options, operating system, storage device, and failure
  model.
- Journal paths are caller-trusted. The implementation has no `O_NOFOLLOW`
  policy, regular-file/permission enforcement, or defense against pathname
  replacement by a non-cooperating process.

The intended deployment premise is: after reopen, the implementation exposes
only a validated complete prefix, with an explicitly chosen policy for a torn
final record. The repository does not prove that every real crash produces
such an observation. Checksums detect the modeled corruptions with test
evidence; they do not make undetected corruption impossible.

The executable emitter has the same filesystem boundary. Path mode calls
Lean's ordinary `IO.FS.writeBinFile`; it does not write through `RawJournal`,
request an atomic rename, sync the file or its parent, enforce permissions, or
defend against symlink/path replacement. Durable use begins only after those
emitted bytes are admitted and appended through `ArtifactJournal` under a
deployment-chosen sync and recovery policy.

## 5. FORMAT v4: authenticated admission assembly

`Uwueave/RuntimeAuthV4.lean` is the original v4 model and legacy kind-1 codec.
`Uwueave/RuntimeAuthV4Kernel.lean` adds a separate context-bound kind-3 request
and kind-4 host projection. These native boundaries now supply canonical
syntax, shape, host-width, and exact projection decisions without giving any
one of them a broader admission meaning.

The legacy kind-1 request is a signed move. `SignedContent` binds:

- length-delimited `document` and `genesis` stable ids;
- `signatureAlgorithm`, `issuer`, and `keyEpoch`;
- a scoped `nonce`;
- `MovePayload.operationId`, `lamport`, stable and request-local child ids,
  optional stable and request-local destination ids, and `cite`.

`signingBytesV4` is domain-separated by `protocolMagic` (`UWV4`), version `4`,
and the move request kind. Field tags and length-delimited variable ids make
the encoding unambiguous. `signingBytesV4_injective` and the cross-document,
cross-version, and cross-kind separation theorems establish codec binding.
They do not establish collision resistance of a digest or unforgeability of a
signature algorithm.

There is no independent actor field: `toExecOp` sets `replica` to the signed
issuer, with `replica_is_signed_issuer` by construction. `Resolved` separately
requires every signed stable node id to map to its signed request-local kernel
index for the bound document and genesis. A resolver may not silently replace
an id or guess an index.

The executable context-bound request carries the same move fields plus a
nonempty opaque `contextCommitment`. That commitment is inside the distinct
kind-3 signing domain, so changing it changes the exact bytes presented to the
verifier. The codec assigns it no digest, availability, historical-state, or
authorization semantics; the host must supply those.

The shipping `AuthenticatedRuntime` is a raw-only ordered boundary: its public
`admit` method accepts the caller's byte slice, not a caller-authored
projection or checked record. Its stages are:

1. Bound and decode kind 3 with `decodeContextRequestBounded`; distinguish
   `tooLarge`, `badMagic`, `unsupportedVersion`, `wrongKind`, and `malformed`.
2. Run `validateContextShape`; empty document, genesis, context commitment,
   nonce, operation/node ids, or signature are eight explicit refusals. Then
   refuse child/citation values above unsigned 64-bit range and destination
   indices above signed 64-bit range before crossing the FORMAT-v3 ABI.
3. Verify the exact kind-3 `RuntimeAuthV4Kernel.contextSigningBytes` under the
   registry scope and named algorithm, then require the returned trusted-host
   receipt to match every verification input. These bytes are explicitly not
   the legacy kind-1 `RuntimeAuthV4.signingBytesV4`.
4. Classify both the scoped nonce key
   `(document, genesis, issuer, keyEpoch, nonce)` and operation key
   `(document, genesis, operationId)` against the authenticated journal.
   Identical signing bytes are an idempotent retry even if signature bytes
   differ; reuse with different signing bytes is a nonce or operation
   collision and is refused.
5. Require the request to match the runtime instance's fixed `RuntimeScope`
   `(document, genesis, contextCommitment, executionBinding)`. Pin that exact
   historical context; require its returned document, genesis, commitment and
   execution binding to match; then resolve every stable id and require both
   the provider's and the concrete execution weave's kernel index to equal the
   signed index.
6. Evaluate deployment-owned authority and membership policies independently
   against that same immutable context. Both must pass.
7. Construct the exact `MoveOp` and ask the concrete `LeanMoveExecution` for a
   prospective outcome. It clones its `MoveLog` and invokes the existing
   FORMAT-v3 replay. Only `Applied` and `SkippedCycle` are admissible;
   unauthorised, invalid, and unknown-node results are refusals.
8. Construct the crate-private checked record, append it under the journal's
   chosen sync policy with its nonce/operation reservations, and only then call
   the concrete Lean execution commit. An indeterminate append result makes no
   execution commit and requires pinned reopen before retry.

`VerificationBoundary.Accepts`, `Verified`, `ResolverBoundary`,
`ReadyForExecution`, `StorageBoundary`, and `StorageReceipt` name the premises
at those seams. `LayeredOutcome` and `WellLayered` prohibit downstream success
without upstream success. `ResponseCode` and `encodeResponse` give v4
nonempty, version-bound outcomes for decode, authenticity, nonce, authority,
membership, execution, and storage refusal.

The exported legacy `decodeCanonicalKernel` performs kind-1 step 1 and nothing
later. Its
result is exactly one tag byte for a refusal, or tag `0` followed by the exact
`encodeRequestV4` bytes reconstructed from Lean's decoded value. The public
Rust `auth::decode_runtime_auth_v4_canonical` interprets only those six tags;
it contains no UWV4 parser or encoder. The linked 107-byte fixture round-trips,
and focused canaries distinguish size, magic, version, kind, truncated, and
trailing-byte refusals. The size bound controls entry to the logical Lean
parser after the host already allocated the input.

### 5.1 Context-bound projection and concrete verifier boundary

`RuntimeAuthV4Kernel.projectAdmissionKernel` is the next executable rung. It
accepts only request kind 3, performs the five decode, eight shape, and three
host-width decisions above, and returns a canonical kind-4 response. Success
contains Lean's exact canonical request and signing bytes, signature and
algorithm, document/genesis/context/issuer/key-epoch/nonce/operation identities,
stable child/destination references, and every projected FORMAT-v3 execution
lane. The response has roundtrip, injectivity, kind-binding, exact-output, and
distinct-refusal theorems. Rust parses this response grammar only; it has no
kind-3 UWV4 request parser or encoder.

The safe Rust APIs refuse `input.len() > maximum_bytes` before entering FFI,
so an oversize slice is not copied into Lean. That does not bound allocation
which already occurred before the borrowed slice existed; network/file
transports need their own pre-read ceiling. Direct native-export callers also
cross a complete `ByteArray`, whose kernel path converts to a list before the
logical Lean bound. The transport and logical bounds are complementary.

`rust/src/auth_verifier.rs` supplies a pluggable `RequestVerifier` and
deployment-owned `KeyRegistry`. The concrete algorithm-tag-1 profile is a
32-byte keyed-BLAKE3 **symmetric MAC**, scoped by the exact context commitment,
document, genesis, issuer, and key epoch. It distinguishes unknown context,
document, genesis, issuer, epoch, revoked key, unavailable registry, unknown
algorithm, and bad MAC. `VerificationAcceptance` retains the exact context,
document, genesis, signing and signature byte vectors plus their unkeyed hashes,
and the algorithm/issuer/epoch scalars. `matches_input` compares the exact
vectors and scalars; the hashes are observations, not its only binding.

That acceptance is an ordinary trusted-host attestation: its public constructor
allows external verifier implementations to create it and performs no
verification itself. It is not an unforgeable Rust capability, public-key
signature, EUF-CMA argument, legal identity, key-ownership proof, authority,
membership, nonce, execution, or storage receipt. The in-memory registry makes
ordinary process copies and claims neither zeroization nor locked memory or
durable key lifecycle. The fixed 32-byte comparison accumulates all content
differences after a public length check; no machine-checked constant-time or
side-channel theorem is claimed.

### 5.2 Raw admission and externally pinned recovery

`rust/src/auth_runtime.rs` composes those seams without adding a second UWV4
parser. `AuthenticatedRuntime::new` requires an externally pinned empty
`AuthenticatedMoveJournal`, an empty execution move log, and a concrete Lean
execution-base digest equal to the fixed `RuntimeScope`; a nonempty journal must
use `recover`. Admission returns five top-level outcome classes: an appended or
idempotent-retry receipt, a typed refusal, a dependency-unavailable result, a
definite `StorageRefused`, or `StorageIndeterminate`. The receipt names the
sequence, disposition, exact prefix head and kernel observation while the
journal retains the exact canonical request/signing/signature bytes. A definite
storage refusal is known not to append a new record. An indeterminate result
means no execution commit occurred, not that the disk write definitely failed.

The execution binding is a domain-separated, length-framed BLAKE3 digest over
the concrete weave's ordered node ids, ranks and parent lists plus the exact
grant and revocation lanes. Node ids already commit to contents and parents;
move operations are deliberately excluded because admission appends them only
after the base has been checked. This binds the executor to the context supplied
for one runtime instance; it is an unkeyed identity digest, not authentication.

`AuthenticatedRuntime::recover` also refuses an unpinned journal. For every
record in sequence it sends the stored canonical request back through Lean's
kind-3 projection, reruns exact-byte verification, pins the named historical
context, resolves stable ids, rechecks authority and membership, and performs
the concrete Lean execution preflight. It then requires the newly constructed
complete checked record—including context/policy versions, execution binding,
previous head, request, signature, projections and observation—to equal the stored record before
committing that move to the isolated recovery execution state. Any refusal,
unavailable dependency, projection error, or field mismatch prevents a ready
runtime.

This is an executable host composition boundary, exercised by **11/11 focused
end-to-end tests**, not a formal end-to-end authentication theorem.
The final serialized all-target checkpoint passed **177/177** in **125.72s
real** after **10.49s** compilation; the runtime target accounted for
**85.31s** because it repeatedly launches the Lean-owned corpus. This is
regression-path evidence, not admission throughput.
`RequestVerifier`, context, resolver, authority, and membership are deployment-
owned traits; `VerificationAcceptance` is constructible trusted-host evidence;
the context commitment remains opaque;
and recovery is authoritative only relative to caller custody of the external
head pin and availability of the exact historical policy data. The journal and
runtime do not prove cryptographic hardness, pin freshness, filesystem crash
behavior, stable media, or policy correctness.

### 5.3 Checked V4 sidecar: a different wire and a one-way boundary

The Preoscript V4 sidecar is a neutral deployment manifest, not a replacement
for the `UWV4` request above. `RuntimeAuthV4Checked.CheckedManifest.ofReady`
consumes the exact `ReadyForExecution`, successful shape validation, an active
grant receipt, and a finite context receipt. The context pins nonempty opaque
substrate/head/origin/version identities, a canonical roster and participant
subset, while the grant receipt pins activity, parent ordering, cited id, and
scope coverage. Only this checked producer projects the signed request into
neutral rows.

`RuntimeAuthV4Durable` frames those rows under `FormatTag ⟨4,162⟩`; it is
intentionally incompatible with the `UWV4` signed-request prefix. The canonical
fixture is 369 bytes (SHA-256
`a9f32051b0e1e328ab08b253a808ba54cc5c4a4e9cb2b5d2550c3811cf03b819`).
Bounded projection validation checks schema, byte/list/numeric ceilings,
canonical lists and grants, cited scope, node-index consistency, issuer roster,
and participant membership before rendering a diagnostic Rust DTO. Decode
returns only `Manifest`: it cannot construct `CheckedManifest`, recover a
signature proof, infer authority, or bless the opaque digests.

The Wave-27 runtime test stores those 369 bytes as an opaque history-arrival
payload under `SyncData`, reopens them exactly, drains after the parent arrives,
and converges across causal/reverse order. It also deliberately stores a
version-mutated sidecar under another event id. That acceptance is the canary:
`HistoryArrivalJournal` promises durable opaque bytes, not authentication or V4
validation.

The Wave-27 acceptance runner adds three positive and eighteen standalone-red
Lean fixtures for authenticated context/frontier and the V4 sidecar, delegates
the unchanged three-green/fifteen-red-command transactional V3 suite, and runs
four focused durable-arrival recovery/refusal tests.

### 5.4 Authenticated ERA certificate: exact delivery scope

`AuthenticatedEraCertificate.Verification` is the bridge from the signed
frontier layer into ERA's existing certificate machinery. It consumes one
exact accepted, genuinely issued, roster-bound progress event and a separate
`CompleteAnnouncement` tying that same event to truthful before/after ERA
worlds, its announced cut, issued pool, delivered log, and lawful complete
frontier. Only those two premises together yield `Settled`, the concrete
`settledCert`, delivery-scoped free termination, and the user-level role seal.

`Verification.toReusableCertificate` then intentionally discards the signed
record, signature, issuer, roster, trace, and frontier witness. The retained
artifact is exactly an ERA delivery key and proof that `settledCert` accepts
it. Exact-key equality licenses reuse through `KeyCertSound`; it does not
replay verification, authenticate storage, or survive a new announcement
under the old key. There is still no certificate for the unbounded announcement
future. The separate host keyed-BLAKE3 MAC verifier does not instantiate this
certificate proof bridge or supply its issuance/announcement premises.

The Wave-28 subprocess gate has one positive and five exact-red fixtures. It
pins verification, reusable-certificate soundness and seal survival, then
refuses the wrong event domain, accepted-but-unissued input, incomplete
announcement/frontier, and wrong reusable key. Its prefix checks audit 118
production constants and four test-support constants.

### 5.5 Finite authoring and delivery are proof leaves, not runtime widening

Wave 29 adds two import-pure proof leaves and deliberately leaves
`RuntimeInit`, the FFI, and the native closure unchanged. `FiniteRepairMenu`
checks an explicit finite row bound and stable-ID order, then retains the exact
typed repair, generated menu row, and full `Price`; it has no host endpoint and
does not discover or globally optimize repairs.

`FiniteHistoryDelivery` begins with an authored complete finite `History` and
explicitly assumes each `DeliveredGrowth` replay succeeds, has the exact
accepted list, is coherent, and settles. It proves that different arrival
orders materialize the same finite event set and therefore the same
`eventSetView`. That is not a byte codec, Rust callback implementation,
filesystem observation, delivery theorem, authentication mechanism, or
semantic-history convergence theorem. The latter still requires a separate
`SameRecord` plus `HistoryConvergent` or `RecordDetermined` premise.

The test-only Wave-29 runner exercises a six-version repeated lock history in
causal and maximally reversed order and refuses ID collision, self-parent, and
duplicate-parent inputs. Its repair cases check the finite bound/order,
least-authored-ID, exact full price, and exact-list refusal boundaries. Both
incremental RSS slopes pass: 441,344 B/item for repair and 440,320 B/item for
history.

### 5.6 Paid authenticated-move record and remaining v4 records

The first typed lane has landed in the separate `AuthenticatedMoveJournal`:
exact kind-3 request/signing/signature bytes, context and policy versions,
the exact execution-base binding, nonce/operation scopes, stable references,
projected and concrete move fields, kernel observation, and prior head. Section
6.1 gives its physical contract.
It is intentionally not a generic byte/event escape hatch.

The remaining authoritative runtime schema still needs explicit lanes:

- `AuthorityGrantIssued` and `AuthorityGrantRevoked`: signed issuer/holder,
  stable scope, key epoch, nonce, and operation id; the current numeric
  `(id,parent,scope)` alone is insufficient for authenticated durable policy.
- `EraEventAdmitted` and `EraCutAdmitted`: exact signed event/cut identity and
  issuer binding, including the lifecycle/invitation decision where used.
- `KeyBound`, `KeyRotated`, and `KeyRevoked`: document/genesis-scoped key
  history required to verify old records deterministically.
- Explicit causal-node, sequence-edit, seam-decision, bookmark, activation,
  and spend variants as those surfaces become durable.
- `Checkpoint`: a versioned candidate over an exact authoritative prefix and
  state/substrate commitment, validated by replay before use.

Kind-3 `ContextSignedContent.contextCommitment` is the new field-tagged,
domain-separated substrate reference. The codec proves only that it is
nonempty, signed, and preserved exactly. A deployment must define whether it
commits to an ordered authoritative prefix or a canonical authenticated state
root and provide historical availability and recomputation. The journal's
unkeyed chain head and arbitrary nonempty context bytes do not create those
semantics.

### 5.7 Authenticity, authority, membership, and execution

Composition is conjunctive, not substitutive:

- **Authenticity:** concrete verification says the issuer/key epoch accepted
  these canonical bytes. The keyed-BLAKE3 profile is one concrete symmetric-
  MAC implementation; other `RequestVerifier` implementations are trusted
  deployment code, and no cryptographic security theorem follows. Lean treats
  acceptance as a premise.
- **Authority:** the configured `MoveAuthority` must accept the issuer and move
  under the pinned context. The runtime stores the returned context's authority
  policy version, but the trait implementation owns grant-holder and stable
  scope semantics.
- **Membership:** the independent `MoveMembership` must accept the same issuer
  under the same pinned context. The runtime stores its policy version, but the
  deployment still chooses and implements the ERA/lifecycle discipline.
- **Execution:** only after all three checks may `toExecOp` enter the existing
  Lean `Exec` semantics. Execution status does not retroactively authenticate
  a request.

Liveness remains separate. Fail-closed verification, missing substrate data,
an unavailable key, a stale membership prefix, lock contention, or storage
failure may all prevent progress safely. A future liveness statement needs an
explicit scheduler, delivery/fairness assumptions, key/substrate availability,
and a storage service assumption.

## 6. Migration and backward refusal

FORMAT v3 remains the internal execution ABI while the raw kind-3 authenticated
move orchestrator now guards one admission path. Complete migration remains
additive and loud:

1. Keep the current v3 FFI entry point for internal execution only. Do not
   reinterpret v3 bytes as v4 requests.
2. Keep both distinct bounded v4 entry points: legacy kind-1 syntax and kind-3
   context projection. The runtime consumes the latter's version-bound kind-4
   response and then performs its host admission stages; never reinterpret
   either Lean syntax/projection success as verification.
3. Add a new versioned `DocumentEntry` variant that stores exact canonical v4
   bytes. Never relabel existing `Move`/`Grant`/`Revocation` entries as
   authenticated.
4. On open, classify old document records as **legacy unsigned**. A secure
   runtime either refuses them, opens explicitly in legacy mode, or imports
   them through a separately signed genesis/migration manifest that commits to
   their exact ordered bytes. Migration is a new authority decision, not a
   codec conversion.
5. Once authenticated coverage includes every mutating public surface, expose
   a secure wrapper whose append APIs require an admission receipt and keep raw
   `MoveLog`/legacy journal mutation APIs outside that wrapper.
6. Retain old decoders only for declared migration/read-only paths. Unknown
   versions, kinds, record tags, and complete malformed records are refusals;
   they are never guessed or skipped.

### 6.1 Authenticated-move journal rung

`rust/src/persistence/authenticated.rs` is a separate physical domain, not a
new tag in legacy `UWDJRN01`. `AuthenticatedMoveJournal` uses marker
`UWAMV401` and domain `uwueave.authenticated-move-journal.v1`. Each canonical
v1 body preserves one crate-private already-checked kind-3 record: exact request,
signing and signature bytes; nonce and operation scopes; nonempty context plus
the exact framed execution-base binding and resolver/authority/membership
policy versions; stable ids, projection and
concrete `MoveOp`; prior head; and the prefix-relative `Applied` or
`SkippedCycle` observation.

The same record owns nonce/operation retry-versus-collision indexing and the
append. Indexes advance only after the physical append succeeds. A domain-
separated BLAKE3 chain (`uwueave.authenticated-move-journal.v1.chain\0`) binds
the ordered bodies, including each execution binding. Pinned reopen requires
the exact external last-sequence and
head expectation and therefore refuses clean suffix rollback relative to that
pin. Unpinned reopen is inspection-only and cannot append. The shared raw
journal still supplies record bounds, exact-sequence retry plus resync,
explicit sync/torn-tail policies, locking, checksums, and poisoning after
uncertain I/O.

The crate-private constructor and append method are now reachable only through
the ordered raw-request runtime boundary described in §5.2 (or internal module
code). Storage itself still does not parse UWV4, verify the signature or
context, rerun resolution/authority/membership, make unpinned recovery ready
for execution, defeat rollback without an external pin, or prove filesystem/
stable-media durability. Its six focused module tests cover retry/collision,
pinned rollback, unpinned read-only behavior, torn recovery, legacy-domain
isolation, and oversize atomicity. This is a concrete persistence and host-
composition API—not a cryptographic, policy-correctness, or crash-safety
theorem.

## 7. Optional future redb backend

There is no `redb` dependency today; `rust/Cargo.toml` uses `blake3` for the
current physical journal. SQLite is not part of this plan.

A future pure-Rust `redb` integration should be a separate
`AtomicCommitStore` backend behind the same logical record/admission model,
not a replacement codec. A minimal design would atomically maintain:

- an ordered authoritative record table keyed by document and sequence;
- a nonce table keyed by the full v4 `NonceKey`, storing a digest or exact
  signed content sufficient to distinguish retry from collision;
- commit metadata containing schema version, last sequence, and authoritative
  prefix commitment;
- optional checkpoint blobs keyed by their covered commit, always replay-
  validated before use.

One transaction may append a checked batch, reserve all nonce keys, and update
commit metadata. Success must refine `SuccessfulBatchObservation`; an
ambiguous failure must be resolved by reopen and refine
`AtomicBatchObservation`. Differential tests should run the same logical
history against the current append log and the redb adapter. Database
transactions are still deployment evidence, not an automatic filesystem or
power-loss theorem.

## 8. Operator checklist

- Give `ArtifactJournal`, `DocumentJournal`, and `HistoryJournal` different
  files; never decode a physical file as a logical artifact stream.
- Keep artifact frames within the fixed 1 MiB Lean-validation ceiling, and set
  operational limits for total file bytes and record count outside this API.
- Place journals in a trusted directory with an explicit permission and
  symlink policy; the current pathname API does not enforce either one.
- Use the default `TornTailPolicy::Refuse` until truncation is an explicit
  recovery decision. Record `open_report().truncated_bytes` when truncating.
- Treat every corrupt complete record or invalid checkpoint as an incident;
  do not skip it or copy the suffix into a new journal.
- Run one cooperative writer per journal and treat `Locked` as a live owner or
  stale-environment investigation, not permission to bypass locking.
- Choose `SyncPolicy` from the deployment failure model. Do not report
  `SyncData`/`SyncAll` as proven stable-media durability.
- After append/sync I/O failure, discard the poisoned handle, reopen, and
  retry the same sequence and exact bytes.
- Back up authoritative journal files and migration manifests. Derived views,
  caches, and unvalidated checkpoints are rebuildable and are not backups.
- Do not call legacy document records authenticated. Expose the raw v4 runtime
  as a secure deployment path only with production verifier/key history,
  historical context, resolver, authority and membership providers, explicit
  external-pin custody, and a declared storage failure model; the traits and
  journal do not manufacture those premises.

## 9. Next two implementation slices

### Slice A: one authenticated move, end to end — landed host boundary

The smallest slice has landed without rewriting `Exec`: legacy kind-1 syntax,
kind-3 decode/shape/width/projection, scoped verifier, authenticated journal,
and `AuthenticatedRuntime` now form the exact raw-only order documented in
§5.2. One `RuntimeScope` fixes document, genesis, context and the concrete Lean
execution base. Recovery requires an external pin and revalidates the complete
historical prefix before it yields a ready runtime. The focused suite is
**11/11 green**. The remaining work here is stronger
evidence: exhaustive adversarial runtime tests, formal refinement of the host
composition to the Lean layered model, production policy implementations and
their historical-data/key lifecycles, a filesystem/crash model, and a
cryptographic security argument. The landed API does not by itself supply any
of those claims.

### Slice B: complete authoritative document recovery

Extend the typed journal across the remaining mutating surfaces: causal node
creation, sequence edits, authenticated grants/revocations, ERA events/cuts
and key history first; then seam, spend, bookmarks, and activation under
explicit policy. Instantiate a concrete `PersistentRuntime.RecordSchema`,
validate checkpoints against exact prefixes, rebuild a full `Weave` without
consulting caches, and add failpoint/reopen differential tests.

Then define `AtomicCommitStore` and implement either a conservative segment
commit protocol or the optional redb adapter. Prove/refine at the logical
boundary that accepted batches produce only the observations allowed by
`SuccessfulBatchObservation` and `AtomicBatchObservation`; keep OS/filesystem
behavior as an explicit deployment assumption.
