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

## 1. What ships today: the FORMAT-v3 path

The current public Rust path is a deterministic but unauthenticated runtime:

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

Important current gaps:

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

### 1.1 Native closure and initialization

**Implemented as a fail-closed build control, not a compiler proof.**
`Uwueave/RuntimeInit.lean` is a deliberately data-free native root. It directly
imports exactly the four exported-kernel modules:

- `Uwueave.Exec`
- `Uwueave.SeqKernel`
- `Uwueave.EraKernel`
- `Uwueave.Preo.ArtifactJournalKernel`

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
initialized runtime. The current full gate observed 13 Lake-owned objects
(655,368 bytes before archiving), 14 archive members including the shim
(798,968 bytes), and 132 passing Rust tests.

This closes stale, extra, missing, and mixed-generation object selection plus
initializer drift. It does **not** prove Lean's IR-to-C lowering, either native
compiler or the linker, C/Rust/Lean ABI agreement, reference ownership, runtime
behavior, or filesystem semantics. Those remain the separate execution-TCB
rows in `docs/TRUST.md`.

## 2. The Cycle 22 persistence surfaces

Cycle 22 adds two deliberately different pure-Rust journals under
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

### 2.2 DocumentJournal: the typed MoveLog journal

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

### 2.3 Shared physical record format

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
`uwueave.document-journal.v1`. The BLAKE3 dependency is an integrity control,
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
| Artifact logical stream | Exact concatenation of `projectionBytes` | Canonical compiled artifact records |
| Artifact physical file | Checksummed `UWARJ001` records containing unchanged logical frames | Physical recovery evidence only |
| Document logical journal | Ordered typed `DocumentEntry` values | Presently MoveLog mutations; checkpoint is validated acceleration |
| Document physical file | Checksummed `UWDJRN01` records containing canonical entry bodies | Physical recovery evidence only |
| FORMAT v3 request | Lean-owned execution request bytes | Derived execution input, never journal authority |
| FORMAT v4 request | Canonical signed-request bytes from `RuntimeAuthV4` | Future authenticated admission record; not wired today |
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

## 5. FORMAT v4: authenticated admission plan

`Uwueave/RuntimeAuthV4.lean` is the smallest honest v4 foundation. It is a
**contract/model and canonical codec**, not a shipping Rust endpoint.

The one currently modeled request is a signed move. `SignedContent` binds:

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

Admission must be an ordered pipeline:

1. Bound and decode with `decodeBounded`; distinguish `tooLarge`, `badMagic`,
   `unsupportedVersion`, `wrongKind`, and `malformed`.
2. Run `validateShape`; empty document/genesis/nonce/operation/node ids and an
   empty signature are explicit refusals.
3. Verify the exact `signingBytesV4` under the registered issuer/key epoch and
   named algorithm.
4. Compare the scoped nonce key `(document, genesis, issuer, keyEpoch, nonce)`.
   Identical signed content is an idempotent replay even if signature bytes
   differ; the same nonce with different signed content is a collision and is
   refused.
5. Resolve stable ids and verify the included request-local indices.
6. Evaluate authority and membership independently against a committed,
   authoritative substrate. Both must pass.
7. Project with `toExecOp` and invoke the existing FORMAT-v3 execution
   semantics. Do not rewrite the sort/fold in Rust.
8. Append the exact canonical authenticated request, its admission decision,
   and the substrate reference required to reproduce that decision before
   acknowledging acceptance.

`VerificationBoundary.Accepts`, `Verified`, `ResolverBoundary`,
`ReadyForExecution`, `StorageBoundary`, and `StorageReceipt` name the premises
at those seams. `LayeredOutcome` and `WellLayered` prohibit downstream success
without upstream success. `ResponseCode` and `encodeResponse` give v4
nonempty, version-bound outcomes for decode, authenticity, nonce, authority,
membership, execution, and storage refusal.

### 5.1 Records v4 still needs

The next runtime journal schema should use explicit typed lanes rather than a
generic byte/event escape hatch:

- `AuthenticatedMove`: exact canonical v4 request bytes plus a stable
  substrate reference and the admitted `Exec.Op` projection.
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

The substrate reference should commit to the ordered authoritative prefix (or
to a separately specified canonical authenticated state root), not merely the
four arrays a caller chose to marshal. No such commitment is present in
`RuntimeAuthV4.SignedContent` today; adding it is a v4 schema revision that
must receive its own field tag and codec-separation theorems.

### 5.2 Authenticity, authority, membership, and execution

Composition is conjunctive, not substitutive:

- **Authenticity:** concrete verification says the issuer/key epoch accepted
  these canonical bytes. A future deployment must supply the cryptographic
  implementation and its security argument; Lean currently treats acceptance
  as a premise.
- **Authority:** the authenticated issuer holds an active grant whose stable
  scope covers the move. Grant-holder binding must be explicit; possessing
  someone else's grant id is not authority.
- **Membership:** the authenticated issuer is live and has the required ERA
  role in the committed membership prefix. Decide whether the runtime uses
  `Era.resolve` arbitration or `Era.resolveGated` lifecycle discipline and
  make that policy/version explicit.
- **Execution:** only after all three checks may `toExecOp` enter the existing
  Lean `Exec` semantics. Execution status does not retroactively authenticate
  a request.

Liveness remains separate. Fail-closed verification, missing substrate data,
an unavailable key, a stale membership prefix, lock contention, or storage
failure may all prevent progress safely. A future liveness statement needs an
explicit scheduler, delivery/fairness assumptions, key/substrate availability,
and a storage service assumption.

## 6. Migration and backward refusal

FORMAT v3 remains the shipping execution ABI while v4 admission is built. The
migration should be additive and loud:

1. Keep the current v3 FFI entry point for internal execution only. Do not
   reinterpret v3 bytes as v4 requests.
2. Add a distinct v4 decode/admission entry point. `UWV4`, version, and kind
   must be checked before any semantic field is used; v4 responses are always
   nonempty and version-bound.
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

- Give `ArtifactJournal` and `DocumentJournal` different files; never decode a
  physical file as a logical artifact stream.
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
- Do not call current document records authenticated. Do not enable secure v4
  mode until concrete verification, key history, nonce persistence,
  authority, membership, and authenticated append are all in the path.

## 9. Next two implementation slices

### Slice A: one authenticated move, end to end

Land the smallest slice that improves the boundary without rewriting `Exec`:

1. Export the canonical v4 bounded decoder/encoder and refusal codes through a
   narrow typed FFI, as was done for artifact validation.
2. Add a Rust `AuthenticatedRuntime` wrapper with a pluggable verifier and
   explicit key registry, stable-id resolver, authority predicate, membership
   predicate, and persistent nonce index rebuilt from authoritative records.
3. Add a versioned `AuthenticatedMove` document record carrying the exact v4
   bytes and a reproducible substrate-prefix reference.
4. Admit only after decode, shape, concrete verification, nonce, resolution,
   authority, and membership checks; project with `toExecOp`; append before
   returning accepted. Keep FORMAT v3 as the internal execution kernel.
5. Test every layer's refusal, cross-document/genesis/key-epoch substitution,
   retry versus nonce collision, stable-id/index mismatch, omitted/stale
   substrate, append ambiguity and reopen, and exact v4-to-`Exec.Op` fields.

This slice may claim codec binding and tested verification behavior for the
chosen implementation. It must not claim EUF-CMA security or crash safety.

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
