# PREOSCRIPTING

*The design document for **preoscript** — a language for composing promises,
future-relative evidence, and proof-carrying repair plans. Committed, unlike
the correspondence in `CODEXHELP.md`; this is what we intend to build, revised
in place as we learn we were wrong.*

---

## Quickstart: one checked query from source to bytes

[`Uwueave.Preo.Quickstart`](Uwueave/Preo/Quickstart.lean) is the smallest
complete, executable journey through the current surface. The companion
[`scripts/preo-quickstart-canaries.sh`](scripts/preo-quickstart-canaries.sh)
checks the positive path, five deliberate type errors, canonical V3 bytes,
reopen, a two-frame logical journal, and bounded Lean inspection. From the
repository root, this block is copy-pastable:

```sh
# Compile the checked example and run its green/red/runtime canaries.
lake build Uwueave.Preo.Quickstart Uwueave.Preo.ArtifactInspectionMain
scripts/preo-quickstart-canaries.sh

# Materialize the Quickstart's exact V3 bytes, then inspect one frame and the
# two-frame logical artifact journal. Keep the directory printed at the end.
quick_dir="$(mktemp -d "${TMPDIR:-/tmp}/preo-quickstart-doc.XXXXXX")"
lake env lean --run tests/preo-quickstart/Runtime.lean "$quick_dir"
tools/uwueave-preo-inspect --frame "$quick_dir/quickstart-v3.frame"
tools/uwueave-preo-inspect --journal "$quick_dir/quickstart-v3.journal"
printf 'quickstart artifacts: %s\n' "$quick_dir"

# The production emitter has a finite registry of real Lean-owned artifacts.
tools/uwueave-preo-artifact --list
tools/uwueave-preo-artifact \
  semantic-export --output "$quick_dir/semantic.preo"
tools/uwueave-preo-inspect --frame "$quick_dir/semantic.preo"

# stdout mode emits binary only, so redirect it before inspecting it.
tools/uwueave-preo-artifact full-export --stdout \
  > "$quick_dir/full.preo"
tools/uwueave-preo-inspect --frame "$quick_dir/full.preo"
```

The source path is deliberately explicit:

1. `preo_program Journey` binds the application `AppState` to the typed
   `AppSchema` through `project`, evaluates one typed expression, and retains
   the authored state and projected-environment reaches. Its generated
   `.Eval`, `.Future`, `.Result`, `.Report`, reads, holes, and analyses all come
   from that one checked term.
2. `QueryFuture` names equality of the projected environment over an
   `AppWorld`, and `preo_certificate QueryCertificate` is indexed by that exact
   future, acceptance predicate, and `startIndex`. The resulting certified
   report retains the exact world; a certificate for another future or world
   does not typecheck.
3. `preo_protocol JourneyProtocol` elaborates the two written crossings.
   `preo_plan JourneyPlan` searches only its duplicate-free, capped, authored
   action universe and retains the selected plan proof. `preo_budget
   JourneyBudget` then consumes that plan's `ProfileUpperBound`; a floor or a
   number alone cannot accept the budget.
4. Proof-indexed builders produce checked V3 query, result, world, certificate,
   plan, and budget rows with written stable IDs. In this fixture the query
   reads only `count`, the result is exact/inspectable/shown, and the certificate
   points to the same future and world. `v3Artifact` is assembled only through
   checked additions, `v3_bytes_reopen_exact` proves canonical decode, and
   `v3_bytes_executable_exact` proves the stack-safe emitted bytes equal those
   canonical bytes.

### Authenticated observation and transactional V3 export

The Quickstart above deliberately authors its analysis reach. The Wave-26
adapter in [`ObservedBoundResult`](Uwueave/Preo/ObservedBoundResult.lean) is the
next boundary: it lets a deployment attach a separately supplied running reach
and authenticity proof to the already world-bound report. It does not observe
anything itself. The complete acceptance gate is
[`scripts/preo-v3-acceptance-canaries.sh`](scripts/preo-v3-acceptance-canaries.sh):

```sh
# Two positive fixtures, rollback/name-reuse, and fourteen exact rejection
# boundaries: authenticity, reach, dependent indices, resources, and trust.
scripts/preo-v3-acceptance-canaries.sh

# The positive observed value and public surface can also be checked directly.
lake env lean tests/preo-v3-acceptance/PositiveObserved.lean
lake env lean tests/preo-v3-acceptance/PositiveSurface.lean
```

The observation premise is ordinary proof-bearing Lean data. This is the exact
shape used by the positive fixture:

```lean
def observationBoundary :
    ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state

def runningReach : List AppWorld := [startWorld]

def observedStartReport :
    ObservedBoundResult.ObservedCertifiedReport observationBoundary worldBinding
      runningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld observationBoundary worldBinding runningReach
    startIndex
    rfl                                      -- Authentic startWorld start
    (by change startWorld ∈ [startWorld]; simp) -- running reach
    (by change startWorld ∈ [startWorld]; simp) -- authored world reach
    QueryCertificate                         -- this future/index/answer
```

`ObservedCertifiedReport` retains all four premises rather than flattening
them: the external `Authentic` witness, membership in `runningReach`, membership
in `worldBinding.worldReach`, and the exact `CheckedCertificate`. Its world and
state equalities align the observed state report and certificate-gated world
report at one `WorldIndex`. A bare `CertifiedReport`, a lookalike record, an
authentic state at the wrong world, or an authored world absent from running
reach is insufficient. Conversely, the constructor does not read a process,
network, filesystem, clock, signature, or device, and it does not prove that
the caller's `runningReach` is complete or truthful.

The live checked V3 surface consumes that exact observed family:

```lean
preo_export_v3 Export from Journey := {
  base := baseArtifact,
  futureDecl := QueryFuture,
  binding := worldBinding,
  index := startIndex,
  observed := observedStartReport,
  certificate := QueryCertificate,
  plan := artifactPlan,
  budget := artifactBudget,
  query := checkedQuery,
  future := artifactFuture,
  world := checkedWorld,
  resolutionId := fun _ => ⟨0⟩,
  surfaceId := StableId.surface,
  reasonId := fun _ => ⟨0⟩,
  certificateId := StableId.certificate,
  branch := exactStartBranch,
  maxWork := 64,
  config := validationConfig
}

example : Export.StateProgram = Journey := rfl
example : Export.ObservedReport = observedStartReport := rfl
example : Export.Encoding = v3Artifact := rfl
example : Export.Bytes = v3Bytes := rfl
example : Export.Validation.isOk = true := Export.validation_ok
```

This is a checked projection, not a record-shaped escape hatch:

- `observed` must reduce to the real `ObservedCertifiedReport` family for the
  exact binding and index; `certificate` must be the certificate retained by
  that report.
- `plan` and `budget` must already be rows of the exact base artifact, and the
  budget must name that exact plan. `query`, `future`, and `world` remain
  indexed by the supplied state program, future declaration, and world index.
- Result status, effect, visibility, disclosure, and certificate rows are
  projected through checked builders. The caller cannot type in favorable
  first-order badges.
- `maxWork` bounds surface expansion before result construction. `config`
  independently bounds the data validator: V2 base resources plus V3 stable-ID
  magnitude; world/query/result/certificate counts; reads, holes, hole-path
  depth, analyses, and effect width. Raising one bound does not waive the
  other.
- V3 validation also requires unique, strictly increasing extension row IDs;
  canonical analysis/effect order; query↔result agreement; reads equal the
  field erasure of holes; valid binary child-path segments; referenced fields,
  futures, and worlds; a downward-closed effect containing the observed status;
  and disclosure only where the status permits it. The V3 wire still cannot
  validate certificate→result association or collisions among authored
  resolution/surface/reason name registries, so the proof-indexed construction
  remains stronger than decoded validation.

The command owns one environment transaction. Any failed phase—including work
or validation refusal—rolls back every declaration under the export prefix;
the same name may then be reused by a successful command. This is Lean
environment rollback, not filesystem or external-service atomicity.

The API is green; its current scaling gate is not. Wave 27 measured the V3
export peak-RSS slope as
`(RSS₁₆ − RSS₀) / 16 = 7,031,808 B/item = 6.7060546875 MiB/item`, which is a
`FAIL_SCALE` against the hard **4 MiB/item** ceiling. The harness used serialized
`lean -j1 --profile` processes wrapped in `/usr/bin/time -lp`, two unmeasured
warmups and the median of five runs, without cache clearing or the declaration
trace profiler; all four V3 rows were below its noise threshold. Exact generated
prefixes, rollback/reuse, and API-status goldens still pass. This is an
elaboration-process memory result, not runtime heap usage or evidence that the
semantic construction is unsound. Reproduce the retained hard surface checks
without rebuilding dependencies with:

```sh
PREO_BENCH_SKIP_BUILD=1 scripts/preo-bench.sh wave27-golden
```

### Positional holes, attribution, and generic framing

Typed programs retain exact `Expr.Hole` values: syntax-tree child path, field
position, and `field`/`opaque` kind. `reads` is definitionally the field erasure
of that hole list. Checked V3 `HoleRow`s map those exact positions to authored
stable field IDs; validation bounds every path and checks that each path segment
is a binary child index. A decoded hole row is structural diagnostic data, not
evidence that a runtime source produced the value.

The separate [`DerivedProgram`](Uwueave/Preo/DerivedProgram.lean) attributed
materialization retains candidate value, source, and the complete positional
hole. Its `verifiedAttributedDocument` additionally requires a caller-supplied
`SourceAuthenticity` proof for every present world, and
`verified_position_iff` returns that authenticity fact with the exact
candidate/source/position witness. Neither V3 decoding nor a field ID supplies
that proof.

Framing is generic below either artifact version. `ArtifactDurableCore` exposes
`stackSafeEncodeFrame tag payload` and `stackSafeEncodeValue codec tag value`,
proved byte-identical to `Durable.encodeFrame`/`encodeValue`, including reserved
payload bytes and exact trailing-journal preservation. The supplied canonical
codec still owns payload semantics; a `FormatTag` only separates version and
domain. V3 uses version `3` in artifact domain `161`, while V2 remains a
different version. Generic framing therefore does not make V2 accept V3, make
an arbitrary codec canonical, or promote decoded rows into proofs.

### Authenticated frontier and world-context path

[`AuthenticatedFrontier`](Uwueave/AuthenticatedFrontier.lean) makes frontier
progress a conjunction, not a signature-shaped shortcut. Its reserved inner
ERA event kind is `6`. `AuthenticatedProgress` retains the exact accepted
signed event, membership in the received trace, genuine `WasIssued` evidence,
actor=issuer, and issuer membership in the written roster.
`AuthenticatedAdvance` then adds two independent semantic premises: the
issuer's new frontier point is settled, and the event's decoded before/after
frontiers and issued/delivered pools form a lawful `Frontier.DeliveryAdvance`.
The caller supplies the signature scheme, authentic-issuer premise, received
trace, issuance transcript, roster, and semantic decoder. Signature acceptance
alone manufactures none of them.

[`AuthenticatedWorldContext`](Uwueave/AuthenticatedWorldContext.lean) (AWC)
continues the checked path at reserved position-event kind `5`:

```text
AcceptedEvent + received trace + AuthenticIssuer
  → IssuedPositionEvent
  → AuthenticatedPositionClaim (exact world/value/source/Expr.Hole)
  → ContextualPositionClaim (active grant + causal origin/version)
  → ConsumptionReceipt (fresh grow-only grant tombstone)

AuthenticatedProgress + lawful AuthenticatedAdvance
  + one exact contextual position witness per newly delivered candidate
  → AuthenticatedConsumingDelivery
  → WorldFuture.DeliveryFuture
```

The final projection is deliberately `WorldFuture.DeliveryFuture`, not the
stronger `WorldContext.DeliveryFuture`, because capability consumption grows
while the underlying context axes stay frozen. The positive fixture also pins
three refusals: a stale world version, the wrong causal origin, and reuse of a
consumed grant. AWC proves a model-level relationship from explicit premises;
it does not deploy a cryptographic verifier, observe a network, or serialize
those proofs into a sidecar.

The complete green/red boundary suite is copy-pastable from the repository
root. It includes frontier origin/roster/domain/staleness, AWC
position/origin/version/capability, V4 sidecar, the unchanged V3 surface, and
the native durable-arrival tests:

```sh
scripts/wave27-acceptance-canaries.sh
```

### Signed ERA cut bridge and reusable delivery certificate

[`AuthenticatedEraCertificate`](Uwueave/AuthenticatedEraCertificate.lean)
joins the authenticated frontier path to ERA finalisation without treating one
as proof of the other. `EraCodec` extends the frontier codec with event time,
announced cut, and before/after ERA-world projections. Every projection is
applied to the exact event in `progress.acceptedEvent`; the canonical frontier
candidate pairs that ERA event and its decoded time with the event's actor.
Those codec functions are authored semantic bindings, not hashes or an
authenticated wire decoder.

`CompleteAnnouncement` is the separate lawfulness/completeness price. For the
same signed event it requires:

- an `EraCertificate.Announcement` from the decoded before-world to the
  decoded after-world;
- membership of the decoded cut in the after-world's cuts;
- exact equivalences between after-world pool/log membership and the lawful
  advance's issued/delivered booleans for every canonical ERA candidate; and
- settlement in the decoded after-frontier for every finalised pool event.

The cut-membership field says that the cut is present after the announcement;
it does not say that this call newly added it. Likewise, the two `iff` fields
classify the canonical candidates obtained from ERA events. They do not exclude
extra malformed or non-canonical points in a more general frontier carrier.
`CompleteAnnouncement.settled` combines these premises with the lawful
advance's delivery-completeness theorem to prove
`EraCertificate.Settled afterWorld`.

`Verification` is the exact junction. Its authenticated acceptance, receipt,
genuine issuance, actor/issuer equality and roster membership live in the
indexed `AuthenticatedProgress`; its stored field is the independent
`CompleteAnnouncement`. From both it exposes the announcement, cut membership,
settlement, `settledCert (eraKey afterWorld)`, and the existing role-seal
theorem. A signature alone therefore proves neither announcement lawfulness
nor settlement, while a lawful announcement alone authenticates no source.

The resulting free-termination theorem is intentionally scoped to
`EraCertificate.Delivery`: already-issued events may arrive while the cut set
and issuance pool stay frozen. It says that `finalView` is stable on that axis
only. It does **not** license stopping under `Announcement` (the cut set may
grow) or `Issuance` (the pool may grow), and it says nothing about ERA's
non-final `fullView`.

`Verification.toReusableCertificate` then forgets the one-time signed record,
signature, issuer, roster, received trace and frontier proof. The resulting
`ReusableCertificate` contains exactly an `EraKey` and a proof that
`EraCertificate.settledCert` accepts that key. Its `Matches` relation is exact
key equality, and `ReusableCertificate.sound` turns that pair into a reusable
`KeyCertSound` object for `finalView` under `Delivery`. It cannot be reused for
a different key, and retaining it is not equivalent to retaining or replaying
the original authentication.

This is a model-level proof bridge, not a deployment verifier. The signature
scheme and key/revocation views, received trace, issuance oracle, roster,
frontier decoder, complete announcement, and event-ID authenticity remain
caller premises. The fixture uses the toy signature scheme. The module creates
no live record or cut, checks no production cryptography, defines no wire
format, and establishes no filesystem, network, replay-store, or host-execution
guarantee.

The frozen acceptance gate is copy-pastable from the repository root:

```sh
scripts/wave28-era-certificate-canaries.sh
```

It contains seven Lean fixtures (one common support file, one positive, and
five standalone red fixtures), **190 lines including the runner**. The latest
frozen functional run took **7.0s**: the positive pins acceptance, issuance,
`Announcement`, `Settled`, exact reusable key/acceptance/soundness and
`sealSurvives`; the reds reject the wrong reserved domain, accepted-but-unissued
input, an incomplete announcement codec, an incomplete settled frontier, and a
wrong reusable key. Declaration-prefix floors cover 118 production constants
and four common-test constants, both clean.

At the same freeze the aggregate census was 182 Lean source modules, 183 full
build jobs, 159 direct proof-root imports excluding `Audit`, and 25,041 audited
constants, with 700 MAP keystones and 130 documented transports. The remaining
work ledger records 155 literal `⟨UNDONE⟩` occurrences extracted as 153
marker-bearing blocks across 43 Lean files. These are checkpoint counts; the
final aggregate Rust gate passed 147/147 tests in 16.00s, including 1.61s of
compilation. These are checkpoint counts; the fail-closed commands are the
durable acceptance contract.

### Runtime-auth V4: checked sidecar, not the `UWV4` request

Three byte protocols now sit near one another and must remain distinct:

| bytes | framing | purpose |
|---|---|---|
| `RuntimeAuthV4.encodeRequestV4 request` | ASCII `UWV4`, then version `4`, request kind `1` | the signed runtime request; `signingBytesV4` covers its content but excludes the signature field |
| `RuntimeAuthV4Durable.manifestBytes manifest` | durable format `⟨4, 162⟩`; prefix `[213, 74, 4, 162]` | a neutral runtime-auth **sidecar** projected from a checked request, active grant, and finite context |
| checked artifact V3 bytes | durable format `⟨3, 161⟩` | the typed query/result/certificate artifact described above |

[`RuntimeAuthV4Checked`](Uwueave/Preo/RuntimeAuthV4Checked.lean) is the one-way
proof-rich producer. `CheckedManifest.ofReady` consumes the exact
`RuntimeAuthV4.ReadyForExecution`, shape check, active `GrantReceipt`, and
`ContextReceipt`; its private constructor prevents decoded rows from entering
that type. `ContextReceipt.ofAuthenticatedProgress` may bind the request issuer
to an independently authenticated progress issuer by explicit equality. The
context's substrate/history-head digests and origin/version IDs remain
caller-authored, nonempty opaque byte bindings. Roster and participant lists
are finite canonical manifests, not proofs that membership is globally
complete.

The signed-request row now has two deliberately separated executable
boundaries. `RuntimeAuthV4.decodeCanonicalKernel` retains the legacy kind-1
syntax checkpoint: explicit bound, five exact refusal reasons, and canonical
re-encoding of the **107-byte** fixture. `RuntimeAuthV4Kernel` owns a distinct
context-bound kind-3 request and kind-4 projection response. Its signing bytes
include the nonempty opaque context commitment; its native endpoint performs
the same five decode checks, eight nonempty-field checks, and three exact
FORMAT-v3 host-width checks before projecting canonical request/signing bytes,
signature and scope identities, stable ids, and every execution lane. Rust
interprets only the Lean-owned response grammar, never either UWV4 request
wire. A pluggable host verifier and keyed-BLAKE3 symmetric-MAC profile consume
the exact projected bytes under a context/document/genesis/issuer/epoch-scoped
registry. Their acceptance is ordinary trusted-host evidence—not public-key
verification—retaining exact scope/signing/signature vectors plus unkeyed
hashes. It is not EUF-CMA, resolution, nonce freshness, authority, membership,
execution, append, or durability.

The Rust `AuthenticatedRuntime` now composes a separate raw-only admission
boundary around kind 3: Lean projection; exact-input verification; durable
nonce/operation retry or collision classification; one immutable historical
context under one fixed document/genesis/context/execution-base scope, where
the last value is a domain-separated framed digest of concrete topology plus
grant/revocation lanes rather than an authenticator; stable-id/index resolution
against both the provider and concrete execution
weave; independent authority and membership; concrete Lean move preflight;
journal append; then in-memory commit. Definite storage refusal is separated
from indeterminate I/O. Recovery requires an externally pinned journal, reruns
those stages for every canonical
stored request, compares the complete checked record, and replays the prefix in
order. Those deployment traits, historical context availability, external pin,
MAC security and filesystem behavior remain premises—not facts reconstructed
from the V4 sidecar or proofs supplied by the host composition itself.

[`RuntimeAuthV4ProjectionCore`](Uwueave/Preo/RuntimeAuthV4ProjectionCore.lean)
validates the neutral sidecar's schema, resource bounds, canonical lists,
grant/reference relationships, scope, and listed membership. Only its private
`ValidatedProjection` may enter
[`renderRustSource`](Uwueave/Preo/RuntimeAuthV4Projection.lean), which emits a
neutral Rust DTO plus equality lookup conveniences—not a verifier, permit, or
membership oracle. `RuntimeAuthV4Durable.decodeManifestExact` likewise returns
only neutral rows; it cannot reconstruct `CheckedManifest`, signature
verification, authority, frontier, or storage evidence.

The opt-in fixture is exactly **369 bytes**. Lean proves its length, framing
prefix, and exact decode; the SHA-256 below is an external regression label,
not a theorem or authenticity claim. The emitter is intentionally test-only:

```sh
auth_dir="$(mktemp -d "${TMPDIR:-/tmp}/preo-auth-v4-doc.XXXXXX")"
lake env lean --run rust/tests/support/RuntimeAuthV4Fixture.lean \
  > "$auth_dir/runtime-auth-v4.sidecar"
wc -c < "$auth_dir/runtime-auth-v4.sidecar"       # 369
od -An -tu1 -N4 "$auth_dir/runtime-auth-v4.sidecar" # 213 74 4 162
shasum -a 256 "$auth_dir/runtime-auth-v4.sidecar"
# a9f32051b0e1e328ab08b253a808ba54cc5c4a4e9cb2b5d2550c3811cf03b819

# Kernel-check the checked→manifest→validate→render and exact-decode paths.
lake env lean Uwueave/Preo/RuntimeAuthV4Examples.lean
lake env lean Uwueave/Preo/RuntimeAuthV4Fixtures.lean
```

For library-side rendering, the exact sequence is
`Projection.ofManifest checked.toManifest`, `validate config projection`, then
`renderRustSource validated` (or `validateAndRender`). The fixture exposes it as
`RuntimeAuthV4Examples.fixtureRust`. There is no production sidecar emitter or
sidecar inspector CLI yet; the artifact inspector does not accept this format.

Three boundaries are load-bearing:

- `Journey.StateReach = [start, later]` and `worldBinding.worldReach =
  [startWorld]` are **authored analysis reaches**. They are not observations of
  runtime reachability and are not authenticated deployment facts. The
  world-bound certificate proves its proposition assuming the named world and
  future relation; it does not discover that the running process inhabits that
  index.
- `uwueave-preo-inspect` returns bounded, decoded JSON with
  `"authority":"diagnostic-only"`. Successful decoding and reference
  validation do not reconstruct a Lean verdict, certificate, plan, or proof.
  Proof authority remains in the checked source values from which the bytes
  were projected.
- The Quickstart's `quickstart-v3.journal` is just two concatenated logical
  artifact frames for the inspector. Rust `ArtifactJournal` is a separate
  checksummed physical store for exact artifact payloads. Rust
  `HistoryJournal` is different again: it stores explicit-ID causal application
  events with parents and opaque payloads; `HistoryArrivalJournal` additionally
  makes out-of-order arrivals authoritative. These stores preserve bytes—they
  do not validate a runtime-auth sidecar inside an event payload. Neither
  journal is the application's materialized state, and no current refinement
  theorem turns its payload into a proof-indexed Lean `History`.

All emission commands above cross an ordinary host-I/O boundary. Direct output
uses `IO.FS.writeBinFile`; redirected output uses the shell. Neither path
promises atomic replacement, `fsync`, directory durability, permission/path
hardening, or recovery after a crash. The Rust journals add concrete locking,
checksums, sync policy, reopen validation, and torn-tail policy, but those are
deployment evidence—not a theorem that a filesystem or device honors its
premises.

### Bounded authored repair menus

[`Uwueave.FiniteRepairMenu`](Uwueave/FiniteRepairMenu.lean) makes one useful
author-facing repair search executable without pretending to discover the
universe of repairs. A `UniverseInput` is an authored list of
`MenuCandidate`s plus an explicit `maxEntries`. `checkUniverse` first rejects a
list longer than that bound, then requires the stable numeric candidate IDs to
be strictly increasing. A successful `CheckedUniverse` retains both proofs;
its `toCatalog` projection preserves the exact list and merely forgets menu
presentation data.

`synthesize` returns the first applicable entry in that checked list. Strict ID
order makes it the least applicable authored ID, but the IDs are ordering
policy, not semantic costs: changing which repair receives the lower ID can
change the selected repair. The theorem therefore compares stable IDs only. It
does not order, total, scalarize, or exchange any field of `Repair.Price`.

The successful `Found` value retains the exact typed `Repair`, generated
available menu row, and the unchanged complete eight-axis `Price`: seam
crossings, arbiter cuts, rollback window, resolution writes, evidence
retention, plural read, reachability restriction, and assumptions. The row is
generated from the proof that the same candidate applies, so its promise delta
and price are those of that exact repair rather than authored duplicates.

Refusal is equally exact and equally local. `Result.refused` proves that every
entry in the checked list is inapplicable; an empty checked list therefore
refuses vacuously. It does **not** prove that the source promise has no repair
outside the list, that the list contains every exit or target promise, or that
an infinite carrier has been enumerated. Over-bound and noncanonical raw inputs
are rejected before search rather than silently truncated or reordered. This
leaf can supply the repair-catalog side of `Preo.Planning`; it does not replace
that module's separate finite schedule/action search.

### Finite history runtime: exactly what became executable

[`Uwueave.HistoryRuntime`](Uwueave/HistoryRuntime.lean) proves that the
`PairDecision.refused` branch is impossible under an explicit covering finite
`Enumeration`, and uses that result to construct a total selector whose scope
contains every pair on the same enumerated DAG. The merge kernel and conflict
reconciler are still caller-supplied. Its higher-judgement sweep is finite and
proof-carrying, but semantic `Decidable` procedures are explicit inputs rather
than synthesized from arbitrary state, observation, or protocol types.

The same module can materialize one selected admission as a fresh `V ⊕ Unit`
merge version with a `Coherent` extended history. It does not yet allocate an
unbounded sequence of fresh names or construct arbitrary repeated criss-cross
growth. Separately, its caller-ID event runtime executes a six-event finite
fixture with two sibling admissions, two criss-cross merges, and a successor.
Immediate `append` refuses a missing parent. `DeliveryState` instead exposes a
bounded out-of-order policy: exact retry is idempotent across materialized and
pending stores, a reused ID with different content is a collision, self and
duplicate parents are refused, and an unresolved event is buffered only while
capacity remains. Once parents arrive, a finite drain materializes ready events;
causal and reverse delivery settle to the same event set and view.

The buffer bound is an operational invariant proved from `DeliveryState.empty`:
`DeliveryValid` is preserved by successful receives, including the exact
capacity-preservation theorem. Arbitrary public record values should not be
read as authenticated or reachable states. IDs are caller-supplied equality
keys, not hashes or identities, and Lean requires only duplicate-free parent
lists rather than the Rust journal's canonical strictly increasing parent
order. This event machine is not a construction of repeated proof-indexed
`History` values.

[`Uwueave.PersistentHistoryRuntime`](Uwueave/PersistentHistoryRuntime.lean)
instantiates checked replay and checkpoints for immediate append and bounded
delivery. A delivery cursor's accepted sequence is the authoritative arrival
log, so it includes records that remain pending; `DeliveryCursorCoherent` ties
that sequence to the materialized-or-pending stores, and replay from empty
validates checkpoints, including a buffered prefix followed by a settling
suffix.

Rust `HistoryJournal` supplies the pure-Rust `RawJournal` host rung for
immediately causal events. `BufferedHistoryJournal` is intentionally different:
only ready events reach the physical journal, its bounded pending map is
volatile, and reopen loses those pending arrivals. It can converge after two
successive/criss-cross merges when every event is eventually delivered.

`HistoryArrivalJournal` closes that volatile-pending deployment gap with a
distinct checksummed wire. Every accepted event record is appended before its
in-memory materialized/pending transition; bounded missing-parent arrivals
therefore survive reopen and later drain deterministically in event-ID order.
Exact retry is no-write, ID collision and buffer overflow refuse before write,
and canonical checkpoints bind capacity plus the accepted, materialized, and
pending maps. Torn/corrupt/version/capacity/checkpoint failures are covered by
focused recovery tests. “Durable” is still relative to the selected
`SyncPolicy` and the host filesystem's promises.

Lean exposes `DurableArrivalCallbacks` as a typed receive/reopen contract equal
to `deliverySchema` replay from an empty capacity-bound cursor. No theorem says
the Rust codec implements it: Lean permits any duplicate-free parent order,
while Rust requires strictly increasing parent IDs, and no bytes/schema
relation connects the languages. The cross-boundary V4 fixture proves exact
opaque bytes survive pending reopen and drain—and deliberately proves that a
mutated payload under a fresh event ID is stored too. Persistence is not
authentication. None of these runtimes enumerates arbitrary or infinite DAGs,
lifts the proof model beyond its `Type 0` boundary, authenticates IDs, proves
filesystem/device premises, or bridges opaque payload bytes back to
`SelectedAdmission`/`Coherent` proofs.

[`Uwueave.FiniteHistoryDelivery`](Uwueave/FiniteHistoryDelivery.lean) now
supplies the strongest honest bridge at that last boundary: a caller-authored
finite presentation, not an automatic reconstruction. `FiniteGrowth` takes an
existing `History`, `HistoryMerge`, and implementation, then requires an
explicit complete duplicate-free version list and an event list whose payloads
are exactly those versions. The caller also supplies stable equality IDs,
injectivity over the finite presentation, exact ID and parent lists for every
`Origin.root`/`ran`/`merged` node, parent closure, history coherence, ancestor
selection, and `PolicyGenerated`. From those semantic premises,
`view_eq_state` proves that the policy-derived view reproduces every authored
history state.

`DeliveredGrowth` witnesses one successful replay of a permutation of exactly
that event list from an empty capacity-bound delivery cursor. Replay success,
the exact accepted arrival list, cursor coherence, and an empty pending buffer
are fields—they are not inferred merely from `FiniteGrowth`. Two such settled
witnesses for the same growth materialize the same full event set despite
different arrival orders, and hence have equal `eventSetView`s. The positive
fixture instantiates the six-version lock history: root, two branches, two
sibling merges, and their merge, delivered in causal and reverse order.

This event-set result is not a semantic-history convergence theorem. The leaf
does not derive `SameRecord` from delivered events, and its separate
`semantic_view_eq_of_convergent` and
`semantic_view_eq_of_recordDetermined` helpers still require a caller-proved
`SameRecord` plus the corresponding `HistoryPolicy` premise. It performs no
delivery automatically, decodes no opaque payload, authenticates no stable ID,
and states no relation to the Rust journals or filesystem. Collision, self
parent, and duplicate-parent refusals are executable runtime fixtures, not
proof that arbitrary host bytes denote this authored history.

The combined fail-closed gate is copy-pastable from the repository root:

```sh
scripts/wave29-finite-canaries.sh
```

Its frozen acceptance set is an executable runner plus 11 Lean files: one
shared support file, two positive fixtures, and eight standalone red fixtures
(**389 lines total**). The latest functional run took **11.2s**. Repair-menu
reds pin the least authored ID, full price, exact-list refusal, size bound, and
canonical order; history reds pin ID collision, self-parent, and
duplicate-parent refusal. Declaration-prefix floors cover 228
`FiniteRepairMenu` constants, 63 `FiniteHistoryDelivery` constants, and 61
shared-support constants; all were clean, with no `native_decide`, `sorry`,
`admit`, or `axiom`.

At this checkpoint the aggregate census is 185 Lean source modules / 186
full-build jobs and 162 direct proof-root imports excluding `Audit`, with
25,747 constants checked by the total axiom gate, 731 MAP keystones and 135
documented transports. Exact
benchmark-facing API/output goldens are available without rebuilding
dependencies:

```sh
PREO_BENCH_SKIP_BUILD=1 scripts/preo-bench.sh wave29-golden
```

That gate passed five exact repair outputs, six exact history outputs, and the
API-status contract. Serialized `lean -j1 --profile` plus `/usr/bin/time -lp`
(two warmups, median five, no cache clearing or trace profiler) measured repair
RSS growth at **441,344 B/item** with **0.1885 ms/item** elaboration growth, and
history RSS growth at **440,320 B/item** with **0.2145 ms/item** elaboration
growth; both RSS slopes pass the 4 MiB/item cap. The new APIs had only a frozen
header-only `MISSING_API` baseline, so comparison reports
`NO_BASELINE_MISSING_API`, not a historical speedup. Repair N16 remained
infrastructure-noisy after nine retries (wall MAD 10.576923%, user MAD 2.5%);
the other rows finished noise-free. The earlier kind-1 syntax all-target Cargo
checkpoint was **148/148 green** in **31.02s real**, including **0.14s** of warm compilation;
the later context-projection closure is 15 objects / 1,049,544 B. These are checkpoint
measurements, not substitutes for the
executable gates.

The final serialized whole-tree gate
`CARGO_BUILD_JOBS=1 cargo test --all-targets -- --test-threads=1` passed
**177/177** tests in **125.72s real** after **10.49s** compilation, with
**35.60s user**, **37.86s sys**, and **1,274,494,976 B** maximum RSS. The
10-test authenticated-runtime matrix
accounted for 85.31s because it repeatedly launches the Lean-owned corpus;
this is fail-closed regression evidence, not a latency or throughput benchmark.

## 1. The thesis

> **preoscript rejects a budget using a semantic lower bound, accepts one only
> with a witnessed upper bound, and never lets a number or a singular UI value
> erase the strategy, fork, future, or premise that justified it.**

That sentence is not ours. It is the corrected thesis an external reviewer
handed back after refuting our first one, and we adopted it because it is
better. Our original — "a language whose types carry a coordination budget" —
was a scalar, and a scalar is not soundly compositional (§4.1).

## 2. The name is the first rule

`preo` = **preorder**. There are at least four live in this system, and
conflating any two of them produces false theorems (we produced one, and
retracted it):

| preorder | meaning | module |
|---|---|---|
| `⊑` | lattice order (`x ⊔ y = y`) | `Confluence.lean` |
| causal reachability | some history prefix reaches this state | `CausalReach.lean` |
| delivery-future | only already-issued events may arrive | `Evidence.lean` |
| extension-future | new application writes are permitted too | `Evidence.lean` |

**In preoscript you cannot write a stability claim without naming which future
you mean.** `Evidence.futures_not_interchangeable` is why: a query can be final
under delivery and open under extension. And the futures are *nested*, not
independent — delivery ⊆ extension — so stability under the larger implies
stability under the smaller, and the reverse coercion is invalid. That
subtyping direction should be a theorem the language derives, never a rule it
asserts.

The pun is deliberate and we are keeping it: a `preo` declaration
**pre**scribes what runs free and **pro**scribes what cannot afford itself.

## 3. What the language must say that the library cannot

The library classifies. A language must retain things that ordinary theorem
calls discard:

1. the **globally shared** repair choice (§4.1);
2. **unresolved future obligations**, per position;
3. **status-dependent downstream restrictions** (a fork you may not silently
   collapse);
4. **promise changes** introduced by a repair — arbitration buys agreement and
   spends monotonicity, and a solver that "meets the budget" by quietly solving
   a different application problem is the failure mode;
5. **composition before optimization**;
6. **proof-carrying synthesis results**.

If a design can be expressed as a tactic call plus a report, it does not need a
language. These six cannot.

## 4. The coordination effect

### 4.1 Not a number — a profile

Our first design graded a session by a count of "meetings". It fails under
composition:

```
min_σ (c₁ σ + c₂ σ)   ≠   (min_σ c₁ σ) + (min_σ c₂ σ)
```

The right-hand side lets each stream pick its *own* best seam; the left-hand
side correctly demands one globally coherent choice. Our own
`Cost.no_seam_frees_both` is the witness: two streams, each free under some
seam, with **no single seam freeing both**.

So a coordination grade is a **cost profile over the strategy space**,
`P : Σ → Nat`, composed **pointwise**, and minimized only when the session
closes. In practice the elaborator retains symbolic strategy variables, the
constraints over them, a cost expression conditional on each choice, and the
proof terms establishing each route's validity — and the solver chooses after
composition, never before. (`Uwueave/CoordEffect.lean`.)

### 4.2 A floor rejects; only a plan accepts

```
Floor(spec, W)  ≤  Cost(plan, W)  ≤  Budget
```

`Cost.coordination_forced` gives the left inequality — a bound forced by what
you *promised*, independent of implementation. It licenses **rejection** and
nothing else. `floor ≤ budget` does **not** license acceptance; accepting
requires exhibiting a plan and proving its upper bound.

Hence three outcomes, not two (`Uwueave/Budget.lean`):

```lean
inductive BudgetVerdict
  | accepted   (plan : Plan) (upper : plan.cost ≤ budget)
  | rejected   (floor : budget < unavoidableFloor)
  | unresolved (obligation : SynthesisObligation)
```

`unresolved` carries what would have to be exhibited. It is not the
honest-label sin, because it names its own remaining work.

### 4.3 Crossings are not meetings

`Cost.lean` counts **seam crossings**. It models no attendance, no coalescing,
no barriers, no elapsed time. So a session budget must say which currency it
means, and the language should not offer a single word that hides five:

```
peer barriers · arbiter cuts · network rounds · user prompts · rollbacks
```

Calling all five "meetings" manufactures attractive false zeroes. A meeting is
a *scheduling interpretation* over demands with scope, participants, epoch,
evidence and rounds. `Uwueave/Scheduling.lean` now builds that interpretation:
proof-carrying obligations compose pointwise under one shared strategy, a
schedule witnesses coverage, and five currencies remain separate. Its exact
2-crossings→1-meeting, 0→1, and 1→2 examples prove there is no scalar
conversion in either direction. The standalone `preo_budget` command now
accepts an existing five-currency `ProfileUpperBound` for an exact generated
session. What remains unbuilt is *unbounded* schedule discovery and the prettier
inline budget block—not witnessed budget acceptance, the bounded authored search
in `Preo.Planning`, the protocol AST, its proof-carrying elaboration, or the
scheduling judgement. `Protocol.Term` carries the bounded
operation/sequence/parallel/choice/repeat/sync language. An inline `preo`
protocol accepts a typed term in that AST; the standalone `preo_protocol`
command gives all six constructors a parser-safe native spelling and expands to
that same semantic API.

### 4.4 Prices are records, not numbers

Arbitration does not cost "0". It costs a trusted announcement and rollback
exposure. Exposing a fork costs the singular-output contract. Escrow costs
rights allocation and metadata. Retaining evidence costs storage and replay.
So a price is a record with fields, each justified by a theorem in the tree or
omitted (`Uwueave/Repair.lean`), and a deployment supplies its own valuation
`Price → Cost` — because a team that considers rollback catastrophic and
metadata cheap should not be forced to share a scalar with one that does the
opposite.

## 5. Results carry their epistemic status

### 5.1 Static capability vs runtime status

`derive verdict : Forked Claim` is ambiguous: does it mean *every* evaluation
forks, or that this computation *may* fork? It means the second, so the
declaration should state **capability** (`mayOpen`, `mayFork`) and evaluation
should return a **status view**. Two axes, not one.

### 5.2 The status space is bigger than four

Candidates × closure gives at least six cells, because zero candidates is a
real state and its two closures mean different things:

| candidates | open | closed |
|---|---|---|
| zero | nothing observed yet | **definitive absence** |
| one | provisional singleton | exact singleton |
| many | open fork | closed fork |

`Evidence.lean` ships five constructors (`vacuous` is the zero case, named
rather than folded away). Visibility — produced-but-uninspectable, from
authorization, encryption, laziness, or an opaque remote — is an **independent
axis**, not a sixth constructor, so the underlying evidence stays factored and
the four common views are *derived*.

### 5.3 Exactness is indexed by a future, and often by a value

`Exact Delivered α` and `Exact Working α` are different claims, and
`Exact Working α <: Exact Delivered α` because surviving the larger future set
implies surviving the smaller. That coercion must come from a theorem about
future inclusion, never an ad-hoc subtyping rule.

And exactness is frequently *value*-dependent. For an existential over a
grow-only set, `true` is self-certifying — no future retracts it — while
`false` stays open until closure. So the honest result is not "this Boolean
becomes exact after a seal"; it is one epistemic carrier whose status depends
on the value it currently holds.

### 5.4 Futures range over worlds, not states

Two replicas can share a materialized state and differ in issued-but-undelivered
events, frontier, seals, roster, capabilities, and known merge bases. So
`DeliveryFuture` cannot be defined from the state alone, and an exactness
certificate that escapes its frontier or epoch context is unsound under reuse.
(`Uwueave/WorldFuture.lean`.)

### 5.5 Resolution must compile — auditably

"You cannot silently collapse a fork" is right; "you cannot ever pick one" is
wrong. The enforceable property is:

> **No branch selection occurs through an implicit coercion.**

So resolution is explicit and *retained in the type*: `resolve verdict by
era_order` yields `ResolvedBy EraOrder Claim`, carrying the policy and — where
disclosure rules allow — the suppressed alternatives.

## 6. Field kinds: capabilities, not a record

`MergeState` cannot be mandatory. A join CRDT, an op-replay structure, and an
MRDT with a merge base have genuinely different merge signatures — and
`Ancestral.join_is_ancestral_merge_iff_trivial` proves a join *is* a three-way
merge only on a one-point carrier. One mandatory binary interface would either
lie about three-way merge or discard the base uncertainty that makes it
valuable. So merge is a **model** with a context type
(`Uwueave/MergeModel.lean`), and a field kind supplies *layered* capabilities:

| capability | supplies |
|---|---|
| `MergeModel` | carrier, merge context, outcomes, laws |
| `OperationalModel` | operations, local admission, issued evidence |
| `ReachabilityModel` | worlds, reachable executions, live witnesses |
| `FutureModel` | named futures and their inclusions |
| `ClosureModel` | frontiers, seals, finalization certificates |
| `ObservationModel` | result domain and its approximation order |
| `FootprintModel` | read/write scope and independence |
| `FiniteEvidence` | finite support and materialization |
| `ExecutableModel` | codec, kernel, refinement theorem |
| `DisclosureModel` | what provenance may be shown, to whom |

A new paper should add one capability and some rules — never extend a universal
`FieldKind` record.

**Verdict routes do not live inside field kinds.** A rule like *"monotone
summary + upward-closed invariant ⟹ confluent pullback"* is not part of G-Set
identity; it applies to anything satisfying its premises. Routes belong in an
extensible `RuleSet` where every route returns a proof-carrying verdict, so
search order may change performance or which explanation you get, but never
soundness.

⚠ That last sentence is no longer a design intention — it is
**`Preo.run_answer_congr`**, and the surface is built on it
(`Uwueave/Preo/Classification.lean`). Read what it does and does not say: the
*answer* is invariant under any membership-preserving change of registry; the
*explanation* is a list, and which one a report prints first is a separate
policy. The proof is not bookkeeping — it reduces to `Preo.verdict_agree`, that
a `free` and a `clash` for one invariant are contradictory **terms**, so the
disagreement a first-match order was protecting against cannot be constructed.

**Exits are morphisms between specifications** — source merge model and promise
to target merge model and promise — not values in a per-field list.

**Composition needs formulas, not badges.** If a component exports only
`FREE`/`ESCALATES`/`SEAM`, the information needed to compose relationally is
already gone: composition needs the invariant, its footprint, its reachability
assumptions, the selected future, the strategy variables, and the promise
deltas.

## 7. The surface

Promises and prices, not fields and annotations — because a surface of
decorated struct fields can only classify what we already know how to classify.

```
preo Swarm where
  field findings : GrowSet (Agent, Claim)
  field holds per Agent : Slot File
  field spent per Agent : Escrow Tokens
  field roster : EraGroup

  invariant one_writer : ∀ f, |{a | holds a = f}| ≤ 1
  invariant in_budget  : ∀ a, spent a ≤ alloc a

  future Delivered on (Future.evidenceWorldModel Holes.Val) :=
    Future.Delivery Holes.Val
  future Working on (Future.evidenceWorldModel Holes.Val) :=
    Future.Extension Holes.Val

  typed derive next_score over {
    schema := [.nat, .nat],
    reach := [before, afterRemote, afterLocal]
  } := .natSucc (.field 0)

  derive anyone_found : Bool = ∃ (a,c) ∈ findings, c = target
  derive open_files   : Nat  = |files \ range holds|

  protocol WaveProtocol over TeamStrategy := waveProtocol
  session Wave under TeamEra runs WaveProtocol at chosenStrategy := chosen_is_admissible
```

The typed-term form above is the expert escape hatch. The native spelling is a
separate command with a punctuation-delimited recursive body:

```
preo_protocol WaveNative over TeamStrategy at chosenStrategy :=
  .seq [
    .operation { id := 1, crossings := 0, needs := [] },
    .repeat {
      count := 2,
      body := .sync {
        currency := .userPrompt,
        participants := [0],
        scope := 0,
        epoch := 0,
        evidence := .none,
        round := 0,
        barrier := 0 } } ]
```

It emits predictable `Term`, `Elaboration`, `Session`, `Plan`, `Limits`, and
`ProfileUpperBound` constants. Choice is nonempty and selected by an explicit
natural in this first deterministic fragment; crossing origins are bounded by
the operation's written crossing count.

Note what the session result carries that our first sketch did not: a checked
**schedule/plan**, a **multi-currency cost profile**, and an actual **protocol
shape**. The standalone `preo_budget` surface now accepts a limit only by
consuming a `Scheduling.ProfileUpperBound` — one real plan satisfying all five
currency coordinates for the exact named session. It performs no schedule
search. An `allows` list
naming an operation vocabulary is not a workload — if `reallocate` may repeat
without bound, no finite worst-case bound follows from membership in a list.
The field, invariant, future, typed-derive, ordinary-derive, protocol and
session forms shown here are live. `typed derive` is parser-hard at the braces
and `:=`: `Raw.infer` must produce an intrinsically typed `Expr.Term`, after
which the command exposes exact positional `Holes`, erased `Reads`,
proof-carrying `MergeSafe?`/`MonotoneSafe?`, and a checked cache/update chain
(`updateCache` promotes each proved result without reevaluation).
Its written finite `reach` also feeds a real `ResultProgram.CheckedDeclaration`:
the generated default is an exact singleton result under the equality future,
with preserve-fork resolution and explicit inspectable/shown policy, plus a
checked six-status report at the reference carrier. `reportAt` requires proof
that its environment belongs to the written reach and retains that proof in a
`ReachReport`, tying every generated report to the effect-inference domain; an
empty reach therefore cannot report.
Malformed operators,
out-of-range fields and raw `.custom` fail the entire row before any typed term
or analysis is emitted. A future must name its full
`Preo.Future.WorldModel`, so no declaration can be inferred from materialized
state alone. An inline protocol body remains a typed Lean term of
`Protocol.Term TeamStrategy`, the deliberate opaque escape hatch. The native
`preo_protocol` parser does not duplicate protocol semantics: it expands its
six data-shaped forms into that same `Protocol.Term`, calls
`Protocol.elaborate` once, and exposes the checked schedule and exact
five-currency bound. Inline sessions call
`Protocol.elaborate`/`elaborateProfilePlan` once and expose their checked
schedule and upper bound. Certificates and budgets remain parser-safe
standalone commands whose dependent types are ordinary Lean terms:

```
preo_certificate Quiesced :
  Future.CheckedCertificate Swarm.Delivered answer key accepts exactWorld := proof

preo_budget WaveLimit for Swarm.Wave : fiveCurrencyLimits := checkedProfileBound

preo_export SwarmManifest from Swarm : hostValidationConfig :=
  declaration := { id := 100, stateType := 101, schema := 1 }
  | field findings := { id := 102, kind := 10, carrier := 103, key := none }
  | invariant one_writer := {
    id := 104, carrier := 103, codec := findingsCodec, answered := rfl }
  | future Delivered := {
    certificate := Quiesced, id := 105, world := 106, relation := 107 }
  | budget WaveLimit for Wave := {
    id := 110, session := 108, plan := 109,
    samePlan := checkedProfileBound_is_wave_plan }
```

`preo_certificate` requires its written type to reduce to
`Future.CheckedCertificate`; it never infers an index from materialized state.
`preo_budget` pins `checkedProfileBound` to `Swarm.Wave.session`. The earlier
pretty in-declaration budget block and schedule synthesis remain unbuilt.

`preo_export` is a checked manifest rather than a report serializer. It starts
one `Export.DeclarationBundle` at the generated state and folds each row
directly through the corresponding proof-indexed builder. Field rows name the
generated carrier; invariant rows require an existing answered classification
equality and an explicit `FirstOrderCodec`; future rows require the exact named
certificate; session rows accept only a `Protocol.Elaboration`. Numeric IDs are
written data—not hashes of Lean names. The command emits the checked bundle,
artifact, canonical encoding, durable format/bytes, raw V2 projection, explicit
validation result, private validated value and deterministic rendered source.
Its kernel-computed validation gate rejects duplicate stable IDs and malformed
references at compile time. An unresolved invariant has no `answered` proof, a
certificate for another future/world does not typecheck, and a composed
`ProfilePlan` is refused until `DeclarationBundle` grows a semantic builder for
that shape. A budget row is also the session/plan row: it calls
`addElaborationWithBudget` and requires an explicit proof that the named
`preo_budget` carries exactly the elaboration's plan. A valid bound for a
different plan of the same session is refused rather than silently relabelled.
The encoding retains its five written limits and five realized coordinates.
Decoding remains one-way first-order data and never reconstructs a verdict,
certificate or scheduling plan.

### 7.1 Deep only where analysis requires it

Every deep constructor is a case in every theorem forever. The live typed core
therefore stays deliberately first-order: booleans, naturals, products,
options, typed field reads, boolean operations and natural operations. It is
already enough for sound structural dependency extraction, positive merge/monotonicity
certification, checked incremental reuse and a six-status result adapter.
Sessions independently get operation, sequence, parallel, finite choice,
bounded repetition and synchronization. Everything else keeps the ordinary
Lean `derive` escape hatch:

```
derive custom = opaque LeanFunction
  monotone by …   mergeable by …   status by …   footprint by …
```

An expert adds a computation without teaching every theorem to recurse through
arbitrary Lean syntax. That escape hatch receives only the theorem-backed
mergeability routes it actually matches; it does not acquire typed-program
reads or cache laws by inspection.

One boundary is explicit: a typed row's authored `Expr.Schema` and `Expr.Env`
are not silently identified with the surrounding declaration's generated
`State`. An application that wants document evaluation writes a
`State → Expr.Env Schema` projection and calls the emitted `.Eval`. The
elaborator currently makes no field-name/type coercion claim.

### 7.2 Robust proof and work boundaries

Production code that only needs the proposition-closing `classify` tactic,
finite enumerations, probe search, or the small proof idioms may import
`Uwueave.Tactics.Core`. Code that needs `Spec.Verdict` values,
`classifyIn?`/`classify?`/`classifyFinite`, or the `verdict` tactic should
import `Uwueave.Tactics.Verdict`; it already imports `Core`. The larger
`Uwueave.Tactics` module is the demonstration suite and deliberately imports
additional domains.

Automatic tactic work is bounded. The exhaustive route used implicitly by
`classify` and `verdict` accepts at most 64 enumerated states and 4096 ordered
pairs. An over-cap or nontransparent `FinEnum` spine is a loud typed resource
refusal, not a route miss; unexpected internal failures are likewise not
silently converted to inapplicability. The explicit value function
`classifyFinite` remains logically total and has no implicit work cap. “Total”
describes its result type, not its compile-time cost.

There is one narrower current Preo caveat: an invariant over a carrier with
both `FinEnum` and `DecidablePred` makes the elaborator emit the explicit,
uncapped `classifyFinite` result as an accumulated facet. A supplied verdict
does not suppress that route, because applicable facets are accumulated rather
than chosen first-match. Until the elaborator shares the tactic work gate, keep
automatically enumerable Preo carriers small or avoid installing `FinEnum` for
a large carrier.

Two recursive generators also have semantic simp interfaces on purpose:

- For `Preo.Planning.actionChoices`, use
  `mem_actionChoices_iff_sublist` and `actionChoices_length`. Do not normalize
  `actionChoices_cons` across a large action list: it materializes `2^n`
  candidates. Runtime-facing construction should use `checkActionUniverse`,
  which rejects duplicates and a caller-supplied `maxChoices` bound before
  materialization. That bound is authored policy, not a global system ceiling.
- For bounded protocols, use `repeatSession_crossings` and
  `repeatSession_demands` to simplify observations. The structural
  `repeatSession_zero`/`repeatSession_succ` and
  `repeatDemands_zero`/`repeatDemands_succ` equations are explicit `rw` tools,
  not global simp rules. Avoid
  `simp [repeatSession]` at large literal bounds. These observation laws avoid
  proof-normalization blowups; exact denotation still retains the real linear
  repeated demand stream.

### 7.3 One public facade, transactional phases

The implementation is split without splitting the language. The public
[`Uwueave.Preo.Elab`](Uwueave/Preo/Elab.lean) module is the **only** place that
registers handlers for `preo`, `preo_certificate`, `preo_budget`,
`preo_export`, `#preo_report`, and the native `preo_protocol` command. The
modules under [`Uwueave/Preo/Elab/`](Uwueave/Preo/Elab/) expose ordinary,
non-registered worker declarations. Importing a worker therefore cannot
install a second handler for the same syntax or cause a surface command to run.

For a `preo N`, the
[`Declaration`](Uwueave/Preo/Elab/Declaration.lean) orchestrator retains the
historical phase and report-row order:

```
state and fields
  → invariants
  → composed document seam
  → futures
  → typed derives
  → ordinary derives
  → protocols
  → sessions
  → publish report rows
```

This order is semantic compatibility, not a scheduling suggestion. The phases
are not run in parallel, and report rows enter the environment extension only
after all earlier generated declarations have succeeded. Splitting the old
monolith gives Lean smaller recompilation and profiler boundaries and lets a
leaf consumer import less implementation. It does not reduce kernel checking,
change route order, or introduce a second semantics for any surface form.

The shared
[`Internal`](Uwueave/Preo/Elab/Internal.lean) layer makes two kinds of emission
deliberately different:

- `emitRequired` emits a declaration promised by the surface. A thrown
  exception or logged elaboration error restores that command's input
  environment and aborts the enclosing surface command; the diagnostic is
  retained.
- `probeCommand` tries an optional classification or transport route. Failure
  restores its input environment and message log and returns the diagnostic as
  data, so an inapplicable route leaves no declaration and no stray error.
  Success keeps the checked declaration. Macro scopes and name generators keep
  advancing across a failed probe; reusing hidden hygiene state would be less
  safe than leaving that monotone state alone.

Every public mutating core is wrapped in `withEnvTransaction`. If a required
late phase fails, the environment is restored to its state before the whole
surface command: earlier generated constants and any report-extension entries
are both absent, while diagnostics remain visible. The identical user-level
top name can then be used by a later successful command. The executable
[`RollbackReuse`](tests/preo-automation/RollbackReuse.lean) canary checks both
absence and same-name reuse. This is environment atomicity inside Lean; it is
not a filesystem transaction.

The phase split is intentionally **not** a generated-API change. Existing
names, types, emission order, report rows, and route labels remain the
compatibility contract, pinned comprehensively by the
[`names-types-rows.tsv`](tests/preo-bench/golden/expected/names-types-rows.tsv)
golden fixture. In particular, the stable families remain:

- a declaration `N` emits `N.State`; each field `f` emits `N.f.Carrier`,
  `N.f`, `N.f.merge_hom`, `N.f.plant`, `N.f.plant_proj`,
  `N.f.plant_merge`, and `N.f.surj` (plus `seed` and `mergeState` for a custom
  carrier);
- an invariant `i` emits `N.i`, its accumulated `verdict` family and
  `N.i.classification`, with `seam`, `onState`, `seamOnState`, or `obligation`
  only when the corresponding checked route applies;
- futures retain `N.F.WorldModel` and `N.F`; ordinary derives retain their
  `on`, value, `merge`, `classification`, and possible `obligation` family;
  typed derives retain the existing checked program, dependency, incremental,
  result, reach, and report family;
- protocols and sessions retain their term/elaboration, `Plan`, `UpperBound`,
  and where applicable `ProfilePlan` declarations; the native spelling retains
  the exact `Strategy`, `selectedStrategy`, `Term`, `Elaboration`, `Session`,
  `Plan`, `Limits`, `ProfileUpperBound`, and equality-witness surface described
  above;
- `preo_budget B` retains `B`, `B.Limits`, `B.Session`, `B.Plan`, and
  `B.PeerUpperBound`; `preo_certificate C` emits exactly `C`; and
  `#preo_report` emits no declaration;
- `preo_export E` retains exactly `E.Declaration`, `E.Bundle`, `E.Artifact`,
  `E.Projection`, `E.Encoding`, `E.ArtifactDurableFormat`,
  `E.ArtifactDurableBytes`, `E.ProjectionV2`, `E.ValidationConfig`,
  `E.Validation`, `E.validation_ok`, `E.Validated`, `E.Rendered`, and
  `E.RenderResult`, in dependency order.

### 7.4 Explicit durable-artifact emission

Elaboration computes and names durable artifact bytes but performs no I/O.
Writing one of the currently registered real artifacts is an explicit host
action through [`tools/uwueave-preo-artifact`](tools/uwueave-preo-artifact):

```sh
# Show the finite registry and its canonical Lean names.
tools/uwueave-preo-artifact --list

# Write binary bytes to stdout; redirect them, do not print them in a terminal.
tools/uwueave-preo-artifact \
  SemanticExport.ArtifactDurableBytes --stdout > semantic.preo

# Or ask Lean's runner to write a named path directly.
tools/uwueave-preo-artifact \
  ProjectionV2.Examples.fullExport --output full.preo

# The short aliases `semantic-export` and `full-export` are also accepted.
```

Both output modes select bytes from the Lean-owned finite registry in
[`ArtifactEmit`](Uwueave/Preo/ArtifactEmit.lean); Rust does not reconstruct the
artifact. `--stdout` writes only the binary artifact on standard output, and
`--output` leaves standard output empty on success.

The direct-path mode uses ordinary `IO.FS.writeBinFile`, and shell redirection
uses the shell's ordinary file behavior. Neither writes a sibling temporary
file and atomically renames it; neither proves `fsync`, directory durability,
permission safety, path hardening, or crash recovery. A crash or I/O failure
can therefore leave a missing, truncated, or partially replaced output. Treat
the CLI as an explicit byte emitter, then hand the bytes to the durable runtime
or to an application-specific atomic publication protocol when that stronger
host guarantee is required.

## 8. Why it is a UI substrate

The epistemic status of a value determines its widget: `Exact` renders a value;
`Open` renders the value **and** what is pending; `Forked` renders candidates
with provenance; `OpenForked` does both.

Three enforceable properties, and one honest limit:

- **No exact badge without a stability certificate.**
- **No singular extraction from a possible fork without a named policy.**
- **No "fully synchronized" status without naming the scope it is relative to.**
- ⚠ Types enforce *semantic presence*, not **salience**. A correctly typed
  `OpenForked` can still be rendered as one-pixel grey text below the fold. So
  keep constructors abstract, expose total eliminators, require every status to
  be handled, and make exact badges consume certificates.

**Obligations are affordances only when someone can discharge them.** "Waiting
on Bob" is not actionable if the current user cannot request it, Bob has
retired, or the producer set is itself unknown. An actionable obligation needs
an actor, an authorization proof, a precondition, and an effect.

**Provenance may need redaction.** The contract is not "always show every
branch"; it is *no silent selection, and every shown or hidden branch has an
explicit disclosure decision.* A redacted fork is still a fork.

The load-bearing claim we have **not** proved, stated as a hypothesis rather
than a fact: *a recurring class of local-first UI misrepresentations consists
of unproved coercions from open, forked, or scope-relative evidence to an exact
singular presentation.* Checking it needs a defect corpus and a coding
protocol. We are not going to claim "most bugs" without one.

## 9. Synthesis

Two targets, both handed to us by review, both now in the tree:

**Seams are graph colorings.** Build the clash graph — vertices are reachable
legal states, edges join pairs whose merge is illegal — and a valid seam is
exactly a coloring with no monochromatic clash edge. Seam-finding becomes
search, and because a coloring is one **global** object, minimizing over
colorings after composing constraints is sound where per-stream minima are not.
(`Uwueave/SeamColoring.lean`.)

**The coarsest summary is a quotient.** For a query `f`, contextual equivalence
`x ≈_f y ⟺ f x = f y ∧ ∀ z, f (x ⊔ z) = f (y ⊔ z)` is stable under adding
context, and its quotient is the candidate coarsest future-sufficient evidence
domain. Membership collapses to one bit; exact count collapses to nothing; a
threshold query should land in between. (`Uwueave/MinimalSummary.lean`.)

## 10. Status

| feature | backing | status |
|---|---|---|
| FREE / ESCALATES / SEAM verdicts | `Confluence`, `Catalog`, `Ceiling`, `Segmented` | proved |
| clash repro | `escalation_witness` | proved |
| priced exit menu | `Exits` | proved |
| typed repairs + promise deltas | `Repair`, `RepairMenu` | **proved**: generated repairs retain exact promise relations and an eight-axis price, including reachability restriction rather than falsely pricing escrow as free |
| ✅ bounded authored repair-menu search | `FiniteRepairMenu`, `RepairSynthesis` | **BUILT for an explicit checked list.** Search enforces a written size cap and strictly increasing stable IDs, returns the least applicable authored ID with its exact typed repair, row, delta and complete eight-axis price, or proves every listed row inapplicable. IDs are ordering policy rather than price; refusal says nothing about repairs omitted from the finite list. |
| mergeable-vs-replay verdict | `JoinHom.summaryFold_iff_joinHom` | proved |
| epistemic result carrier | `Evidence`, `Holes` | proved |
| future-indexed exactness | `Evidence`, `WorldFuture`, `Preo/Future` | **proved and surfaced**: declarations retain the world model/index; checked stability and certificates project proofs, and only extension→delivery restriction exists |
| coordination floor | `Cost.coordination_forced` | proved |
| cost profiles + composition | `CoordEffect`, `Scheduling` | **proved**: pointwise composition precedes one global strategy choice; schedules retain five currencies |
| budget trichotomy | `Budget`, `Preo.Planning` | **proved**; explicit duplicate-free, pre-capped authored action universes additionally compute an exact witnessed minimum without claiming to enumerate arbitrary schedules or seams |
| merge models | `MergeModel` | **proved** for join, ancestral and op-replay models, now universe-polymorphic at the generic model layer |
| seam synthesis | `SeamColoring`, `MenuTotality` | **proved for explicit finite carriers/palettes**, including exhaustive refusal and a least-width certificate; infinite search remains outside the result |
| summary synthesis | `MinimalSummary`, `TextSummary` | **proved semantically** through contextual quotients; the fixed text window now has an exact iff, while executable quotient construction for arbitrary evaluators remains open |
| arbitrary refined outcomes | `Specification` | **proved semantically**: under totality, coordination-freedom is exactly history monotonicity plus fiber directedness, and `IConfluent` is the singleton-outcome instance |
| classification → `Verdict` term | `Tactics.classifyFinite` (`Uwueave.Tactics.Verdict`) | **proved**; the explicit total function is uncapped, while automatic tactic routing has a 64-state/4096-pair work gate |
| surface syntax + elaborator | `Preo/Syntax`, `Preo/Elab`, `Preo/Demo`, `Preo/ProtocolSurface` | **built**: built-in and explicit-seed application carriers, invariants/ordinary derives, intrinsically typed derives with exact dependencies + checked incremental/result/report artifacts, keyed fields, named world futures/certificates, typed-term and native protocols, proof-carrying sessions, five-currency budgets and explicit checked export manifests |
| classification ACCUMULATES facets | `Preo/Classification` | **built**: `Classification` holds `global`/`seams`/`mergeability`/`obligations` as *lists*; rules add, never replace |
| route-order invariance | `Preo.run_answer_congr` | **proved**: two registries with the same rules in any order certify the same answer. Bottoms out in `Preo.verdict_agree` (two verdicts for one invariant cannot disagree — the pair is uninhabitable), not in bookkeeping. `run_answer_of_perm` is the permutation corollary. |
| ✅ seam verdicts in the surface | `Preo.budgetSeam`, `Preo.seamAlong`, `Segmented.budget_segmented` | **CLOSED** (was "inexpressible"). A globally clashing invariant now carries a `SegVerdict` facet *alongside* its clash — `Preo.seam_forces_clash` proves a seam is not a third alternative but forces the ESCALATES column. `Demo`'s `LoomDoc2.in_budget.seam` **is** `WeaveState.quotaVerdict`, by `rfl`. `seamAlong` lifts it to the whole declared document, using the emitted section (`<field>.plant`) that fragment 1 said the elaborator could not synthesize. |
| ✅ cross-field invariants in the surface | `Spec.Verdict.cross`, `Spec.pointsAtExisting_iconfluent` | **CLOSED** (was refused by name). A two-field invariant is classified against the *product* state; `LoomDoc2.fk` **is** `Spec.refIntVerdict` by `rfl`. The keyed form is also live: `KeyedDoc.fk.verdict` is `WeaveState.bookmarksVerdict` by `rfl`. Three or more fields is still refused: `Verdict.cross` is binary. |
| ✅ `derive` + mergeability verdict | `JoinHom.Fourth`, `summaryFold_iff_joinHom`, `Preo.mergeability_comp` | **CLOSED**. `derive n : T = <expr>` emits the computation plus a `Fourth` facet with its `Fourth.Correct` proof. Registry: ∃-read, filtered view, high-water mark, set image (`fromResults`) and count (`needsEvidence`, via `no_count_merge_without_provenance`) — each *attempted by typechecking*, so an unknown shape is an obligation, never a guess. ⚠ the `needsEvidence` transport to document scale needs the projection **surjective**, not merely a hom; the elaborator emits `<field>.surj` for exactly that. |
| ✅ typed program + local runtime/result adapter | `Preo.Expr`, `Preo.Incremental`, `Preo.ResultProgram`, `typed derive` | **BUILT for the first-order local evaluator.** `Raw.infer` is retained by an exact success witness; positional holes/reads, positive merge and monotone proof options, checked chained cache/update correctness and off-dependency zero work are emitted from that one term. An authored finite reach produces a least six-status effect and proof-carrying reach-indexed checked reports under the explicit equality future/preserve-fork/default disclosure policy. `ObservedBoundResult` can additionally attach a caller-proved authentic running-reach observation at the exact world. `preo_export_v3` projects that exact observed typed program into checked V3 rows; the legacy V2 `preo_export` surface remains unchanged and does not gain a typed-program member. Arbitrary Lean stays in ordinary `derive`; document-State projection and non-equality futures require explicit application proofs. **Still unbuilt:** wiring `ContextCompiler` summaries into this command and observing/authenticating a deployment without caller premises. |
| ✅ **seam composition in the surface** | `SegVerdict.selfSeam`, `liftFst`/`liftSnd`, `andSeams`, `absorbFree`, `prependFree` | **CLOSED at the general surface/combinator layer.** `TwinQuota.documentSeam` is the existing product seam by `rfl`; `NestedSurface` finds two seam rows through eight right-nested fields and absorbs six checked FREE rows; the general algebra reconstructs `WeaveState.weaveDocSeamVerdict` as the same value. `GroupedCarrierSurface.State` now **is** `WeaveDoc` by `rfl`, with the explicit `core₀` seed. The remaining exact full-surface obstruction is narrower: built-in `Quota` plants structural zero, which is not `BudgetInv 10`; the surface cannot silently substitute the invariant-specific `quota₀`. |
| ✅ **`per` / keyed families in the surface** | `Confluence.keyed_cross_iconfluent`, pointwise `MergeState` | **CLOSED for field carriers and keyed referential integrity.** `field bookmarks per Bool : GrowSet Nat` emits `Bool → GSet Nat`; `KeyedDoc.fk.verdict` is `WeaveState.bookmarksVerdict` by `rfl`. Unsupported keyed relations remain obligations, and automatic keyed clash seams still require a concrete key/default witness. |
| ✅ **named world futures in the surface** | `Preo.Future.FutureDecl`, `WorldIndex`, `CheckedStability`, `CheckedCertificate` | **CLOSED.** `future N on M := D` checks `D : FutureDecl M`; `preo_certificate N : CheckedCertificate ... := proof` retains the complete world index and is whole-value `rfl` to the hand certificate. Same-state/different-world refusal and one-way delivery⊆extension variance remain theorem-visible in `Demo`. |
| ✅ **protocol/session surface** | `Protocol.Term`, `Protocol.Elaboration`, `Preo.ProtocolSurface`, `elaborateProfilePlan`, `elaborateComposedProfilePlan` | **CLOSED with both a typed opaque body and native `preo_protocol`.** The native command covers operation/sequence/parallel/nonempty choice/bounded repeat/sync and emits the exact elaboration, session, plan and five-currency bound. Inline sessions expose checked plans/upper bounds and composed profiles select one global strategy. Reports name semantic artifacts and deliberately contain no invented verdict bit or meeting scalar. |
| ✅ **five-currency budget surface** | `Scheduling.ProfileUpperBound`, `preo_budget`, `Preo.Planning` | **CLOSED for witnessed acceptance and bounded authored search.** A standalone command consumes one real plan satisfying `Currency → Nat` pointwise at the exact generated session. `Demo` rediscovers `coalescedProfileUpperBound` by `rfl`; separate theorems refute acceptance from crossings or a peer-meeting floor. `Preo.Planning` searches only a duplicate-free, pre-capped authored action universe. **Unbuilt:** arbitrary schedule discovery and a pretty inline budget block. |
| ✅ **first-order checked export** | `Preo.Artifact`, `Preo.Export`, `Preo.ArtifactDurable`, `Preo.ProjectionV2`, `preo_export` | **BUILT AND SURFACED.** Private proof-indexed builders project answered classifications, certified world futures, ordinary/profile protocol elaborations and exact-plan five-currency budgets into one canonical first-order artifact. The manifest supplies every stable ID, witness codec and budget plan equality explicitly; it emits canonical durable bytes and must pass V2 structural/resource validation before rendering. Unresolved invariants, wrong certificates, wrong-plan budgets and duplicate IDs fail closed. Published V1 remains the budget-empty legacy schema. Composed profile plans wait for a dedicated checked export builder; decoded wire tags have no path back to semantic proof constructors. |
| ✅ **authenticated observed V3 export** | `Preo.ObservedBoundResult`, `Preo.ArtifactV3Checked`, `Preo.ProjectionV3Core`, `Preo.ArtifactV3Surface`, `preo_export_v3` | **BUILT AND SURFACED for one exact observed typed program.** The command consumes separate authenticity, running-reach, authored-reach, certificate, plan and budget proofs; projects checked query/result/world/certificate rows plus positional reads/holes/analyses/effects; enforces work and validator resource caps; and publishes only after the whole environment transaction succeeds. Canonical bytes are generically framed under the distinct V3 format tag. The caller still supplies observation/authenticity and stable name registries; decoded validation cannot reconstruct proofs or check every semantic association. |
| ✅ authenticated frontier + consuming world context | `AuthenticatedFrontier`, `AuthenticatedWorldContext` | **PROVED for explicit deployment premises.** A signed, received, genuinely issued progress event is conjoined with a lawful delivery advance; exact signed positions, active causal grants and fresh consumption tombstones justify each newly delivered candidate. Stale version, wrong origin and consumed-token reuse refuse. No signature hardness, network observation, roster completeness or host execution is inferred. |
| ✅ authenticated ERA delivery certificate | `AuthenticatedEraCertificate`, `EraCertificate` | **PROVED as an exact model-level bridge.** One signed, received and genuinely issued progress event is joined to a separate complete, lawful ERA announcement at the same decoded event; this yields `Settled`, an exact-key reusable `settledCert`, and role sealing under `Delivery`. Cut membership need not be newly added, canonical-candidate equivalences do not exclude malformed extra frontier points, and no free-termination result is claimed for `Announcement`, `Issuance`, or `fullView`. Cryptography, decoding and deployment premises remain external. |
| ✅ runtime-auth V4 syntax, projection, host admission + sidecar | `RuntimeAuthV4`, `RuntimeAuthV4Kernel`, Rust `auth_runtime`, `RuntimeAuthV4Checked`, `RuntimeAuthV4Durable`, `RuntimeAuthV4Projection` | **BUILT as separated boundaries.** Legacy request kind 1 retains its five-refusal syntax checkpoint. Context-bound kind 3 signs an opaque context commitment and reaches Lean-owned decode, shape, host-width and exact kind-4 projection. The raw-only host runtime fixes document/genesis/context/execution scope, then orders scoped verification, journal identity classification, pinned context, provider+execution index agreement, independent authority/membership, concrete Lean move preflight, append and in-memory commit; the checked journal body stores the execution binding and externally pinned recovery revalidates the exact prefix. Definite storage refusal is distinct from indeterminate I/O. The focused suite is **10/10** green. Separately, exact `ReadyForExecution`, active grant and finite context produce neutral canonical format-`⟨4,162⟩` rows/bytes and a validated Rust DTO. Host policies and the external pin remain trusted; sidecar decode/render/storage reconstruct no verifier, authority, membership or frontier proof. |
| **declaration composition** | `Preo.Export.DeclarationBundle` is one checked declaration bundle, not composition | **unbuilt across declarations**: composing two independently authored declarations still needs formulas, footprints, futures, strategies and promise deltas rather than concatenating artifacts |
| ✅ **scheduling judgement** | `Scheduling.Session`, `Obligation`, `Schedule`, `ProfilePlan`, `ProfileUpperBound`, `Protocol.Term`, `Preo.Planning` | **built and surfaced**: typed origins, metadata-rich demands, separate currencies, witnessed pointwise limits, bounded protocol semantics, shared-strategy composition, bounded authored action-subset search, and exact crossing/meeting non-function refutations. **Unbuilt:** arbitrary schedule discovery and the pretty inline budget block. |
| recursive protocols | `ChoreoRec` | **built as guarded finite approximants** with recursion-free conservativity and a concrete barrier deadlock; temporal liveness/fair delivery remain explicit hypotheses, not syntax-derived claims |
| durable artifacts | `Durable`, `ArtifactDurableCore` | **proved logical codec/journal rung** with canonical roundtrip, generic stack-safe framed encoding, and torn-tail recovery; no filesystem, flush or crash-atomicity guarantee is claimed |
| ✅ bounded finite history delivery | `HistoryRuntime`, `PersistentHistoryRuntime`; Rust `HistoryJournal`/`BufferedHistoryJournal`/`HistoryArrivalJournal` | **BUILT for caller-ID finite events.** Exact retry/collision, bounded pending delivery, finite drain, criss-cross event-set convergence, replay and checked checkpoints are executable. The older Rust buffered wrapper remains volatile; the distinct arrival journal durably retains accepted pending events and canonical state checkpoints across reopen. Opaque payload persistence is not authentication. No cross-language refinement, ID authenticity, infinite enumeration or proof-history reconstruction is claimed. |
| ✅ authored finite history presentation | `FiniteHistoryDelivery` | **PROVED for caller-supplied witnesses.** A complete finite version/event presentation with exact IDs, origin parents, closure, coherence, ancestor selection and policy generation reproduces the authored semantic states. Separately witnessed settled replays of permutations of that exact event list converge only at the runtime event-set view. Delivery is not synthesized, `SameRecord` remains an independent premise for semantic convergence, and no Rust, byte-decoding, filesystem or authentication relation is claimed. |

## 11. What would make us abandon this

Recorded now, while it is cheap to say:

- If the deep-embedded core cannot stay under roughly a dozen constructors
  without losing the analyses in §7.1, the language is the wrong shape and the
  right answer is a tactic library plus a code generator.
- If declaration composition turns out to be expressible by composing verdicts
  after all, §3's justification collapses and we should say so.
- If the graded effect cannot be made sound outside the segmented fragment, the
  budget feature should ship as an *analysis* that reports, not a *type* that
  refuses.

*Revised in place. Every claim here that a reviewer refutes gets its retraction
written where the claim was made, not appended at the end.*
