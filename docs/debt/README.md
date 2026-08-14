# Debt registry schema v1

This directory contains the active stable-ID debt registry. Its immutable
baseline is commit
`6331af269f80c25c26775299b4678c29b45716cc`, the first commit containing the
fully classified `active.jsonl`. The normal repository gate is:

```sh
scripts/debt-gate.py check \
  --base 6331af269f80c25c26775299b4678c29b45716cc \
  --profile development-v0.2
```

That baseline SHA is source-controlled and is the same for pull requests,
branch pushes, and tags; it is never selected from an event-provided base or
parent revision. It must remain an exact ancestor. Do not squash, rebase,
amend, or cherry-pick the baseline under a new identity after a descendant
names it. CI uses a full-history checkout so the gate can inspect every
post-baseline commit.

A green development registry check is not a release claim. The
`development-v0.2` profile forbids unclassified rows but permits active P0s so
ordinary branches and pull requests can carry visible work. `release-v0.2`
also rejects every active P0; `release-v0.5` rejects every active obligation.
These policies do not establish the semantic relevance of runnable closure
evidence, discharge external trust premises, authenticate GitHub refs, or
verify release signatures and artifacts.

## Source grammar

Every primary marker has one immutable four-digit ID:

```text
⟨UNDONE U-0001⟩
⟨PREMISE U-0002⟩
⟨SCOPE U-0003⟩
⟨DEBT-REF U-0001⟩
```

Qualifier prose may follow an ID after whitespace, a comma, or a dash. A
primary ID occurs exactly once; repeats use `DEBT-REF`. Markers must occur in a
Lean line or block comment. Once migration is complete, legacy markers without
an ID are errors.

`marker_sha256` is the lowercase SHA-256 of these domain-separated bytes:

```text
"uwueave.debt-marker.v1\0"
  || source_path_utf8 || "\0"
  || id_ascii || "\0"
  || normalized_marker_block_utf8
```

The marker block uses the existing census boundary: it starts at the
marker-bearing line and stops before the next blank line, asterisk (`*`) list
item, Markdown heading, or standalone Lean comment terminator. A non-standalone line
containing `-/` is retained and ends the block. Lines are LF-normalized and
only trailing horizontal whitespace is stripped, and the normalized block ends
in one LF. Path and ID are therefore part of the commitment. After the first
registry baseline, an active row is wholly immutable: moving or editing an item
requires closing or superseding its old ID and allocating a new monotone ID.

## Active registry

`docs/debt/active.jsonl` is canonical UTF-8/LF JSONL. It has one compact,
lexicographically key-sorted object per line, rows sorted by ID, no blank lines,
and exactly these keys:

```json
{"acceptance":"Named close condition.","class":"obligation","id":"U-0001","marker_sha256":"64 lowercase hex digits","schema":1,"severity":"P1","source":"Uwueave/Module.lean","summary":"Short summary."}
```

- `class` is `obligation`, `premise`, `scope`, or `unclassified`.
- `severity` is `P0` through `P3` or `null`; obligations require a severity,
  while unclassified rows require `null`.
- Obligations require nonempty `acceptance`; unclassified rows require it to
  be empty.
- `source` is a canonical repository-relative `Uwueave/**/*.lean` path.
- `UNDONE` admits `obligation` or `unclassified`; the other marker labels map
  exactly to their corresponding classes.

An ordinary profile-free check permits unclassified rows during local triage.
CI development and release profiles do not:

```sh
scripts/debt-gate.py check --base BASE_COMMIT --profile development-v0.2
scripts/debt-gate.py check --base BASE_COMMIT --release-tag v0.2.0
```

Release tags map through an exact, source-controlled table. `v0.2.0` selects
`release-v0.2`, and `v0.5.0` selects `release-v0.5`; unknown, malformed, patch,
and prerelease tags fail closed until explicitly registered. The deprecated
`--milestone v0.2` spelling temporarily aliases only `development-v0.2` for
in-flight receipt tooling and can never select a release policy.

## Immutable closure receipts

A removed base-active item requires a new canonical one-line receipt at
`docs/debt/closed/U-####.json`. The fixed keys are `schema`, `id`,
`prior_entry_sha256`, `prior_marker_sha256`, `disposition`, `rationale`, and
`evidence`. `superseded` alone adds `replacement_id`.

`prior_entry_sha256` hashes the prior active row's canonical JSON object bytes
without its JSONL newline. `prior_marker_sha256` must equal that row's exact
marker hash. Dispositions are:

- `proved`: evidence is exactly one Lean declaration check.
- `implemented`: evidence is exactly one per-ID case manifest.
- `obsolete`: evidence is exactly one Lean declaration or per-ID case manifest.
- `superseded`: `evidence` is empty and `replacement_id` names a distinct
  active item of the same class; an obligation replacement may not weaken
  severity.

Each evidence object binds one tracked, non-symlinked regular file by exact
SHA-256. It has only `kind`, `path`, and `sha256`; commands, declaration names,
selectors, and expected output are not receipt-controlled. Schema v1 admits
only these two evidence forms:

```json
{"kind":"lean_decl","path":"tests/DebtClosures/U_0001.lean","sha256":"64 lowercase hex digits"}
{"kind":"case_manifest","path":"tests/DebtClosures/U_0001.case.json","sha256":"64 lowercase hex digits"}
```

The gate derives rather than trusts execution arguments, runs from the
repository root in a sanitized environment, and applies a timeout and output
bound. Evidence and child artifacts must exactly match their stage-0 Git-index
blobs before execution.

For `lean_decl`, the ID fixes both the path above and declaration name
`debtClosure_U_0001`. The gate compiles the exact hashed Lean source as a
temporary module, then a
separately parsed trusted inspector loads the resulting `.olean` with
`Lean.importModules`, verifies exact module ownership, and queries
`Lean.collectAxioms` through the environment API. Fixture-defined parser or
command extensions therefore cannot shadow inspection. The declaration may
depend only on Lean's reviewed core axioms (`propext`, `Classical.choice`, and
`Quot.sound`).

The `case_manifest` is itself canonical one-line UTF-8/LF JSON. Its exact
schema-v1 form is:

```json
{"checks":[{"kind":"rust_test","sha256":"64 lowercase hex digits"}],"id":"U-0001","schema":1}
```

The manifest ID must equal the receipt ID. `checks` is nonempty, sorted by
kind, contains no duplicate kind, and schema v1 admits exactly one
`rust_test`. The ID and kind derive the only child path,
`rust/tests/debt_u_0001.rs`, Cargo target `debt_u_0001`, and libtest name
`debt_closure_u_0001`; none is supplied by the receipt or manifest. The child
is a separately tracked regular non-symlinked file and its exact bytes must
match the manifest SHA-256 and Git index.

Rust evidence fails closed unless `cargo` and `rustc` are the exact official
1.89.0 release and commit hashes recorded by the release policy. The sanitized
runner retains resolved `cargo`, `rustc`, and job-private `lake` directories,
plus narrowly validated `RUSTUP_HOME`, `RUSTUP_TOOLCHAIN`, `CARGO_HOME`, and
`ELAN_HOME` selectors, so
the crate's Lean build dependency remains reachable without inheriting the
ambient `PATH`. Policy CI installs Rust 1.89.0 and hydrates locked dependencies
before running the frozen debt gate.

Before execution, Cargo metadata must map the derived target to the exact
SHA-bound child source. A matching explicit `[[test]]` may not redirect the
path or disable the standard harness. The gate then asks libtest to list the
target and requires exactly one derived `: test` entry. It runs that exact
test with ignored tests included and one test thread, requires exit status
zero, and requires one exact `... ok` line plus the standard one-passed,
zero-failed harness summary. A zero-match Cargo success and an early
`process::exit(0)` without a completed harness transcript are therefore red.

Python and shell cases are deliberately not schema-v1 evidence. An in-process
Python test can call `os._exit(0)` before a trusted unittest wrapper checks its
result, while a shell case is an unconstrained program. Adding either runner
requires a separately reviewed supervisor with equally strong completion
semantics.

Every ordinary check reruns all current receipt evidence. The history walk also
requires each manifest and child blob to exist in its receipt-introduction
commit and to retain identical regular-file mode and bytes in every descendant,
so adding a different ID's case never invalidates earlier receipts and temporary
mutation followed by restoration cannot evade the gate.

These checks establish exact runner selection, reachability, byte identity,
and ordinary harness completion. They do not make child output cryptographically
unforgeable: a malicious, reviewed SHA-bound Rust test could print a plausible
libtest transcript before `process::exit(0)`. Exact artifact review remains in
the trusted computing base, and human review must establish that the evidence
semantically closes the named debt.

Receipts present at the comparison base must remain byte-identical forever.
There is no waived or reclassified disposition.

## Base-aware invariants

The post-migration gate reads its comparison state from Git tree/blob objects
with `git ls-tree` and `git cat-file`. It rejects:

- deletion of a marker, row, or old receipt without the required immutable
  evidence;
- forged prior hashes or modified old receipts;
- any change to a surviving active row (including source, marker hash, class,
  severity, summary, or acceptance); an edited obligation needs a new ID;
- reused IDs or new IDs at or below the historical maximum;
- duplicate, unregistered, malformed, non-comment, or legacy markers;
- unknown references, missing evidence, path traversal, unknown JSON keys,
  duplicate keys, noncanonical serialization, evidence/index drift, Cargo
  target redirection, wrong Rust toolchains, and zero-test successes.

The comparison is not merely base-versus-worktree. The gate walks every
committed descendant on an ancestry path from the base to `HEAD`, checks each
parent transition, carries the historical maximum forward, and rejects an ID
or receipt that disappeared, changed, or was reused in an intermediate commit.
It applies the same existence, SHA, canonical-manifest, and byte-identity checks
to every committed evidence blob and manifest child.

## Guarded initial bootstrap (completed)

Bootstrap never edits Lean, assigns IDs, or overwrites a registry. The initial
migration first landed reviewed marker IDs. At that checked-out, non-shallow
`HEAD`, with the worktree source tree unchanged from the commit, the registry
was created with:

```sh
scripts/debt-gate.py bootstrap \
  --base MARKER_MIGRATION_COMMIT \
  --write docs/debt/active.jsonl \
  --allow-bootstrap
```

The resolved bootstrap base had to equal `HEAD` and be an ancestor of it. The command
rejects shallow history, any registry or receipt in the base/worktree or any
reachable prior commit, a zero-marker census, any legacy/malformed marker or
mixed raw `UNDONE` word, any
symlink, and any difference in either the complete Lean source snapshot or the
canonical `(id, label, source, marker_sha256)` set. It writes by temporary
file, flush, `fsync`, and atomic rename; any failure leaves no registry.

Bootstrap and triage formed one uncommitted local transaction. Initial `UNDONE`
rows were deliberately `unclassified`; every row, including severity and
acceptance for obligations, was reviewed before `active.jsonl` was committed.
The first committed registry is the immutable baseline named above—there is no
post-baseline mutation loophole, and bootstrap cannot be rerun over it.
