# Debt registry schema v1

This directory contains the active stable-ID debt registry. Its immutable
baseline is commit
`6331af269f80c25c26775299b4678c29b45716cc`, the first commit containing the
fully classified `active.jsonl`. The normal repository gate is:

```sh
scripts/debt-gate.py check \
  --base 6331af269f80c25c26775299b4678c29b45716cc \
  --milestone v0.2
```

That baseline SHA is source-controlled and is the same for pull requests,
branch pushes, and tags; it is never selected from an event-provided base or
parent revision. It must remain an exact ancestor. Do not squash, rebase,
amend, or cherry-pick the baseline under a new identity after a descendant
names it. CI uses a full-history checkout so the gate can inspect every
post-baseline commit.

A green registry check is not a release claim. The `v0.2` milestone forbids
unclassified rows, but it does not forbid P0/P1 obligations, establish the
semantic relevance of runnable closure evidence, discharge external trust
premises, authenticate GitHub refs, or verify release signatures and artifacts.

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

An ordinary check permits unclassified rows during triage. Supplying a release
milestone does not:

```sh
scripts/debt-gate.py check --base BASE_COMMIT --milestone v0.2
```

## Immutable closure receipts

A removed base-active item requires a new canonical one-line receipt at
`docs/debt/closed/U-####.json`. The fixed keys are `schema`, `id`,
`prior_entry_sha256`, `prior_marker_sha256`, `disposition`, `rationale`, and
`evidence`. `superseded` alone adds `replacement_id`.

`prior_entry_sha256` hashes the prior active row's canonical JSON object bytes
without its JSONL newline. `prior_marker_sha256` must equal that row's exact
marker hash. Dispositions are:

- `proved`: evidence is exactly one Lean declaration check.
- `implemented`: evidence is exactly one case in the repository-owned aggregate
  dispatcher.
- `obsolete`: still requires at least one runnable command.
- `superseded`: `evidence` is empty and `replacement_id` names a distinct
  active item of the same class; an obligation replacement may not weaken
  severity.

Each evidence object binds one tracked, non-symlinked regular file by exact
SHA-256 and records the only admitted canonical command. Schema v1 deliberately
admits only two reviewed runners:

```json
{"command":["lake","env","lean","tests/DebtClosures/U_0001.lean"],"declaration":"debtClosure_U_0001","kind":"lean_decl","path":"tests/DebtClosures/U_0001.lean","sha256":"64 lowercase hex digits"}
{"command":["bash","scripts/debt-closures.sh","--debt-case","U-0001"],"kind":"aggregate_case","path":"scripts/debt-closures.sh","sha256":"64 lowercase hex digits"}
```

The gate derives rather than trusts execution arguments, runs from the
repository root in a sanitized environment, and applies a timeout and output
bound. It compiles the exact hashed Lean source as a temporary module, then a
separately parsed trusted inspector loads the resulting `.olean` with
`Lean.importModules`, verifies exact module ownership, and queries
`Lean.collectAxioms` through the environment API. Fixture-defined parser or
command extensions therefore cannot shadow inspection. The declaration may
depend only on Lean's reviewed core axioms (`propext`, `Classical.choice`, and
`Quot.sound`).

Implementation cases go only through the fixed, repository-owned and
SHA-bound `scripts/debt-closures.sh` dispatcher, which may invoke reviewed Rust,
Python, or shell suites internally and must emit exactly
`debt-evidence: U-####: PASS`. Arbitrary per-receipt Python, Rust custom harness,
and shell commands are not schema-v1 evidence. Every ordinary check reruns all
receipt evidence, including immutable historical receipts. This establishes
runner reachability and byte identity; human review must still establish that
the evidence semantically closes the named debt.

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
  duplicate keys, and noncanonical serialization.

The comparison is not merely base-versus-worktree. The gate walks every
committed descendant on an ancestry path from the base to `HEAD`, checks each
parent transition, carries the historical maximum forward, and rejects an ID
or receipt that disappeared, changed, or was reused in an intermediate commit.

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
