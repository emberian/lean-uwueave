# Release contract

Uwueave is moving toward v0.5 through deliberately narrower release stages.
An application release number is not a wire-format version and does not widen
the proof or deployment claims in `docs/TRUST.md`.

## v0.2.0 — source-only integrity preview

The first release candidate is a signed source tag/archive, not a crates.io
package or a binary distribution. It requires:

- an ordinary cold `lake build` to enforce the whole-tree trust floor;
- every trust, Preoscript, universe, and Wave 27-30 acceptance canary;
- every retained Preoscript golden suite;
- the debt tool's isolated tests and audit-only inventory, followed by stable
  debt IDs and a classified registry before the final v0.2 tag;
- a current lexical UNDONE census before the final v0.2 tag;
- frozen, all-target Rust tests on native Linux and macOS;
- zero unclassified or P0 release debt at the final tag; and
- exact agreement among the `v0.2.0` tag, Cargo/Lake metadata, lockfile,
  changelog, and a future canonical release manifest.

The v0.2 contract makes no C ABI promise. The C shim and Lean exports remain
private implementation details. It also makes no relocatable-binary promise:
the current native build links the Lean shared runtime from the installing
elan toolchain. Cargo publication remains disabled because the present crate
root excludes the Lean sources and Lake metadata required by `build.rs`.

The full authenticated Preoscript V3 export currently measures
6.493408203 MiB of peak-RSS growth per item on hbox, above the retained
4 MiB/item gate. That red result is disclosed, not waived; it blocks v0.3.

## v0.3.0 — finite closure and source packaging

- Land finite-product synthesis/closure and close its registered debt family.
- Keep universe-generalized public carriers under Type-1 acceptance canaries.
- Reduce full V3 export growth to at most 4 MiB/item under the retained
  benchmark protocol.
- Make the Cargo source package self-contained and verify its extracted form
  on Linux and macOS. The preferred design is a repository-root package whose
  explicit include set contains the Lean, Lake, Rust, shim, test, and license
  inputs; copying the Lean tree below `rust/` is not acceptable.
- Generate and test a canonical inventory of all independent wire,
  persistence, and hash-domain versions.

## v0.4.0 — operational distribution

- Close the chosen authenticated-admission, history-delivery, recovery,
  rollback, key/context lifecycle, and deployment-policy compositions.
- Give every supported wire and disk format compatibility fixtures and an
  explicit migration policy.
- If binaries are shipped, bundle or statically link the exact Lean runtime
  under a relocatable Linux `$ORIGIN` / macOS `@loader_path` contract and test
  each archive on a clean machine.
- Attach per-target checksums, source and binary SBOMs, and build provenance.

## v0.5.0 — completion candidate

- No literal `UNDONE` marker remains.
- The debt registry contains no `obligation` or `unclassified` entry. Any
  surviving external boundary is explicitly represented as `PREMISE` or
  `SCOPE`, without relabeling compiler, runtime, cryptographic, or filesystem
  trust as a theorem.
- No P0/P1 release debt remains, and all trust, semantic, runtime, recovery,
  packaging, compatibility, performance, and release gates are green.
- The supported OS/architecture matrix is stated narrowly and tested.
- The annotated signed tag, changelog, source/package archives, checksums,
  SBOMs, and provenance all name the same v0.5.0 source generation.

## Gate placement

Per pull request, CI runs deterministic metadata/policy checks, a cold Linux
Lean build and acceptance suite, and cold frozen Rust suites on Linux and
macOS. Dependency hydration is allowed network access; `cargo test --frozen`
is the build/test phase.

Nightly or hbox-only work includes repeat profiling, scaling comparisons,
sanitizers, long property/corruption campaigns, and advisory-database checks.
Hbox outputs are performance and validation evidence, not release binaries.

Release-only work starts from a clean tagged checkout with no build caches and
adds extracted-package verification, clean-machine archive smoke tests,
checksums, SBOM generation, and OIDC-backed artifact provenance.

## Pre-candidate v0.2 P1 limitations

The following items are visible during development and must be registered and
disclosed rather than silently waived.  The v0.2 source preview forbids
unclassified and P0 release debt; these named P1 limitations may remain only
with their exact boundary and acceptance criterion intact.  Later milestones
must close them before their stricter release contracts can hold.

- The census checked into the current semantic wave differs from a fresh
  census only at four shifted line anchors. `scripts/v02-policy.sh` permits
  exactly the pinned diagnostic hash when CI supplies the matching temporary
  environment value. Any further census drift fails. Remove that value and
  regenerate the census in the dedicated marker-reconciliation change.
- CI pins the reviewed `lean-action` commit, but that action's internal elan
  bootstrap still downloads its installer from an upstream moving branch.
  The Lean compiler itself remains fixed by `lean-toolchain`. Pinning and
  checksumming the elan bootstrap artifact remains a release P1.
- Rust CI is fixed to 1.97.0, but the crate does not yet declare a supported
  MSRV. Set `rust-version` only after the lower bound has been measured.
