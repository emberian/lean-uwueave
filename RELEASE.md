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

CI installs elan directly from the official v4.2.3 release assets. The
platform-specific URL is fixed by that release tag and every Linux/macOS,
x86-64/arm64 archive is checked against its recorded upstream SHA-256 before
extraction. The script then installs exactly the name in `lean-toolchain`;
neither a moving installer branch nor an action-owned toolchain selection is
in the trust path. CI gives it a new job-private `ELAN_HOME`, and the installer
refuses an existing path so cached or preinstalled toolchains cannot bypass the
setup.

The crate declares Rust 1.89 as its MSRV. On an isolated hbox checkout, the
locked all-target build—including `build.rs`'s full Lean build and runtime
closure—fails under Rust 1.88.0 at the then-unstable standard-library file-lock
API and succeeds under Rust 1.89.0. Native CI runs that exact compiler on both
supported development hosts and checks it against Cargo metadata before the
frozen suite.

The v0.2 contract makes no C ABI promise. The C shim and Lean exports remain
private implementation details. It also makes no relocatable-binary promise:
the current native build links the Lean shared runtime from the installing
elan toolchain. Cargo publication remains disabled because the present crate
root excludes the Lean sources and Lake metadata required by `build.rs`.

The full authenticated Preoscript V3 export currently measures
5.779296875 MiB of peak-RSS growth per item on hbox after the first safe
generator factoring pass (down 10.9975% from 6.493408203 MiB/item), still above
the retained 4 MiB/item gate. That red result is disclosed, not waived; it
blocks v0.3.

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

## Toolchain pin renewal

Renew the elan bootstrap only from an official `leanprover/elan` release.
Record the annotated tag's peeled source commit in
`scripts/install-pinned-elan.sh`, replace every supported asset digest with the
SHA-256 reported by the official GitHub release API and independently download
and hash each artifact. Review the archive listing before changing the single
`elan-init` payload expectation. The change is accepted only after the install
script completes on the CI matrix's exact Ubuntu and macOS images and the cold
Lean acceptance job remains green. Changes to the compiler are separate:
`lean-toolchain` stays the sole authoritative Lean selection.

Raise `rust-version` only from a fresh isolated checkout. The immediately
preceding stable Rust release must fail for a compiler-version reason present
in the crate or its locked target dependency closure, and the candidate must
complete the real all-target Cargo build with the Lean-dependent build script.
Update the exact CI toolchain and `scripts/v02-rust-msrv.sh` in the same change.

## Development and release debt policy

Branches and pull requests use `development-v0.2`: unclassified debt is red,
while active P0s remain visible without blocking ordinary integration. An exact
`v0.2.0` tag selects `release-v0.2` and fails on any active P0. An exact
`v0.5.0` tag selects `release-v0.5` and fails while any obligation remains.
Every other tag fails closed until its policy is explicitly registered. The
policy reads canonical registry class and severity fields; it
does not infer release state from marker, summary, acceptance, or document
prose.

Debt-policy success is only one release condition. It does not authenticate a
tag, establish that runnable evidence is semantically relevant, discharge
external premises, or verify manifests, signatures, provenance, or artifacts.
