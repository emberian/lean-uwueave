# Changelog

All notable user-visible changes will be recorded here. The project uses
[Semantic Versioning](https://semver.org/spec/v2.0.0.html) for application
releases; application versions do not rename or imply compatibility of the
independently versioned wire and persistence formats.

## [Unreleased]

### Added

- A source-only v0.2 release contract and staged v0.3-v0.5 exit criteria.
- Ordered policy and Lean acceptance runners shared by CI and local checks.
- Cold Linux Lean acceptance and cold native Linux/macOS CI coverage.

### Changed

- Cargo publication is disabled until an extracted crate contains the Lean
  sources and Lake metadata required by `build.rs`.
- Cargo metadata now advertises the repository's actual Unlicense grant.
- The Lake manifest package name now agrees with `lakefile.toml`.

### Security

- CI now declares least-privilege read-only permissions and runs trust
  rejection canaries as an explicit required job.

[Unreleased]: https://github.com/emberian/lean-uwueave/commits/dev
