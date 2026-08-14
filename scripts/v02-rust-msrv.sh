#!/usr/bin/env bash
# Cheap executable check that CI is testing the exact Cargo-declared MSRV.

set -euo pipefail

if (( $# != 0 )); then
  echo 'usage: scripts/v02-rust-msrv.sh' >&2
  exit 2
fi

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd -- "$repo_root"

expected_release=1.89.0
expected_rustc_commit=29483883eed69d5fb4db01964cdf2af4d86e9cb2
expected_cargo_commit=c24e1064277fe51ab72011e2612e556ac56addf7
rustc_verbose=$(rustc --version --verbose)
cargo_verbose=$(cargo --version --verbose)
actual_rustc_release=$(awk '$1 == "release:" { print $2 }' <<<"$rustc_verbose")
actual_rustc_commit=$(awk '$1 == "commit-hash:" { print $2 }' <<<"$rustc_verbose")
actual_cargo_release=$(awk '$1 == "release:" { print $2 }' <<<"$cargo_verbose")
actual_cargo_commit=$(awk '$1 == "commit-hash:" { print $2 }' <<<"$cargo_verbose")
if [[ $actual_rustc_release != "$expected_release" ||
      $actual_rustc_commit != "$expected_rustc_commit" ]]; then
  echo "CI must run official rustc $expected_release ($expected_rustc_commit)" >&2
  echo "found rustc $actual_rustc_release ($actual_rustc_commit)" >&2
  exit 1
fi
if [[ $actual_cargo_release != "$expected_release" ||
      $actual_cargo_commit != "$expected_cargo_commit" ]]; then
  echo "CI must run official cargo $expected_release ($expected_cargo_commit)" >&2
  echo "found cargo $actual_cargo_release ($actual_cargo_commit)" >&2
  exit 1
fi

metadata=$(cargo metadata --manifest-path rust/Cargo.toml --locked --no-deps --format-version 1)
CARGO_METADATA=$metadata python3 - <<'PY'
import json
import os

metadata = json.loads(os.environ["CARGO_METADATA"])
packages = [package for package in metadata["packages"] if package["name"] == "uwueave"]
if len(packages) != 1:
    raise SystemExit(f"expected one uwueave package in Cargo metadata, found {len(packages)}")
if packages[0].get("rust_version") != "1.89":
    raise SystemExit(
        "Cargo metadata must declare the empirically verified rust-version 1.89"
    )
PY

echo 'Rust MSRV gate passed: Cargo rust-version 1.89 under rustc 1.89.0'
