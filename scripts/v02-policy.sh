#!/usr/bin/env bash
# Fast v0.2 metadata, governance, and mocked-infrastructure gates.

set -euo pipefail

usage() {
  echo 'usage: scripts/v02-policy.sh [--release-tag EXACT_TAG]' >&2
}

debt_policy_args=(--profile development-v0.2)
if (( $# != 0 )); then
  if (( $# != 2 )) || [[ $1 != --release-tag || -z $2 ]]; then
    usage
    exit 2
  fi
  debt_policy_args=(--release-tag "$2")
fi

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd -- "$repo_root"

echo 'v0.2 policy: validating release metadata'
python3 - <<'PY'
import json
from pathlib import Path
import tomllib

root = Path.cwd()
cargo = tomllib.loads((root / "rust/Cargo.toml").read_text(encoding="utf-8"))
package = cargo["package"]
if package.get("publish") is not False:
    raise SystemExit("rust/Cargo.toml must keep publish = false before self-contained packaging")
if package.get("license") != "Unlicense":
    raise SystemExit("Cargo license must match the repository's sole Unlicense text")
if package.get("rust-version") != "1.89":
    raise SystemExit("Cargo rust-version must remain the empirically verified 1.89 MSRV")
license_text = (root / "LICENSE").read_text(encoding="utf-8")
if "free and unencumbered software released into the public domain" not in license_text:
    raise SystemExit("LICENSE is not the expected Unlicense grant")

lake_manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
lakefile = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
if lake_manifest.get("name") != lakefile.get("name"):
    raise SystemExit("lake-manifest.json and lakefile.toml package names differ")
if lakefile.get("name") != package.get("name"):
    raise SystemExit("Lake and Cargo package names differ")

lock_text = (root / "rust/Cargo.lock").read_text(encoding="utf-8")
needle = f'name = "{package["name"]}"\nversion = "{package["version"]}"'
if needle not in lock_text:
    raise SystemExit("Cargo.lock does not contain the current package name/version")
PY

echo 'v0.2 policy: running isolated debt-registry tests'
python3 tests/debt_gate_test.py

echo 'v0.2 policy: running isolated Ledger-2 integrity tests'
python3 tests/ledger2_gate_test.py

echo 'v0.2 policy: running canonical ABI mutation tests'
python3 tests/abi_gate_test.py

echo 'v0.2 policy: running fully mocked hbox helper tests'
bash tests/hbox-checkpoint.sh

echo 'v0.2 policy: checking the immutable debt registry and committed ancestry'
readonly debt_registry_base=6331af269f80c25c26775299b4678c29b45716cc
scripts/debt-gate.py check --base "$debt_registry_base" "${debt_policy_args[@]}"

echo 'v0.2 policy: checking the machine-readable execution-TCB ledger'
python3 scripts/ledger2-gate.py check

echo 'v0.2 policy: checking the canonical Rust-C-Lean ABI source contract'
python3 scripts/abi-gate.py source

echo 'v0.2 policy: checking the lexical UNDONE census'
LC_ALL=C scripts/undone-census.sh --check

echo 'v0.2 policy gates passed'
