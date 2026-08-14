#!/usr/bin/env bash
# Fast v0.2 metadata, governance, and mocked-infrastructure gates.

set -euo pipefail

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

echo 'v0.2 policy: running fully mocked hbox helper tests'
bash tests/hbox-checkpoint.sh

echo 'v0.2 policy: auditing the exact pre-migration debt inventory'
debt_audit=$(scripts/debt-gate.py audit)
printf '%s\n' "$debt_audit"
DEBT_AUDIT_JSON=$debt_audit python3 - <<'PY'
import json
import os

actual = json.loads(os.environ["DEBT_AUDIT_JSON"])
expected = {
    "active_registry": False,
    "canonical_primary": 0,
    "closed_receipts": 0,
    "debt_refs": 0,
    "debt_stems": 155,
    "legacy_or_malformed": 155,
    "mode": "audit-only",
    "normal_check_enabled": False,
    "raw_undone_words": 159,
    "schema": 1,
    "undone_family_occurrences": 155,
}
for key, value in expected.items():
    if actual.get(key) != value:
        raise SystemExit(
            f"pre-migration debt inventory changed at {key}: "
            f"expected {value!r}, found {actual.get(key)!r}"
        )
PY

echo 'v0.2 policy: checking the lexical UNDONE census'
set +e
census_output=$(LC_ALL=C scripts/undone-census.sh --check 2>&1)
census_status=$?
set -e
if (( census_status == 0 )); then
  printf '%s\n' "$census_output"
elif [[ -n ${UWUEAVE_V02_ALLOW_STALE_CENSUS_SHA256:-} ]]; then
  actual_sha=$(printf '%s\n' "$census_output" |
    python3 -c 'import hashlib, sys; print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())')
  if [[ $actual_sha != "$UWUEAVE_V02_ALLOW_STALE_CENSUS_SHA256" ]]; then
    printf '%s\n' "$census_output" >&2
    echo "v0.2 policy: census drift is not the pinned temporary exception" >&2
    echo "v0.2 policy: expected $UWUEAVE_V02_ALLOW_STALE_CENSUS_SHA256, found $actual_sha" >&2
    exit 1
  fi
  printf '%s\n' "$census_output" >&2
  echo 'v0.2 policy: WARNING: accepted the exact pinned line-anchor-only census drift' >&2
else
  printf '%s\n' "$census_output" >&2
  echo 'v0.2 policy: census is stale and no exact temporary exception was supplied' >&2
  exit 1
fi

echo 'v0.2 policy gates passed'
