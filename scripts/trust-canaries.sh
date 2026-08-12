#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/trust-canaries"

# The fixtures import the reusable command directly, so make the one required
# olean from a clean checkout before compiling them as independent processes.
(cd -- "$repo_root" && lake build Uwueave.TrustFloor >/dev/null)

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && lake env lean "$fixture_dir/$fixture.lean" 2>&1); then
    echo "trust canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "trust canary passed: $fixture"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && lake env lean "$fixture_dir/$fixture.lean" 2>&1); then
    echo "trust canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "trust canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "trust canary rejected as required: $fixture ($expected)"
}

run_green Allowed
run_green IndentedHeader
run_green RootHeader
run_red Vacuous "audit vacuity tripwire"
run_red CustomAxiom "Canary.CustomAxiom.unsound"
run_red Sorry "sorryAx"
run_red NativeDecide "_native.native_decide.ax_"
