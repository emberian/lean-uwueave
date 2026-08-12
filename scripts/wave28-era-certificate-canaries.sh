#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/wave28-acceptance"

(cd -- "$repo_root" && lake build Uwueave.AuthenticatedEraCertificate >/dev/null)

(cd -- "$repo_root" && lake env lean \
  -o ".lake/build/lib/lean/AuthenticatedEraCertificateCommon.olean" \
  -i ".lake/build/lib/lean/AuthenticatedEraCertificateCommon.ilean" \
  "$fixture_dir/AuthenticatedEraCertificateCommon.lean")

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-28 ERA-certificate canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-28 ERA-certificate canary passed: $fixture"
  printf '%s\n' "$output"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-28 ERA-certificate canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "Wave-28 ERA-certificate canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-28 ERA-certificate canary rejected as required: $fixture ($expected)"
}

run_green PositiveAuthenticatedEraCertificate
run_red WrongDomain "kind = 0"
run_red AcceptedButUnissued "Fixtures.unissuedRecord_not_issued"
run_red IncompleteAnnouncement "Fixtures.complete"
run_red IncompleteFrontier 'Tactic `decide` proved that the proposition'
run_red WrongReusableKey "wrongKey_refused"
