#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/preo-quickstart"
scratch="$(mktemp -d "${TMPDIR:-/tmp}/preo-quickstart.XXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT

(cd -- "$repo_root" && lake build \
  Uwueave.Preo.Quickstart \
  Uwueave.Preo.ArtifactInspectionMain >/dev/null)

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "preo quickstart canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "preo quickstart canary passed: $fixture"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "preo quickstart canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "preo quickstart canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "preo quickstart canary rejected as required: $fixture ($expected)"
}

run_green Positive
run_red WrongProjection "wrongProject"
run_red WrongFuture "OtherFuture"
run_red WrongCertificate "wrongCertificate"
run_red WrongPlan "checkedPlan"
run_red WrongWorld "otherIndex.world"

runtime_output="$(cd -- "$repo_root" && lake env lean --run \
  "$fixture_dir/Runtime.lean" "$scratch")"
[[ "$runtime_output" == *'"formatVersion":3'* ]]
[[ "$runtime_output" == *'"schemaId":1100'* ]]
[[ "$runtime_output" == *'"id":1101'* ]]
[[ "$runtime_output" == *'"id":1102'* ]]
[[ "$runtime_output" == *'"id":1104'* ]]
[[ "$runtime_output" == *'"recordCount":2'* ]]

frame_json="$($repo_root/tools/uwueave-preo-inspect \
  --frame "$scratch/quickstart-v3.frame")"
journal_json="$($repo_root/tools/uwueave-preo-inspect \
  --journal "$scratch/quickstart-v3.journal")"
[[ "$frame_json" == *'"recordCount":1'* ]]
[[ "$frame_json" == *'"formatVersion":3'* ]]
[[ "$journal_json" == *'"recordCount":2'* ]]
echo "preo quickstart runtime passed: canonical frame, reopen, two-record journal, Lean inspection"
