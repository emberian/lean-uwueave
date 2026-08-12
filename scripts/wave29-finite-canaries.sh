#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/wave29-acceptance"

(cd -- "$repo_root" && lake build \
  Uwueave.FiniteRepairMenu Uwueave.FiniteHistoryDelivery >/dev/null)

(cd -- "$repo_root" && lake env lean \
  -o ".lake/build/lib/lean/FiniteHistoryDeliveryCommon.olean" \
  -i ".lake/build/lib/lean/FiniteHistoryDeliveryCommon.ilean" \
  "$fixture_dir/FiniteHistoryDeliveryCommon.lean")

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-29 finite canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-29 finite canary passed: $fixture"
  printf '%s\n' "$output"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-29 finite canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "Wave-29 finite canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-29 finite canary rejected as required: $fixture ($expected)"
}

run_green PositiveFiniteRepairMenu
run_green PositiveFiniteHistoryDelivery

run_red WrongLeastMenu "foundId? = some"
run_red WrongFullPrice "price? = some"
run_red NonExhaustiveRefusal "impossible_refusal_is_exactly_exhaustive"
run_red MenuBoundRefusal 'Tactic `decide` proved that the proposition'
run_red MenuOrderRefusal 'Tactic `decide` proved that the proposition'
run_red HistoryCollisionRefusal 'Tactic `decide` proved that the proposition'
run_red HistorySelfParentRefusal 'Tactic `decide` proved that the proposition'
run_red HistoryDuplicateParentRefusal 'Tactic `decide` proved that the proposition'
