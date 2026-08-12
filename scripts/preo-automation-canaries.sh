#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/preo-automation"

# Compile the public dependencies, then the support module outside the public
# Uwueave tree. Every fixture itself runs in a fresh Lean process so an expected
# failure cannot poison the main build.
(cd -- "$repo_root" && lake build \
  Uwueave.Preo.Elab \
  Uwueave.Tactics.Verdict >/dev/null)
support_olean="$repo_root/.lake/build/lib/lean/PreoAutomationSupport.olean"
support_ilean="$repo_root/.lake/build/lib/lean/PreoAutomationSupport.ilean"
(cd -- "$repo_root" && lake env lean \
  -o "$support_olean" -i "$support_ilean" \
  "$fixture_dir/PreoAutomationSupport.lean")

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && lake env lean "$fixture_dir/$fixture.lean" 2>&1); then
    echo "preo automation canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "preo automation canary passed: $fixture"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && lake env lean "$fixture_dir/$fixture.lean" 2>&1); then
    echo "preo automation canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "preo automation canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "preo automation canary rejected as required: $fixture ($expected)"
}

run_green Positive
run_green TacticsPositive
run_green NoVerdict
run_green RollbackReuse

run_red CustomAxiom "Canary.PreoAutomation.CustomAxiom.unsound"
run_red Sorry "sorryAx"
run_red NativeDecide "_native.native_decide.ax_"
run_red NoPool "classify: no probe pool"
run_red NoVerdictTactic "verdict: NO VERDICT"
run_red PoolCap "probe pool has 65 states, over the cap of 64"
run_red AutomaticCapClassify 'classify: route `exhaustive decision over FinEnum` refused work'
run_red AutomaticCapVerdict 'verdict: route `exhaustive decision over FinEnum` refused work'
run_red WrongGoal 'classify: expected `IConfluent I` or `¬ IConfluent I`'
run_red InternalError 'acceptance: internal error in route `canary route`'
