#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/preo-v3-acceptance"

(cd -- "$repo_root" && lake build \
  Uwueave.Preo.ObservedBoundResult \
  Uwueave.Preo.Quickstart \
  Uwueave.Preo.ArtifactV3Surface >/dev/null)

compile_support() {
  local module="$1"
  (cd -- "$repo_root" && lake env lean \
    -o ".lake/build/lib/lean/$module.olean" \
    -i ".lake/build/lib/lean/$module.ilean" \
    "$fixture_dir/$module.lean")
}

compile_support PreoV3AcceptanceSupport
compile_support PreoV3AcceptanceCommon

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "preo V3 acceptance canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "preo V3 acceptance canary passed: $fixture"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "preo V3 acceptance canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "preo V3 acceptance canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "preo V3 acceptance canary rejected as required: $fixture ($expected)"
}

run_green PositiveObserved
run_green PositiveSurface
run_green RollbackReuse
run_red ForgedObservedState \
  "observationBoundary.Authentic startWorld forged"
run_red OutOfRunningReach "startIndex.world ∈ []"
run_red BareCertifiedReport \
  'the observed input is not an exact `ObservedBoundResult.ObservedCertifiedReport`'
run_red FakeObservedLookalike \
  'the observed input is not an exact `ObservedBoundResult.ObservedCertifiedReport`'
run_red WrongProjection \
  "the checked query is not indexed by the exact supplied base and StateProgram"
run_red WrongFuture \
  "the binding is not for the exact future declaration and state-program result"
run_red WrongWorld "the observed report is for a different world index"
run_red WrongCertificate \
  "the certificate differs from the report's exact future, answer function, or world index"
run_red WrongPlan "the exact checked plan row is absent from the supplied base artifact"
run_red ResourceRefusal 'the automatic V3 route exceeded `maxWork`'
run_red ValidatorResourceRefusal \
  "V3 validation refused the checked encoding (resource bound"
run_red CustomAxiom "Canary.PreoV3Acceptance.CustomAxiom.unsound"
run_red Sorry "sorryAx"
run_red NativeDecide "_native.native_decide.ax_"
