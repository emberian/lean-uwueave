#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/wave30-auth-runtime"
support_dir="$(mktemp -d /tmp/uwueave-wave30-auth.XXXXXX)"
trap 'rm -r -- "$support_dir"' EXIT

(cd -- "$repo_root" && lake build \
  Uwueave.RuntimeAuthV4Kernel Uwueave.TrustFloor >/dev/null)

(cd -- "$repo_root" && env LEAN_PATH="$support_dir" lake env lean \
  -o "$support_dir/Wave30AuthRuntimeCommon.olean" \
  -i "$support_dir/Wave30AuthRuntimeCommon.ilean" \
  "$fixture_dir/Wave30AuthRuntimeCommon.lean")

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && env LEAN_PATH="$support_dir" lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-30 auth-runtime canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-30 auth-runtime canary passed: $fixture"
  printf '%s\n' "$output"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && env LEAN_PATH="$support_dir" lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-30 auth-runtime canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "Wave-30 auth-runtime canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-30 auth-runtime canary rejected as required: $fixture ($expected)"
}

run_green PositiveExactProjection
run_green ExactRefusalMatrix

decision_reds=(
  DecodeTooLarge DecodeBadMagic DecodeUnsupportedVersion DecodeWrongKind
  DecodeMalformed ShapeEmptyDocument ShapeEmptyGenesis ShapeEmptyContext
  ShapeEmptyNonce ShapeEmptyOperationId ShapeEmptyChildId
  ShapeEmptyDestinationId ShapeEmptySignature WidthChild WidthDestination
  WidthCite WrongDocumentProjection WrongGenesisProjection
  WrongContextProjection WrongAlgorithmProjection WrongIssuerProjection
  WrongEpochProjection WrongNonceProjection WrongOperationIdProjection
  WrongLamportProjection WrongChildStableProjection WrongChildIndexProjection
  WrongDestinationStableProjection WrongDestinationIndexProjection
  WrongDestinationPresenceProjection WrongCiteProjection WrongSignatureProjection
)
for fixture in "${decision_reds[@]}"; do
  run_red "$fixture" 'Tactic `decide` proved that the proposition'
done

run_red CustomAxiom "Canary.Wave30.CustomAxiom.unsound"
run_red Sorry "sorryAx"
run_red NativeDecide "_native.native_decide.ax_"
