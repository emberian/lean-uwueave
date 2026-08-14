#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/trust-canaries"
support_dir="$(mktemp -d "${TMPDIR:-/tmp}/uwueave-trust-canaries.XXXXXX")"
trap 'rm -r -- "$support_dir"' EXIT

# The fixtures import the reusable command directly, so make the one required
# olean plus the two exact executable exceptions from a clean checkout before
# compiling them as independent processes.
(cd -- "$repo_root" &&
  lake build \
    Uwueave.TrustFloor \
    Uwueave.Preo.ArtifactEmitMain \
    Uwueave.Preo.ArtifactInspectionMain >/dev/null)

# Materialize the adversarial module only in a private temporary search path;
# no deliberately-unsound olean may survive the canary run in the repository.
(cd -- "$repo_root" &&
  env LEAN_PATH="$support_dir" lake env lean \
    -R "$fixture_dir" \
    -o "$support_dir/ModuleCustomAxiomSource.olean" \
    -i "$support_dir/ModuleCustomAxiomSource.ilean" \
    "$fixture_dir/ModuleCustomAxiomSource.lean")

mkdir -p -- "$support_dir/source-tree/Uwueave"
ln -s -- "$fixture_dir/Allowed.lean" \
  "$support_dir/source-tree/Uwueave/SymlinkEscape.lean"

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" &&
      env LEAN_PATH="$support_dir" lake env lean "$fixture_dir/$fixture.lean" 2>&1); then
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
  if output=$(cd -- "$repo_root" &&
      env LEAN_PATH="$support_dir" lake env lean "$fixture_dir/$fixture.lean" 2>&1); then
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
run_green ModuleCoverageAllowed
run_green ArtifactEmitMainFloor
run_green ArtifactInspectionMainFloor
run_red Vacuous "audit vacuity tripwire"
run_red CustomAxiom "Canary.CustomAxiom.unsound"
run_red Sorry "sorryAx"
run_red NativeDecide "_native.native_decide.ax_"
run_red ModuleCoverageMissing "disk coverage hole"
run_red ModuleCoverageWrongException "disk-coverage exception(s) do not exist"
run_red ModuleCustomAxiom "unsoundOutsideModuleNamespace"
run_red CurrentRootAxiom "unsoundCurrentRoot"
run_red CurrentForeignNamespaceAxiom "unsoundCurrentForeignNamespace"
run_red CurrentAuditNotAtEof "must be the final command"

export UWUEAVE_TRUST_CANARY_ROOT="$support_dir/source-tree/Uwueave"
run_red DiskSymlink "trust coverage refuses symlinked source paths"
unset UWUEAVE_TRUST_CANARY_ROOT
