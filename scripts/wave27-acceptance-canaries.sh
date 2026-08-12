#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture_dir="$repo_root/tests/wave27-acceptance"

(cd -- "$repo_root" && lake build \
  Uwueave.AuthenticatedFrontier \
  Uwueave.AuthenticatedWorldContext \
  Uwueave.Preo.RuntimeAuthV4Checked \
  Uwueave.Preo.RuntimeAuthV4Durable \
  Uwueave.Preo.RuntimeAuthV4Projection >/dev/null)

compile_support() {
  local module="$1"
  (cd -- "$repo_root" && lake env lean \
    -o ".lake/build/lib/lean/$module.olean" \
    -i ".lake/build/lib/lean/$module.ilean" \
    "$fixture_dir/$module.lean")
}

compile_support Wave27AcceptanceSupport
compile_support AuthenticatedFrontierCommon
compile_support RuntimeAuthV4Common

run_green() {
  local fixture="$1"
  local output
  if ! output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-27 acceptance canary unexpectedly failed: $fixture" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-27 acceptance canary passed: $fixture"
}

run_red() {
  local fixture="$1"
  local expected="$2"
  local output
  if output=$(cd -- "$repo_root" && lake env lean \
      "$fixture_dir/$fixture.lean" 2>&1); then
    echo "Wave-27 acceptance canary unexpectedly passed: $fixture" >&2
    return 1
  fi
  if [[ "$output" != *"$expected"* ]]; then
    echo "Wave-27 acceptance canary failed for the wrong reason: $fixture" >&2
    echo "expected diagnostic fragment: $expected" >&2
    echo "$output" >&2
    return 1
  fi
  echo "Wave-27 acceptance canary rejected as required: $fixture ($expected)"
}

run_green PositiveAuthenticatedFrontier
run_green PositiveAuthenticatedWorldContext
run_green PositiveRuntimeAuthV4

run_red ForgedSignature "forgedRecord.signature"
run_red WrongProgressOrigin "progress.acceptedEvent.event.actor = 8"
run_red WrongProgressRoster "⊢ False"
run_red OrdinaryEventIsNotProgress "progress.acceptedEvent.event.kind = 1"
run_red StaleFrontier "Frontier.Covers (Frontier.empty"
run_red AdvanceWithoutDelivery "Frontier.noneDelivered (7, 0)"
run_red ForgedPositionPromotion "accepted_forgery_not_promoted"
run_red WrongCausalOrigin "wrong_origin_refuses_position"
run_red StaleWorldVersion "stale_base_refuses_position"
run_red ReusedCapability "consumed_token_not_reusable"

run_red WrongV4Schema "validate config wrongProjection"
run_red EmptyV4Origin "Projection.ofManifest badManifest"
run_red WrongV4Roster "Projection.ofManifest badManifest"
run_red WrongV4Version "changed_format_refused"
run_red EmptyV4Signature "Projection.ofManifest badManifest"
run_red WrongV4Capability "deny request"
run_red V4ResourceRefusal "validate tinyConfig projection"
run_red DecodedManifestNotChecked "has type"

# The unchanged public V3 surface remains an exact compatibility boundary.
# Its existing subprocess suite includes positive generated-name/type/value
# pins, whole-prefix rollback/name reuse, command and validator resource caps,
# and custom-axiom/sorry/native_decide trust-floor contamination.
(cd -- "$repo_root" && ./scripts/preo-v3-acceptance-canaries.sh)

# Pending arrivals are a Rust filesystem boundary, not a Lean theorem.  Run
# the four exact durable-arrival recovery/refusal tests in their native layer.
(cd -- "$repo_root/rust" && cargo test --lib durable_arrival_)
