#!/usr/bin/env bash
# Cold v0.2 proof build followed by ordered positive and negative acceptance gates.

set -euo pipefail

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd -- "$repo_root"

if [[ ${UWUEAVE_V02_COLD_BUILD:-0} != 1 ]]; then
  echo 'v0.2 Lean acceptance refuses to clean build artifacts without UWUEAVE_V02_COLD_BUILD=1' >&2
  exit 2
fi

echo 'v0.2 Lean acceptance: cleaning Lake build outputs'
lake clean

echo 'v0.2 Lean acceptance: building the authoritative root and trust floor'
lake build

echo 'v0.2 Lean acceptance: trust rejection canaries'
scripts/trust-canaries.sh

echo 'v0.2 Lean acceptance: universe-polymorphism canaries'
scripts/v05-universe-canaries.sh

echo 'v0.2 Lean acceptance: Preoscript authoring and runtime canaries'
scripts/preo-automation-canaries.sh
scripts/preo-quickstart-canaries.sh
scripts/preo-v3-acceptance-canaries.sh

echo 'v0.2 Lean acceptance: authenticated and finite-wave canaries'
scripts/wave27-acceptance-canaries.sh
scripts/wave28-era-certificate-canaries.sh
scripts/wave29-finite-canaries.sh
scripts/wave30-auth-runtime-canaries.sh

echo 'v0.2 Lean acceptance: exact Preoscript goldens'
scripts/preo-bench.sh golden
scripts/preo-bench.sh wave26-golden
scripts/preo-bench.sh wave27-golden
scripts/preo-bench.sh wave29-golden

echo 'v0.2 Lean acceptance gates passed'
