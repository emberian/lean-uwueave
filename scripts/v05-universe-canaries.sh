#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
fixture="$repo_root/tests/v05-universe/UniverseCanary.lean"
support_dir="$(mktemp -d "${TMPDIR:-/tmp}/uwueave-v05-universe.XXXXXX")"
trap 'rm -r -- "$support_dir"' EXIT

(cd -- "$repo_root" &&
  lake build Uwueave.HistoryPolicy Uwueave.CertificateScope >/dev/null)

(cd -- "$repo_root" &&
  lake env lean \
    -o "$support_dir/UniverseCanary.olean" \
    -i "$support_dir/UniverseCanary.ilean" \
    "$fixture")

echo "V0.5 universe canary passed: homogeneous and mixed Type0/Type1/Type2 probes"
