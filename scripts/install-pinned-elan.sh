#!/usr/bin/env bash
# Install elan from one checksum-pinned upstream release, then install exactly
# the repository's lean-toolchain. This replaces lean-action's moving bootstrap.

set -euo pipefail

if (( $# != 0 )); then
  echo 'usage: scripts/install-pinned-elan.sh' >&2
  exit 2
fi

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)

# Official leanprover/elan v4.2.3 release, published 2026-06-08.
# The annotated tag peels to the immutable source URL:
# https://github.com/leanprover/elan/tree/b6cec7e10fe4965a605aaf60d1cb4a5837f0462b
elan_release=v4.2.3
base_url="https://github.com/leanprover/elan/releases/download/$elan_release"

toolchain=$(<"$repo_root/lean-toolchain")
if [[ $toolchain == *$'\n'* || $toolchain == *$'\r'* ||
      ! $toolchain =~ ^[A-Za-z0-9._/-]+:[A-Za-z0-9._-]+$ ]]; then
  echo "lean-toolchain is not one supported immutable toolchain name: $toolchain" >&2
  exit 1
fi

elan_home=${ELAN_HOME:-$HOME/.elan}
if [[ $elan_home != /* || $elan_home == *$'\n'* || $elan_home == *$'\r'* ]]; then
  echo "ELAN_HOME must be absolute: $elan_home" >&2
  exit 2
fi
if [[ -e $elan_home || -L $elan_home ]]; then
  echo "ELAN_HOME must be a new path so an existing toolchain cannot bypass setup: $elan_home" >&2
  exit 2
fi

kernel=$(uname -s)
machine=$(uname -m)
case "$kernel:$machine" in
  Linux:x86_64)
    asset=elan-x86_64-unknown-linux-gnu.tar.gz
    expected_sha256=df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2
    ;;
  Linux:aarch64|Linux:arm64)
    asset=elan-aarch64-unknown-linux-gnu.tar.gz
    expected_sha256=cb69af0803b04157bc30201c29c12fca882bb3ad8b43476b8d2d3064810bc3ac
    ;;
  Darwin:x86_64)
    asset=elan-x86_64-apple-darwin.tar.gz
    expected_sha256=10d037a69731c0593723e018130c5f54afde175796b4af8ba1317e561e55598c
    ;;
  Darwin:arm64|Darwin:aarch64)
    asset=elan-aarch64-apple-darwin.tar.gz
    expected_sha256=7cae4c03b2f0de4053fb04a91359d5804551e6e37a6ddd1b2e0097dc561ae4a9
    ;;
  *)
    echo "unsupported elan bootstrap target: $kernel $machine" >&2
    exit 2
    ;;
esac

for executable in curl tar uname mktemp; do
  command -v -- "$executable" >/dev/null 2>&1 || {
    echo "required bootstrap executable is unavailable: $executable" >&2
    exit 2
  }
done
if [[ $kernel == Linux ]]; then
  command -v sha256sum >/dev/null 2>&1 || {
    echo 'required bootstrap executable is unavailable: sha256sum' >&2
    exit 2
  }
else
  command -v shasum >/dev/null 2>&1 || {
    echo 'required bootstrap executable is unavailable: shasum' >&2
    exit 2
  }
fi

temp_root=${TMPDIR:-/tmp}
temp_root=${temp_root%/}
[[ -d $temp_root ]] || {
  echo "bootstrap temporary directory does not exist: $temp_root" >&2
  exit 2
}
bootstrap_dir=$(mktemp -d "$temp_root/uwueave-elan.XXXXXX")
archive="$bootstrap_dir/$asset"
installer="$bootstrap_dir/elan-init"
cleanup() {
  rm -f -- "$archive" "$installer"
  rmdir -- "$bootstrap_dir" 2>/dev/null || true
}
trap cleanup EXIT

url="$base_url/$asset"
echo "elan bootstrap: downloading $url"
curl --disable --fail --location --proto '=https' --tlsv1.2 --retry 3 \
  --output "$archive" "$url"

if [[ $kernel == Linux ]]; then
  actual_sha256=$(sha256sum "$archive" | awk '{print $1}')
else
  actual_sha256=$(shasum -a 256 "$archive" | awk '{print $1}')
fi
if [[ $actual_sha256 != "$expected_sha256" ]]; then
  echo "elan bootstrap checksum mismatch for $asset" >&2
  echo "expected $expected_sha256" >&2
  echo "found    $actual_sha256" >&2
  exit 1
fi
echo "elan bootstrap: verified SHA-256 $actual_sha256"

# Reject path traversal, extra payloads, and symlink tricks before extraction.
archive_listing=$(tar -tzf "$archive")
if [[ $archive_listing != elan-init ]]; then
  echo "unexpected elan bootstrap archive contents: $archive_listing" >&2
  exit 1
fi
tar -xzf "$archive" -C "$bootstrap_dir" elan-init
if [[ ! -f $installer || -L $installer || ! -x $installer ]]; then
  echo 'verified elan archive did not produce one executable regular installer' >&2
  exit 1
fi

unset ELAN_TOOLCHAIN ELAN_UPDATE_ROOT ELAN_INIT_SKIP_PATH_CHECK ELAN_INIT_SKIP_SUDO_CHECK
ELAN_HOME=$elan_home "$installer" -y --no-modify-path --default-toolchain none

export ELAN_HOME="$elan_home"
export PATH="$elan_home/bin:$PATH"
if [[ $(elan --version) != 'elan 4.2.3 (b6cec7e10 2026-06-08)' ]]; then
  echo 'installed elan executable does not match the pinned source release' >&2
  exit 1
fi
elan toolchain install "$toolchain"
if ! elan toolchain list | sed 's/ (default)$//' | grep -Fx -- "$toolchain" >/dev/null; then
  echo "elan did not install the repository toolchain: $toolchain" >&2
  exit 1
fi

if [[ -n ${GITHUB_PATH:-} ]]; then
  printf '%s\n' "$elan_home/bin" >>"$GITHUB_PATH"
fi
if [[ -n ${GITHUB_ENV:-} ]]; then
  printf 'ELAN_HOME=%s\n' "$elan_home" >>"$GITHUB_ENV"
fi

cd -- "$repo_root"
echo "elan bootstrap: repository toolchain $toolchain"
lean --version
lake --version
