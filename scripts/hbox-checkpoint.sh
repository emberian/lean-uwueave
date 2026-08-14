#!/usr/bin/env bash
# Stage and run a reproducible, disposable checkpoint on the hbox build host.
# shellcheck disable=SC2016 # Single-quoted payloads expand only in remote Bash.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  scripts/hbox-checkpoint.sh [--cleanup] lake-build
  scripts/hbox-checkpoint.sh [--cleanup] cargo-no-run
  scripts/hbox-checkpoint.sh self-check

With no arguments, print this help and do nothing. The only remote execution
schemas are:

  lake-build    Run exactly `lake build` from the checkpoint root.
  cargo-no-run  Run exactly `cargo test --all-targets --no-run` from rust/,
                with CARGO_HOME and CARGO_TARGET_DIR under the checkpoint.

There is deliberately no generic remote-command mode. Add a reviewed, fixed
schema here instead of passing shell text or path-like tool options through SSH.

The helper copies the checkout into a unique local /tmp directory, excluding
.git, .lake, and every target directory. Included symlinks and special entries
are refused. It aborts if either of two checksum dry-runs finds that the checkout
changed while the snapshot and Git metadata were captured. Untracked paths that
look like environment files, private keys, credential stores, or tokens are
shown and refused before any snapshot or network operation. The frozen snapshot
is scanned again by path name; even tracked entries matching those conservative
sensitive-name patterns are refused.

The remote checkpoint is always a new
/tank/dregg-build/uwueave-hbox-checkpoint.* directory. A random token in a
non-symlink marker binds every later remote operation and opt-in cleanup to that
exact directory. Remote source is checked for symlinks/special entries and made
read-only. Uploads are local-to-remote only.

Command stdout, stderr, GNU-time output, environment facts, and exit status are
downloaded only to a fresh /tmp/uwueave-hbox-artifacts.* directory. The remote
artifact tree must contain only ordinary directories and regular files: any
symlink, FIFO, socket, or device aborts before download. Nothing is downloaded
into the checkout.

By default local and remote checkpoints are retained and their exact paths are
printed. --cleanup removes only marker-verified, non-symlink checkpoint paths
allocated by this invocation, after logs download. Downloaded /tmp artifacts
remain.

Important hbox differences:
  * Do not stage in hbox's nearly-full home filesystem. This helper always uses
    /tank/dregg-build and puts command temporary files in /tmp.
  * The repository lean-toolchain is selected through $HOME/.elan/bin. The host
    default outside the repository may be an older Lean release.
  * hbox has GNU time. Repository scripts that require macOS
    `/usr/bin/time -lp` are not portable there; this helper records
    `/usr/bin/time -v` instead. GNU maximum RSS is reported in KiB.

Environment variables used by focused tests:
  UWUEAVE_HBOX_HOST       SSH host (default: hbox)
  UWUEAVE_HBOX_SSH        ssh executable (default: ssh)
  UWUEAVE_HBOX_RSYNC      rsync executable (default: rsync)
  UWUEAVE_HBOX_FIND       find executable (default: find)
  UWUEAVE_HBOX_GIT        git executable (default: git)
  UWUEAVE_HBOX_REPO_ROOT  checkout root (default: parent of this script)
EOF
}

die() {
  echo "hbox-checkpoint: $*" >&2
  exit 2
}

note() {
  echo "hbox-checkpoint: $*" >&2
}

is_safe_local_stage() {
  [[ ${1:-} =~ ^/tmp/uwueave-hbox-checkpoint\.[A-Za-z0-9]+$ ]]
}

is_safe_remote_stage() {
  [[ ${1:-} =~ ^/tank/dregg-build/uwueave-hbox-checkpoint\.[A-Za-z0-9]+$ ]]
}

is_safe_artifact_dir() {
  [[ ${1:-} =~ ^/tmp/uwueave-hbox-artifacts\.[A-Za-z0-9]+$ ]]
}

require_executable() {
  local executable=$1
  if [[ $executable == */* ]]; then
    [[ -x $executable && ! -L $executable ]] ||
      die "executable is unavailable or a symlink: $executable"
  else
    command -v -- "$executable" >/dev/null 2>&1 ||
      die "executable is unavailable: $executable"
  fi
}

validate_host() {
  local candidate=$1
  (( ${#candidate} > 0 && ${#candidate} <= 253 )) ||
    die "unsafe SSH host: $candidate"
  [[ $candidate != -* && $candidate != .* && $candidate != *. &&
     $candidate != */* &&
     $candidate != *..* && $candidate =~ ^[A-Za-z0-9.-]+$ ]] ||
    die "unsafe SSH host: $candidate"

  local label
  local -a labels=()
  IFS='.' read -r -a labels <<<"$candidate"
  for label in "${labels[@]}"; do
    (( ${#label} > 0 && ${#label} <= 63 )) ||
      die "unsafe SSH host: $candidate"
    [[ $label =~ ^[A-Za-z0-9]([A-Za-z0-9-]*[A-Za-z0-9])?$ ]] ||
      die "unsafe SSH host: $candidate"
  done
}

exclude_args=(
  --exclude='.git/'
  --exclude='.lake/'
  --exclude='target/'
)

find_included() {
  local source_root=$1
  shift
  "$find_bin" "$source_root" \
    \( -type d \( -name .git -o -name .lake -o -name target \) \) \
    -prune -o \
    "$@" -print0
}

check_local_source_types() {
  local source_root=$1
  local entry relative found=0 listing
  listing=$(mktemp /tmp/uwueave-hbox-source-types.XXXXXX)
  [[ $listing =~ ^/tmp/uwueave-hbox-source-types\.[A-Za-z0-9]+$ ]] ||
    die "mktemp returned an unexpected source-type-list path: $listing"
  if ! find_included "$source_root" -type l >"$listing"; then
    rm -f -- "$listing"
    die 'failed to scan included symlinks'
  fi
  while IFS= read -r -d '' entry; do
    relative=${entry#"$source_root"/}
    note "included symlink is not allowed: $relative"
    found=1
  done <"$listing"
  if (( found != 0 )); then
    rm -f -- "$listing"
    die 'checkpoint source contains included symlinks'
  fi

  found=0
  if ! find_included "$source_root" ! -type d ! -type f ! -type l \
      >"$listing"; then
    rm -f -- "$listing"
    die 'failed to scan included special entries'
  fi
  while IFS= read -r -d '' entry; do
    relative=${entry#"$source_root"/}
    note "included special entry is not allowed: $relative"
    found=1
  done <"$listing"
  rm -f -- "$listing"
  (( found == 0 )) || die 'checkpoint source contains included special entries'
}

check_local_artifact_types() {
  local artifact_root=$1
  local entry relative found=0 listing
  listing=$(mktemp /tmp/uwueave-hbox-artifact-types.XXXXXX)
  [[ $listing =~ ^/tmp/uwueave-hbox-artifact-types\.[A-Za-z0-9]+$ ]] ||
    die "mktemp returned an unexpected artifact-type-list path: $listing"
  if ! "$find_bin" "$artifact_root" -mindepth 1 -type l -print0 >"$listing"; then
    rm -f -- "$listing"
    die 'failed to scan downloaded artifact symlinks'
  fi
  while IFS= read -r -d '' entry; do
    relative=${entry#"$artifact_root"/}
    note "downloaded artifact symlink is not allowed: $relative"
    found=1
  done <"$listing"
  if (( found != 0 )); then
    rm -f -- "$listing"
    die 'downloaded artifact tree contains a symlink'
  fi

  found=0
  if ! "$find_bin" "$artifact_root" -mindepth 1 \
      ! -type d ! -type f ! -type l -print0 >"$listing"; then
    rm -f -- "$listing"
    die 'failed to scan downloaded artifact special entries'
  fi
  while IFS= read -r -d '' entry; do
    relative=${entry#"$artifact_root"/}
    note "downloaded artifact special entry is not allowed: $relative"
    found=1
  done <"$listing"
  rm -f -- "$listing"
  (( found == 0 )) || die 'downloaded artifact tree contains a special entry'
}

is_rsync_excluded_path() {
  local path=$1
  case "/$path/" in
    */.git/*|*/.lake/*|*/target/*) return 0 ;;
    *) return 1 ;;
  esac
}

is_sensitive_path() {
  local path=$1
  case "$path" in
    .env|.env.*|*/.env|*/.env.*|\
    *.pem|*.key|*.p12|*.pfx|*.kdbx|*.token|*.credentials|\
    id_rsa|*/id_rsa|id_ed25519|*/id_ed25519|\
    credentials.json|*/credentials.json|service-account*.json|*/service-account*.json|\
    .ssh/*|*/.ssh/*|.aws/*|*/.aws/*|.gnupg/*|*/.gnupg/*|.kube/*|*/.kube/*)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

check_sensitive_untracked() {
  local source_root=$1
  local path found=0
  local listing_root nonignored ignored listing
  local -A seen=()
  listing_root=$(mktemp -d /tmp/uwueave-hbox-untracked.XXXXXX)
  [[ $listing_root =~ ^/tmp/uwueave-hbox-untracked\.[A-Za-z0-9]+$ ]] ||
    die "mktemp returned an unexpected untracked-list path: $listing_root"
  nonignored="$listing_root/nonignored"
  ignored="$listing_root/ignored"
  if ! "$git_bin" -C "$source_root" ls-files --others --exclude-standard -z \
      >"$nonignored"; then
    rm -rf -- "$listing_root"
    die 'failed to enumerate untracked paths'
  fi
  if ! "$git_bin" -C "$source_root" ls-files --others --ignored \
      --exclude-standard -z >"$ignored"; then
    rm -rf -- "$listing_root"
    die 'failed to enumerate ignored untracked paths'
  fi
  for listing in "$nonignored" "$ignored"; do
    while IFS= read -r -d '' path; do
      is_rsync_excluded_path "$path" && continue
      [[ -z ${seen[$path]+set} ]] || continue
      seen[$path]=1
      if is_sensitive_path "$path"; then
        printf 'hbox-checkpoint: sensitive untracked path is not allowed: %q\n' \
          "$path" >&2
        found=1
      fi
    done <"$listing"
  done
  rm -rf -- "$listing_root"
  (( found == 0 )) || die 'refusing checkpoint with sensitive untracked paths'
}

check_sensitive_snapshot_paths() {
  local snapshot_root=$1
  local entry relative found=0 listing
  listing=$(mktemp /tmp/uwueave-hbox-snapshot-paths.XXXXXX)
  [[ $listing =~ ^/tmp/uwueave-hbox-snapshot-paths\.[A-Za-z0-9]+$ ]] ||
    die "mktemp returned an unexpected snapshot-path-list path: $listing"
  if ! find_included "$snapshot_root" >"$listing"; then
    rm -f -- "$listing"
    die 'failed to enumerate frozen snapshot paths'
  fi
  while IFS= read -r -d '' entry; do
    relative=${entry#"$snapshot_root"/}
    if is_sensitive_path "$relative"; then
      printf 'hbox-checkpoint: sensitive path is not allowed in frozen snapshot: %q\n' \
        "$relative" >&2
      found=1
    fi
  done <"$listing"
  rm -f -- "$listing"
  (( found == 0 )) || die 'refusing frozen snapshot with sensitive path names'
}

snapshot_checkout() {
  local source_root=$1
  local destination=$2
  mkdir -p -- "$destination"
  "$rsync_bin" -a "${exclude_args[@]}" "$source_root/" "$destination/"
}

snapshot_diff() {
  local source_root=$1
  local snapshot=$2
  "$rsync_bin" -naci --delete "${exclude_args[@]}" \
    "$source_root/" "$snapshot/"
}

emit_remote_guard() {
  printf 'set -euo pipefail\n'
  printf 'stage=%q\n' "$remote_stage"
  printf 'expected_token=%q\n' "$checkpoint_token"
  cat <<'REMOTE_GUARD'
marker="$stage/.uwueave-hbox-checkpoint-token"
test -d "$stage"
test ! -L "$stage"
test "$(realpath -- "$stage")" = "$stage"
mounts=$(findmnt -Rrn -o TARGET --target "$stage" 2>/dev/null | \
  awk -v stage="$stage" '$0 == stage || index($0, stage "/") == 1')
test -z "$mounts"
test -f "$marker"
test ! -L "$marker"
test "$(cat -- "$marker")" = "$expected_token"
for child in repo artifacts; do
  path="$stage/$child"
  if test -e "$path" || test -L "$path"; then
    test -d "$path"
    test ! -L "$path"
    test "$(realpath -- "$path")" = "$path"
  fi
done
REMOTE_GUARD
}

assert_remote_identity() {
  if ! emit_remote_guard |
      "$ssh_bin" -o BatchMode=yes -o ConnectTimeout=10 "$host" bash -s; then
    die 'remote checkpoint marker or non-symlink identity check failed'
  fi
}

run_guarded_remote() {
  local failure=$1
  local payload=$2
  assert_remote_identity
  if ! {
    emit_remote_guard
    printf '%s\n' "$payload"
  } | "$ssh_bin" -o BatchMode=yes -o ConnectTimeout=10 "$host" bash -s; then
    die "$failure"
  fi
}

remote_snapshot_diff() {
  local snapshot=$1
  local remote_repo=$2
  assert_remote_identity
  "$rsync_bin" -nrci --delete --no-perms --omit-dir-times \
    "${exclude_args[@]}" "$snapshot/" "$host:$remote_repo/"
}

check_remote_source_types() {
  run_guarded_remote 'remote source identity/type check failed' '
bad=$(find "$stage/repo" \
  \( -type d \( -name .lake -o -name target \) \) -prune -o \
  -type l -print -quit)
if test -n "$bad"; then
  printf "hbox-checkpoint remote: included symlink is not allowed: %s\n" "$bad" >&2
  exit 41
fi
bad=$(find "$stage/repo" \
  \( -type d \( -name .lake -o -name target \) \) -prune -o \
  ! -type d ! -type f ! -type l -print -quit)
if test -n "$bad"; then
  printf "hbox-checkpoint remote: included special entry is not allowed: %s\n" "$bad" >&2
  exit 42
fi'
}

self_check() {
  local check_root
  check_root=$(mktemp -d /tmp/uwueave-hbox-self-check.XXXXXX)
  [[ $check_root =~ ^/tmp/uwueave-hbox-self-check\.[A-Za-z0-9]+$ ]] ||
    die "mktemp returned an unexpected self-check path: $check_root"

  local source_root="$check_root/source"
  local snapshot="$check_root/snapshot"
  mkdir -p -- "$source_root/.git" "$source_root/.lake" \
    "$source_root/target" "$source_root/rust/target" "$source_root/src"
  printf 'keep\n' >"$source_root/src/Keep.txt"
  printf 'git\n' >"$source_root/.git/ignored"
  printf 'lake\n' >"$source_root/.lake/ignored"
  printf 'target\n' >"$source_root/target/ignored"
  printf 'rust target\n' >"$source_root/rust/target/ignored"

  snapshot_checkout "$source_root" "$snapshot"
  [[ -f $snapshot/src/Keep.txt ]] || die 'self-check lost included source'
  [[ ! -e $snapshot/.git && ! -e $snapshot/.lake &&
     ! -e $snapshot/target && ! -e $snapshot/rust/target ]] ||
    die 'self-check copied an excluded build directory'
  [[ -z $(snapshot_diff "$source_root" "$snapshot") ]] ||
    die 'self-check reported drift in a stable snapshot'

  printf 'changed\n' >"$source_root/src/Keep.txt"
  [[ -n $(snapshot_diff "$source_root" "$snapshot") ]] ||
    die 'self-check did not detect source drift'

  validate_host hbox.example
  if (validate_host -oProxyCommand=bad) >/dev/null 2>&1; then
    die 'self-check accepted an option-like host'
  fi

  rm -rf -- "$check_root"
  printf 'hbox-checkpoint: self-check passed (local only; no SSH)\n'
}

cleanup_requested=0
local_stage=''
remote_stage=''
artifact_download=''
checkpoint_token=''
host=${UWUEAVE_HBOX_HOST:-hbox}
ssh_bin=${UWUEAVE_HBOX_SSH:-ssh}
rsync_bin=${UWUEAVE_HBOX_RSYNC:-rsync}
find_bin=${UWUEAVE_HBOX_FIND:-find}
git_bin=${UWUEAVE_HBOX_GIT:-git}

local_marker_is_valid() {
  local marker="$local_stage/.uwueave-hbox-checkpoint-token"
  is_safe_local_stage "$local_stage" &&
    [[ -d $local_stage && ! -L $local_stage && -f $marker && ! -L $marker ]] &&
    [[ $(cat -- "$marker") == "$checkpoint_token" ]]
}

# Invoked indirectly by the EXIT trap.
# shellcheck disable=SC2329
cleanup_stages() {
  local cleanup_status=0
  if [[ -n $local_stage ]]; then
    if local_marker_is_valid; then
      rm -rf -- "$local_stage" || cleanup_status=1
    else
      note "refusing cleanup of unverified local checkpoint: $local_stage"
      cleanup_status=1
    fi
  fi
  if [[ -n $remote_stage ]]; then
    if is_safe_remote_stage "$remote_stage"; then
      if ! {
        emit_remote_guard
        printf 'rm -rf -- "$stage"\n'
      } | "$ssh_bin" -o BatchMode=yes -o ConnectTimeout=10 "$host" bash -s; then
        note "refusing or failing cleanup of unverified remote checkpoint: $remote_stage"
        cleanup_status=1
      fi
    else
      note "refusing cleanup of unexpected remote path: $remote_stage"
      cleanup_status=1
    fi
  fi
  return "$cleanup_status"
}

# Installed below as the EXIT trap.
# shellcheck disable=SC2329
cleanup_on_exit() {
  local exit_status=$?
  trap - EXIT
  if (( cleanup_requested )); then
    cleanup_stages || {
      note 'one or more opt-in cleanup operations failed'
      (( exit_status == 0 )) && exit_status=1
    }
  fi
  exit "$exit_status"
}

if (( $# == 0 )); then
  usage
  exit 0
fi

case "${1:-}" in
  -h|--help)
    usage
    exit 0
    ;;
  --cleanup)
    cleanup_requested=1
    shift
    ;;
esac

subcommand=${1:-}
[[ -n $subcommand ]] || die 'missing subcommand after --cleanup'
shift

run_label=''
work_relative='.'
command_argv=()
case "$subcommand" in
  self-check)
    (( cleanup_requested == 0 )) || die '--cleanup is not used with self-check'
    (( $# == 0 )) || die 'self-check accepts no arguments'
    require_executable "$rsync_bin"
    self_check
    exit 0
    ;;
  lake-build)
    (( $# == 0 )) || die 'lake-build accepts no arguments'
    run_label='lake-build'
    command_argv=(lake build)
    ;;
  cargo-no-run)
    (( $# == 0 )) || die 'cargo-no-run accepts no arguments'
    run_label='cargo-no-run'
    work_relative='rust'
    command_argv=(cargo test --all-targets --no-run)
    ;;
  *)
    usage >&2
    die "unknown subcommand: $subcommand"
    ;;
esac

validate_host "$host"
require_executable "$ssh_bin"
require_executable "$rsync_bin"
require_executable "$find_bin"
require_executable "$git_bin"
require_executable od

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
default_repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
repo_root=${UWUEAVE_HBOX_REPO_ROOT:-$default_repo_root}
repo_root=$(CDPATH='' cd -- "$repo_root" && pwd)
[[ -f $repo_root/lean-toolchain && -d $repo_root/rust && -d $repo_root/.git ]] ||
  die "repository root lacks lean-toolchain, rust/, or .git/: $repo_root"

check_local_source_types "$repo_root"
check_sensitive_untracked "$repo_root"

checkpoint_token=$(LC_ALL=C od -An -N16 -tx1 /dev/urandom | tr -d ' \n')
[[ $checkpoint_token =~ ^[0-9a-f]{32}$ ]] ||
  die 'failed to generate a checkpoint token'

trap cleanup_on_exit EXIT

note 'hbox home capacity is intentionally avoided; staging under /tank and TMPDIR=/tmp'
note 'GNU /usr/bin/time -v is used; maximum RSS in its log is KiB'

local_stage=$(mktemp -d /tmp/uwueave-hbox-checkpoint.XXXXXX)
is_safe_local_stage "$local_stage" ||
  die "mktemp returned an unexpected local path: $local_stage"
printf '%s\n' "$checkpoint_token" >"$local_stage/.uwueave-hbox-checkpoint-token"
chmod 600 "$local_stage/.uwueave-hbox-checkpoint-token"
local_marker_is_valid || die 'local checkpoint marker identity check failed'

snapshot_root="$local_stage/repo"
metadata_root="$local_stage/metadata"
mkdir -p -- "$metadata_root"

note "copying checkout to unique local checkpoint: $local_stage"
if ! snapshot_checkout "$repo_root" "$snapshot_root"; then
  die 'local snapshot copy failed'
fi
check_local_source_types "$snapshot_root"
if ! snapshot_diff "$repo_root" "$snapshot_root" \
    >"$metadata_root/snapshot-drift.txt"; then
  die 'local snapshot checksum dry-run failed'
fi
if [[ -s $metadata_root/snapshot-drift.txt ]]; then
  sed -n '1,120p' "$metadata_root/snapshot-drift.txt" >&2
  die 'checkout changed during snapshot; retry after reaching a stable point'
fi

"$git_bin" -C "$repo_root" rev-parse HEAD >"$metadata_root/git-head.txt"
"$git_bin" -C "$repo_root" status --porcelain=v1 -uall \
  >"$metadata_root/git-status.txt"
if ! snapshot_diff "$repo_root" "$snapshot_root" \
    >"$metadata_root/snapshot-final-drift.txt"; then
  die 'final local snapshot checksum dry-run failed'
fi
if [[ -s $metadata_root/snapshot-final-drift.txt ]]; then
  sed -n '1,120p' "$metadata_root/snapshot-final-drift.txt" >&2
  die 'checkout changed while checkpoint metadata was captured; retry at a stable point'
fi
# Re-scan after the frozen snapshot exists. This closes the interval in which an
# ignored sensitive file could appear after preflight yet still be copied into a
# stable snapshot; later checkout changes cannot affect the snapshot bytes.
check_sensitive_untracked "$repo_root"
check_sensitive_snapshot_paths "$snapshot_root"
if [[ -s $metadata_root/git-status.txt ]]; then
  note 'the checkout is dirty; tracked and untracked source bytes are included in the checkpoint'
fi

note 'checking hbox staging and GNU-time prerequisites'
if ! "$ssh_bin" -o BatchMode=yes -o ConnectTimeout=10 "$host" \
    "test -d /tank/dregg-build && test -w /tank/dregg-build && \
     command -v bash >/dev/null && command -v awk >/dev/null && \
     command -v realpath >/dev/null && \
     command -v findmnt >/dev/null && \
     command -v rsync >/dev/null && \
     /usr/bin/time --version 2>&1 | grep -q 'GNU Time'"; then
  die "hbox prerequisite check failed for host: $host"
fi

if ! remote_stage=$("$ssh_bin" -o BatchMode=yes -o ConnectTimeout=10 "$host" \
    'umask 077; mktemp -d /tank/dregg-build/uwueave-hbox-checkpoint.XXXXXX'); then
  die 'failed to allocate a unique remote checkpoint'
fi
remote_stage=${remote_stage%$'\r'}
is_safe_remote_stage "$remote_stage" ||
  die "hbox returned an unexpected stage path: $remote_stage"
remote_repo="$remote_stage/repo"
remote_artifacts="$remote_stage/artifacts"

if ! {
  printf 'set -euo pipefail\n'
  printf 'stage=%q\n' "$remote_stage"
  printf 'token=%q\n' "$checkpoint_token"
  cat <<'REMOTE_INIT'
test -d "$stage"
test ! -L "$stage"
test "$(realpath -- "$stage")" = "$stage"
marker="$stage/.uwueave-hbox-checkpoint-token"
test ! -e "$marker"
test ! -L "$marker"
(umask 077; set -C; printf '%s\n' "$token" >"$marker")
test -f "$marker"
test ! -L "$marker"
test "$(cat -- "$marker")" = "$token"
REMOTE_INIT
} | "$ssh_bin" -o BatchMode=yes -o ConnectTimeout=10 "$host" bash -s; then
  die 'failed to initialize the remote checkpoint marker'
fi

run_guarded_remote 'failed to create guarded remote checkpoint directories' \
  'mkdir -- "$stage/repo" "$stage/artifacts"'
note "uploading one-way to unique remote checkpoint: $remote_stage"
assert_remote_identity
if ! "$rsync_bin" -a --checksum "$snapshot_root/" "$host:$remote_repo/"; then
  die 'source upload failed'
fi
check_remote_source_types
if ! remote_snapshot_diff "$snapshot_root" "$remote_repo" \
    >"$metadata_root/remote-upload-drift.txt"; then
  die 'remote upload checksum dry-run failed'
fi
if [[ -s $metadata_root/remote-upload-drift.txt ]]; then
  sed -n '1,120p' "$metadata_root/remote-upload-drift.txt" >&2
  die 'remote upload failed its checksum comparison'
fi
assert_remote_identity
if ! "$rsync_bin" -a "$metadata_root/" \
    "$host:$remote_artifacts/source-metadata/"; then
  die 'source metadata upload failed'
fi

run_guarded_remote 'failed to make guarded remote source files read-only' \
  'find "$stage/repo" -type f -exec chmod a-w {} +'

note "running $run_label; command output is captured remotely"
set +e
{
  emit_remote_guard
  printf 'repo=%q\n' "$remote_repo"
  printf 'artifacts=%q\n' "$remote_artifacts"
  printf 'work_relative=%q\n' "$work_relative"
  printf 'command_argv=(\n'
  printf '  %q\n' "${command_argv[@]}"
  printf ')\n'
  cat <<'REMOTE_RUN'
export PATH="$HOME/.elan/bin:$PATH"
export TMPDIR=/tmp
export CARGO_HOME="$stage/cargo-home"
export CARGO_TARGET_DIR="$stage/cargo-target"
export UWUEAVE_HBOX_ARTIFACTS="$artifacts"
mkdir -p -- "$CARGO_HOME" "$CARGO_TARGET_DIR"
cd -- "$repo/$work_relative"
{
  printf 'utc='; date -u +%Y-%m-%dT%H:%M:%SZ
  printf 'host='; hostname
  printf 'cores='; getconf _NPROCESSORS_ONLN
  printf 'home_filesystem='; df -Pk "$HOME" | tail -1
  printf 'tank_filesystem='; df -Pk /tank | tail -1
  printf 'lean='; lean --version | head -1
  printf 'lake='; lake --version | head -1
  if command -v cargo >/dev/null 2>&1; then
    printf 'cargo='; cargo --version
  fi
  printf 'time='; /usr/bin/time --version | head -1
} >"$artifacts/environment.txt"
printf '%q ' "${command_argv[@]}" >"$artifacts/command.txt"
printf '\n' >>"$artifacts/command.txt"
set +e
/usr/bin/time -v -o "$artifacts/time.txt" -- "${command_argv[@]}" \
  >"$artifacts/stdout.log" 2>"$artifacts/stderr.log"
status=$?
set -e
printf '%s\n' "$status" >"$artifacts/exit-status.txt"
exit "$status"
REMOTE_RUN
} | "$ssh_bin" -o BatchMode=yes -o ConnectTimeout=10 "$host" bash -s
command_status=$?
set -e

check_remote_source_types

run_guarded_remote \
  'remote artifacts contain a symlink or special entry; refusing download' '
bad=$(find "$stage/artifacts" -mindepth 1 -type l -print -quit)
if test -n "$bad"; then
  printf "hbox-checkpoint remote: artifact symlink is not allowed: %s\n" "$bad" >&2
  exit 51
fi
bad=$(find "$stage/artifacts" -mindepth 1 ! -type d ! -type f ! -type l \
  -print -quit)
if test -n "$bad"; then
  printf "hbox-checkpoint remote: artifact special entry is not allowed: %s\n" "$bad" >&2
  exit 52
fi'

artifact_download=$(mktemp -d /tmp/uwueave-hbox-artifacts.XXXXXX)
is_safe_artifact_dir "$artifact_download" ||
  die "mktemp returned an unexpected artifact path: $artifact_download"
note "downloading logs only to: $artifact_download"
assert_remote_identity
if ! "$rsync_bin" -rt "$host:$remote_artifacts/" "$artifact_download/"; then
  die 'artifact download to local /tmp failed'
fi

check_local_artifact_types "$artifact_download"

if ! remote_snapshot_diff "$snapshot_root" "$remote_repo" \
    >"$artifact_download/remote-source-drift.txt"; then
  die 'post-command remote source checksum dry-run failed'
fi
if [[ -s $artifact_download/remote-source-drift.txt ]]; then
  note 'remote command changed source outside excluded build directories'
  (( command_status == 0 )) && command_status=1
fi

printf 'local_checkpoint=%s\n' "$local_stage"
printf 'remote_checkpoint=%s\n' "$remote_stage"
printf 'downloaded_artifacts=%s\n' "$artifact_download"
printf 'command_exit_status=%s\n' "$command_status"

exit "$command_status"
