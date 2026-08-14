#!/usr/bin/env bash
# Adversarial, fully mocked checks for scripts/hbox-checkpoint.sh.

set -euo pipefail

mock_note_call() {
  local kind=$1
  shift
  {
    printf '%s' "$kind"
    printf '\t%q' "$@"
    printf '\n'
  } >>"$UWUEAVE_HBOX_TEST_ROOT/operations.log"
}

mock_ssh() {
  local mock_root=$UWUEAVE_HBOX_TEST_ROOT
  mock_note_call ssh "$@"
  if [[ ${UWUEAVE_HBOX_TEST_FAIL_SSH:-0} == 1 ]]; then
    exit 97
  fi

  while [[ ${1:-} == -o ]]; do shift 2; done
  local host=${1:-}
  shift || true
  printf '%s\n' "$host" >>"$mock_root/ssh-hosts.log"

  if (( $# == 1 )) && [[ $1 == *'test -d /tank/dregg-build'* ]]; then
    printf 'preflight\n' >>"$mock_root/events.log"
    return 0
  fi
  if (( $# == 1 )) && [[ $1 == *'mktemp -d /tank/dregg-build/'* ]]; then
    local allocated
    allocated=$(mktemp -d "$mock_root/tank/dregg-build/uwueave-hbox-checkpoint.XXXXXX")
    printf 'allocate\n' >>"$mock_root/events.log"
    printf '%s\n' "${allocated#"$mock_root"}"
    return 0
  fi
  if [[ ${1:-} == bash && ${2:-} == -s ]]; then
    local payload
    payload=$(sed \
      -e "s|/usr/bin/time|$mock_root/bin/mock-time|g" \
      -e "s|/tank|$mock_root/tank|g")
    if [[ $payload == *'expected_token='* ]]; then
      printf 'guard\n' >>"$mock_root/events.log"
    elif [[ $payload == *'.uwueave-hbox-checkpoint-token'* ]]; then
      printf 'marker-init\n' >>"$mock_root/events.log"
    else
      printf 'ssh-script\n' >>"$mock_root/events.log"
    fi
    HOME="$mock_root/home" PATH="$mock_root/home/.elan/bin:$PATH" \
      bash -s <<<"$payload"
    return $?
  fi

  echo "mock ssh: unsupported invocation: $*" >&2
  exit 96
}

mock_rsync() {
  local mock_root=$UWUEAVE_HBOX_TEST_ROOT
  mock_note_call rsync "$@"
  if [[ ${UWUEAVE_HBOX_TEST_FAIL_RSYNC:-0} == 1 ]]; then
    exit 98
  fi

  local -a original=("$@")
  local -a mapped=()
  local argument
  local has_remote=0
  local dry_run=0
  for argument in "$@"; do
    if [[ $argument == --dry-run ||
          ( $argument == -* && $argument != --* && $argument == *n* ) ]]; then
      dry_run=1
    fi
    if [[ $argument == *:/tank/* ]]; then
      has_remote=1
      argument=${argument#*:}
      argument="$mock_root$argument"
    fi
    mapped+=("$argument")
  done

  local last_index=$((${#original[@]} - 1))
  local remote_destination=${original[$last_index]}
  if (( has_remote == 0 && dry_run == 0 )) &&
      [[ ${UWUEAVE_HBOX_TEST_INJECT_SENSITIVE_DURING_SNAPSHOT:-0} == 1 ]] &&
      [[ $remote_destination == /tmp/uwueave-hbox-checkpoint.*/repo/ ]] &&
      [[ ! -e $UWUEAVE_HBOX_REPO_ROOT/secret.pem ]]; then
    printf 'not-a-real-key\n' >"$UWUEAVE_HBOX_REPO_ROOT/secret.pem"
  fi
  if (( has_remote )); then
    printf 'rsync-remote\n' >>"$mock_root/events.log"
  else
    printf 'rsync-local\n' >>"$mock_root/events.log"
  fi

  /usr/bin/rsync "${mapped[@]}"

  if (( has_remote == 0 && dry_run == 1 )) &&
      [[ ${UWUEAVE_HBOX_TEST_REMOVE_SENSITIVE_AFTER_FINAL_DIFF:-0} == 1 ]] &&
      [[ $remote_destination == /tmp/uwueave-hbox-checkpoint.*/repo/ ]]; then
    local local_count_file="$mock_root/local-snapshot-dry-runs"
    local local_count=0
    [[ -f $local_count_file ]] && local_count=$(cat "$local_count_file")
    local_count=$((local_count + 1))
    printf '%s\n' "$local_count" >"$local_count_file"
    if (( local_count == 2 )); then
      rm -f -- "$UWUEAVE_HBOX_REPO_ROOT/secret.pem"
    fi
  fi

  local index
  for ((index = 0; index < last_index; index++)); do
    if [[ ${original[$index]} == *:/tank/*/artifacts/ ]]; then
      printf 'artifact-download\n' >>"$mock_root/events.log"
    fi
  done
  if (( dry_run == 0 )) && [[ $remote_destination == *:/tank/*/repo/ ]]; then
    local mapped_destination=${mapped[$last_index]}
    if [[ ${UWUEAVE_HBOX_TEST_REMOTE_SOURCE_SYMLINK:-0} == 1 ]]; then
      ln -s "$mock_root/SENTINEL" "$mapped_destination/InjectedLink"
    fi
    if [[ ${UWUEAVE_HBOX_TEST_TAMPER_MARKER:-0} == 1 ]]; then
      local stage=${mapped_destination%/repo/}
      printf 'tampered\n' >"$stage/.uwueave-hbox-checkpoint-token"
    fi
  fi
  if (( dry_run )) && [[ $remote_destination == *:/tank/*/repo/ ]] &&
      [[ ${UWUEAVE_HBOX_TEST_TAMPER_BEFORE_CLEANUP:-0} == 1 ]]; then
    local count_file="$mock_root/remote-repo-dry-runs"
    local count=0
    [[ -f $count_file ]] && count=$(cat "$count_file")
    count=$((count + 1))
    printf '%s\n' "$count" >"$count_file"
    if (( count == 2 )); then
      local stage=${mapped[$last_index]%/repo/}
      printf 'tampered-before-cleanup\n' \
        >"$stage/.uwueave-hbox-checkpoint-token"
    fi
  fi
}

mock_find() {
  mock_note_call find "$@"
  [[ ${UWUEAVE_HBOX_TEST_FAIL_FIND:-0} != 1 ]] || exit 92
  /usr/bin/find "$@"
}

mock_git() {
  mock_note_call git "$@"
  [[ ${UWUEAVE_HBOX_TEST_FAIL_GIT:-0} != 1 ]] || exit 91
  if [[ ${UWUEAVE_HBOX_TEST_FAIL_GIT_IGNORED:-0} == 1 ]]; then
    local argument
    for argument in "$@"; do
      [[ $argument != --ignored ]] || exit 90
    done
  fi
  /usr/bin/git "$@"
}

mock_time() {
  if [[ ${1:-} == --version ]]; then
    printf 'time (GNU Time) MOCK\n'
    return 0
  fi
  [[ ${1:-} == -v && ${2:-} == -o ]] || exit 95
  local time_log=$3
  shift 3
  [[ ${1:-} == -- ]] && shift

  case ${UWUEAVE_HBOX_TEST_ARTIFACT_KIND:-regular} in
    symlink)
      ln -s "$UWUEAVE_HBOX_TEST_ROOT/SENTINEL" \
        "$UWUEAVE_HBOX_ARTIFACTS/InjectedArtifact"
      ;;
    fifo)
      mkfifo "$UWUEAVE_HBOX_ARTIFACTS/InjectedArtifact"
      ;;
    mount)
      : >"$UWUEAVE_HBOX_TEST_ROOT/nested-mount-active"
      ;;
  esac

  set +e
  "$@"
  local command_status=$?
  set -e
  {
    printf 'Command being timed: MOCK\n'
    printf 'Elapsed (wall clock) time (h:mm:ss or m:ss): 0:00.00\n'
    printf 'Maximum resident set size (kbytes): 1\n'
    printf 'Exit status: %s\n' "$command_status"
  } >"$time_log"
  return "$command_status"
}

mock_tool() {
  case ${0##*/} in
    lean)
      printf 'Lean (version 4.30.0, MOCK, Release)\n'
      ;;
    lake)
      if [[ ${1:-} == --version ]]; then
        printf 'Lake version MOCK (Lean version 4.30.0)\n'
      elif [[ ${1:-} == build && $# == 1 ]]; then
        printf 'Build completed successfully (1 job).\n'
      else
        exit 94
      fi
      ;;
    cargo)
      if [[ ${1:-} == --version ]]; then
        printf 'cargo 1.99.0-mock\n'
      elif [[ ${1:-} == test && ${2:-} == --all-targets &&
              ${3:-} == --no-run && $# == 3 ]]; then
        printf 'CARGO_HOME=%s\nCARGO_TARGET_DIR=%s\n' \
          "$CARGO_HOME" "$CARGO_TARGET_DIR" \
          >"$UWUEAVE_HBOX_ARTIFACTS/cargo-environment.txt"
        printf 'Finished mock cargo build\n' >&2
      else
        exit 93
      fi
      ;;
    findmnt)
      if [[ -f $UWUEAVE_HBOX_TEST_ROOT/nested-mount-active ]]; then
        local argument target=''
        while (( $# > 0 )); do
          argument=$1
          shift
          if [[ $argument == --target && $# -gt 0 ]]; then
            target=$1
            shift
          fi
        done
        [[ -n $target ]] && printf '%s/artifacts/nested-mount\n' "$target"
      fi
      ;;
  esac
}

if [[ ${UWUEAVE_HBOX_TEST_DISPATCH:-0} == 1 ]]; then
  case ${0##*/} in
    mock-ssh) mock_ssh "$@"; exit $? ;;
    mock-rsync) mock_rsync "$@"; exit $? ;;
    mock-find) mock_find "$@"; exit $? ;;
    mock-git) mock_git "$@"; exit $? ;;
    mock-time) mock_time "$@"; exit $? ;;
    lean|lake|cargo|findmnt) mock_tool "$@"; exit $? ;;
  esac
fi

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
helper="$repo_root/scripts/hbox-checkpoint.sh"

test_root=$(mktemp -d /tmp/uwueave-hbox-checkpoint-test.XXXXXX)
test_root=$(realpath -- "$test_root")
[[ $test_root =~ ^/(private/)?tmp/uwueave-hbox-checkpoint-test\.[A-Za-z0-9]+$ ]]
trap 'rm -rf -- "$test_root"' EXIT HUP INT TERM

mkdir -p "$test_root/bin" "$test_root/home/.elan/bin" \
  "$test_root/tank/dregg-build"
printf 'do not delete\n' >"$test_root/SENTINEL"
printf 'do not delete\n' >"$test_root/tank/dregg-build/SENTINEL"
: >"$test_root/operations.log"
: >"$test_root/events.log"
: >"$test_root/ssh-hosts.log"

for name in mock-ssh mock-rsync mock-time mock-find mock-git; do
  ln "$0" "$test_root/bin/$name"
done
for name in lean lake cargo findmnt; do
  ln "$0" "$test_root/home/.elan/bin/$name"
done

fixture="$test_root/fixture"
mkdir -p "$fixture/.lake" "$fixture/rust" "$fixture/Uwueave"
printf 'preserve local olean\n' >"$fixture/.lake/Preserve.olean"
printf 'excluded test fixture only\n' >"$fixture/.lake/secret.pem"
printf '.lake/\ntarget/\nsecret.pem\n' >"$fixture/.gitignore"
printf 'leanprover/lean4:v4.30.0\n' >"$fixture/lean-toolchain"
printf '[package]\nname = "fixture"\nversion = "0.0.0"\n' \
  >"$fixture/rust/Cargo.toml"
printf 'def fixture : Nat := 1\n' >"$fixture/Uwueave/Fixture.lean"
git -C "$fixture" init -q
git -C "$fixture" config user.name 'Hbox Checkpoint Test'
git -C "$fixture" config user.email 'hbox-checkpoint@example.invalid'
git -C "$fixture" add .
git -C "$fixture" commit -qm fixture

mock_env=(
  UWUEAVE_HBOX_TEST_DISPATCH=1
  UWUEAVE_HBOX_TEST_ROOT="$test_root"
  UWUEAVE_HBOX_HOST=hbox
  UWUEAVE_HBOX_SSH="$test_root/bin/mock-ssh"
  UWUEAVE_HBOX_RSYNC="$test_root/bin/mock-rsync"
  UWUEAVE_HBOX_FIND="$test_root/bin/mock-find"
  UWUEAVE_HBOX_GIT="$test_root/bin/mock-git"
  UWUEAVE_HBOX_REPO_ROOT="$fixture"
)

reset_mock_logs() {
  : >"$test_root/operations.log"
  : >"$test_root/events.log"
  : >"$test_root/ssh-hosts.log"
  rm -f "$test_root/remote-repo-dry-runs"
  rm -f "$test_root/local-snapshot-dry-runs"
  rm -f "$test_root/nested-mount-active"
}

last_stderr_line() {
  tail -1 "$1"
}

expect_failure() {
  local expected=$1
  shift
  local stdout="$test_root/failure.stdout"
  local stderr="$test_root/failure.stderr"
  if "$@" >"$stdout" 2>"$stderr"; then
    echo "hbox-checkpoint test: expected failure: $expected" >&2
    exit 1
  fi
  [[ $(last_stderr_line "$stderr") == "$expected" ]] || {
    printf 'hbox-checkpoint test: wrong final diagnostic\nexpected: %s\nactual:\n' \
      "$expected" >&2
    cat "$stderr" >&2
    exit 1
  }
}

bash -n "$helper"
help_output=$(UWUEAVE_HBOX_SSH=/bin/false "$helper" --help)
[[ $help_output == *'lake-build'* ]]
[[ $help_output == *'cargo-no-run'* ]]
[[ $help_output == *'There is deliberately no generic remote-command mode.'* ]]
[[ $help_output == *'/tank/dregg-build'* ]]
[[ $help_output == *'GNU time'* ]]
default_output=$(UWUEAVE_HBOX_SSH=/bin/false "$helper")
[[ $default_output == *'With no arguments, print this help and do nothing.'* ]]
"$helper" self-check

reset_mock_logs
expect_failure 'hbox-checkpoint: unknown subcommand: command' \
  env "${mock_env[@]}" "$helper" command -- true
[[ ! -s $test_root/operations.log ]]

# Host grammar rejects option-like, dotted-relative, path, and empty-label forms
# before either mocked transport can run.
for bad_host in '-oProxyCommand=bad' '.hbox' 'hbox.' '..' 'hbox/path' 'hbox..example'; do
  reset_mock_logs
  expect_failure "hbox-checkpoint: unsafe SSH host: $bad_host" \
    env "${mock_env[@]}" UWUEAVE_HBOX_HOST="$bad_host" "$helper" lake-build
  [[ ! -s $test_root/operations.log ]]
done

# Local scan producers cannot fail closed as an empty result. Both Git queries
# have distinct diagnostics, and no snapshot or transport starts after failure.
reset_mock_logs
expect_failure 'hbox-checkpoint: failed to scan included symlinks' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_FAIL_FIND=1 \
    "$helper" lake-build
if rg -q '^(ssh|rsync)' "$test_root/operations.log"; then
  echo 'hbox-checkpoint test: transport ran after local find failure' >&2
  exit 1
fi

reset_mock_logs
expect_failure 'hbox-checkpoint: failed to enumerate untracked paths' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_FAIL_GIT=1 \
    "$helper" lake-build
if rg -q '^(ssh|rsync)' "$test_root/operations.log"; then
  echo 'hbox-checkpoint test: transport ran after local git failure' >&2
  exit 1
fi

reset_mock_logs
expect_failure 'hbox-checkpoint: failed to enumerate ignored untracked paths' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_FAIL_GIT_IGNORED=1 \
    "$helper" lake-build
if rg -q '^(ssh|rsync)' "$test_root/operations.log"; then
  echo 'hbox-checkpoint test: transport ran after ignored git failure' >&2
  exit 1
fi

# Local included symlinks are shown and refused before rsync or SSH.
ln -s Uwueave/Fixture.lean "$fixture/IncludedLink"
reset_mock_logs
expect_failure 'hbox-checkpoint: checkpoint source contains included symlinks' \
  env "${mock_env[@]}" "$helper" lake-build
rg -q 'included symlink is not allowed: IncludedLink' "$test_root/failure.stderr"
if rg -q '^(ssh|rsync)' "$test_root/operations.log"; then
  echo 'hbox-checkpoint test: transport ran after symlink refusal' >&2
  exit 1
fi
rm "$fixture/IncludedLink"

# A symlink whose name resembles an excluded directory must still be rejected.
mv "$fixture/.lake" "$fixture/.lake-real"
ln -s Uwueave "$fixture/.lake"
reset_mock_logs
expect_failure 'hbox-checkpoint: checkpoint source contains included symlinks' \
  env "${mock_env[@]}" "$helper" lake-build
rg -q 'included symlink is not allowed: \.lake' "$test_root/failure.stderr"
if rg -q '^(ssh|rsync)' "$test_root/operations.log"; then
  echo 'hbox-checkpoint test: transport ran after excluded-name symlink refusal' >&2
  exit 1
fi
rm "$fixture/.lake"
mv "$fixture/.lake-real" "$fixture/.lake"

# Nested excluded-name symlinks and special entries are also detected, rather
# than being hidden by directory-name pruning.
mkdir -p "$fixture/Nested"
ln -s ../Uwueave "$fixture/Nested/.lake"
reset_mock_logs
expect_failure 'hbox-checkpoint: checkpoint source contains included symlinks' \
  env "${mock_env[@]}" "$helper" lake-build
rg -q 'included symlink is not allowed: Nested/\.lake' \
  "$test_root/failure.stderr"
rm "$fixture/Nested/.lake"
mkfifo "$fixture/Nested/.lake"
reset_mock_logs
expect_failure \
  'hbox-checkpoint: checkpoint source contains included special entries' \
  env "${mock_env[@]}" "$helper" lake-build
rg -q 'included special entry is not allowed: Nested/\.lake' \
  "$test_root/failure.stderr"
rm "$fixture/Nested/.lake"

# Sensitive untracked paths are likewise shown and refused before transport.
printf 'SECRET=not-real\n' >"$fixture/.env"
reset_mock_logs
expect_failure 'hbox-checkpoint: refusing checkpoint with sensitive untracked paths' \
  env "${mock_env[@]}" "$helper" lake-build
rg -q 'sensitive untracked path is not allowed: \.env' "$test_root/failure.stderr"
if rg -q '^(ssh|rsync)' "$test_root/operations.log"; then
  echo 'hbox-checkpoint test: transport ran after sensitive-path refusal' >&2
  exit 1
fi
rm "$fixture/.env"

# Ignored untracked sensitive names are scanned too, unless they are under one
# of the exact rsync-excluded directory components.
printf 'not-a-real-key\n' >"$fixture/secret.pem"
reset_mock_logs
expect_failure 'hbox-checkpoint: refusing checkpoint with sensitive untracked paths' \
  env "${mock_env[@]}" "$helper" lake-build
rg -q 'sensitive untracked path is not allowed: secret\.pem' \
  "$test_root/failure.stderr"
[[ ! -s $test_root/ssh-hosts.log ]]
rm "$fixture/secret.pem"

# A sensitive ignored file introduced after preflight but before snapshot copy
# lands in a checksum-stable snapshot. The post-snapshot scan must still refuse
# it before SSH.
reset_mock_logs
expect_failure 'hbox-checkpoint: refusing checkpoint with sensitive untracked paths' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_INJECT_SENSITIVE_DURING_SNAPSHOT=1 \
    "$helper" lake-build
rg -q 'sensitive untracked path is not allowed: secret\.pem' \
  "$test_root/failure.stderr"
[[ ! -s $test_root/ssh-hosts.log ]]
rm "$fixture/secret.pem"

# The ignored secret survives in the frozen snapshot through both checksum
# comparisons, then disappears from the mutable checkout. The snapshot scan,
# not the checkout rescan, must still reject it before SSH.
reset_mock_logs
expect_failure \
  'hbox-checkpoint: refusing frozen snapshot with sensitive path names' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_INJECT_SENSITIVE_DURING_SNAPSHOT=1 \
    UWUEAVE_HBOX_TEST_REMOVE_SENSITIVE_AFTER_FINAL_DIFF=1 \
    "$helper" lake-build
rg -q 'sensitive path is not allowed in frozen snapshot: secret\.pem' \
  "$test_root/failure.stderr"
[[ ! -e $fixture/secret.pem ]]
[[ ! -s $test_root/ssh-hosts.log ]]

# Transport failures receive stable wrapper diagnostics.
reset_mock_logs
expect_failure 'hbox-checkpoint: local snapshot copy failed' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_FAIL_RSYNC=1 \
    "$helper" --cleanup lake-build
[[ ! -s $test_root/ssh-hosts.log ]]

reset_mock_logs
expect_failure 'hbox-checkpoint: hbox prerequisite check failed for host: hbox' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_FAIL_SSH=1 \
    "$helper" --cleanup lake-build
[[ -s $test_root/ssh-hosts.log || -s $test_root/operations.log ]]

# A mocked upload that introduces a remote source symlink is rejected before the
# fixed build schema runs.
reset_mock_logs
expect_failure 'hbox-checkpoint: remote source identity/type check failed' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_REMOTE_SOURCE_SYMLINK=1 \
    "$helper" --cleanup lake-build
rg -q 'hbox-checkpoint remote: included symlink is not allowed:' \
  "$test_root/failure.stderr"

# Marker tampering prevents the next remote operation. Without --cleanup the
# mock stage is retained, demonstrating fail-closed identity behavior.
reset_mock_logs
expect_failure \
  'hbox-checkpoint: remote checkpoint marker or non-symlink identity check failed' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_TAMPER_MARKER=1 \
    "$helper" lake-build
leaked_local=$(sed -n \
  's/^hbox-checkpoint: copying checkout to unique local checkpoint: //p' \
  "$test_root/failure.stderr")
[[ $leaked_local == /tmp/uwueave-hbox-checkpoint.* ]]
rm -rf -- "$leaked_local"

# Token verification is repeated inside cleanup. Tampering after the final
# checksum leaves the remote stage untouched while still cleaning local state.
reset_mock_logs
expect_failure 'hbox-checkpoint: one or more opt-in cleanup operations failed' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_TAMPER_BEFORE_CLEANUP=1 \
    "$helper" --cleanup lake-build
rg -q 'refusing or failing cleanup of unverified remote checkpoint:' \
  "$test_root/failure.stderr"
cleanup_local=$(awk -F= '$1 == "local_checkpoint" {print $2}' \
  "$test_root/failure.stdout")
cleanup_remote=$(awk -F= '$1 == "remote_checkpoint" {print $2}' \
  "$test_root/failure.stdout")
cleanup_artifacts=$(awk -F= '$1 == "downloaded_artifacts" {print $2}' \
  "$test_root/failure.stdout")
[[ ! -e $cleanup_local ]]
[[ -d $test_root$cleanup_remote ]]
[[ -f $test_root/tank/dregg-build/SENTINEL ]]
rm -rf -- "$cleanup_artifacts"

# Symlink and special artifact entries fail before any remote-to-local artifact
# rsync. The metadata upload is allowed, so distinguish rsync source direction.
for artifact_kind in symlink fifo; do
  reset_mock_logs
  expect_failure \
    'hbox-checkpoint: remote artifacts contain a symlink or special entry; refusing download' \
    env "${mock_env[@]}" UWUEAVE_HBOX_TEST_ARTIFACT_KIND="$artifact_kind" \
      "$helper" --cleanup lake-build
  if rg -q '^artifact-download$' "$test_root/events.log"; then
    echo 'hbox-checkpoint test: artifact download started after type rejection' >&2
    exit 1
  fi
done

# A descendant mount reported after the command blocks artifact handling and
# also makes opt-in cleanup fail closed, leaving the marked remote stage intact.
reset_mock_logs
expect_failure 'hbox-checkpoint: one or more opt-in cleanup operations failed' \
  env "${mock_env[@]}" UWUEAVE_HBOX_TEST_ARTIFACT_KIND=mount \
    "$helper" --cleanup lake-build
rg -q 'remote checkpoint marker or non-symlink identity check failed' \
  "$test_root/failure.stderr"
rg -q 'refusing or failing cleanup of unverified remote checkpoint:' \
  "$test_root/failure.stderr"
if rg -q '^artifact-download$' "$test_root/events.log"; then
  echo 'hbox-checkpoint test: artifact download started across descendant mount' >&2
  exit 1
fi

# Fully mocked successful lifecycle: marker-guarded remote operations, fixed
# command, /tmp-only download, exact cleanup, and an unrelated sentinel kept.
reset_mock_logs
lifecycle_stdout="$test_root/lifecycle.stdout"
env "${mock_env[@]}" "$helper" --cleanup lake-build >"$lifecycle_stdout"
local_checkpoint=$(awk -F= '$1 == "local_checkpoint" {print $2}' "$lifecycle_stdout")
remote_checkpoint=$(awk -F= '$1 == "remote_checkpoint" {print $2}' "$lifecycle_stdout")
downloaded_artifacts=$(awk -F= '$1 == "downloaded_artifacts" {print $2}' "$lifecycle_stdout")
[[ $local_checkpoint == /tmp/uwueave-hbox-checkpoint.* ]]
[[ $remote_checkpoint == /tank/dregg-build/uwueave-hbox-checkpoint.* ]]
[[ $downloaded_artifacts == /tmp/uwueave-hbox-artifacts.* ]]
[[ ! -e $local_checkpoint ]]
[[ ! -e $test_root$remote_checkpoint ]]
[[ -f $test_root/tank/dregg-build/SENTINEL ]]
[[ $(cat "$test_root/tank/dregg-build/SENTINEL") == 'do not delete' ]]
[[ $(cat "$fixture/.lake/Preserve.olean") == 'preserve local olean' ]]
[[ $(cat "$fixture/.lake/secret.pem") == 'excluded test fixture only' ]]
[[ $(cat "$downloaded_artifacts/exit-status.txt") == 0 ]]
[[ ! -s $downloaded_artifacts/remote-source-drift.txt ]]
[[ -f $downloaded_artifacts/source-metadata/snapshot-final-drift.txt ]]
[[ ! -s $downloaded_artifacts/source-metadata/snapshot-final-drift.txt ]]

# Each stage-related rsync is immediately preceded by a marker guard.
awk '
  $0 == "rsync-remote" && previous != "guard" { exit 1 }
  { previous = $0 }
' "$test_root/events.log"
[[ $(cat "$test_root/ssh-hosts.log" | LC_ALL=C sort -u) == hbox ]]

rm -rf -- "$downloaded_artifacts"

# The second fixed schema also remains confined to the checkpoint.
reset_mock_logs
cargo_stdout="$test_root/cargo.stdout"
env "${mock_env[@]}" "$helper" --cleanup cargo-no-run >"$cargo_stdout"
cargo_artifacts=$(awk -F= '$1 == "downloaded_artifacts" {print $2}' \
  "$cargo_stdout")
[[ $(cat "$cargo_artifacts/exit-status.txt") == 0 ]]
[[ $(cat "$cargo_artifacts/command.txt") == \
   'cargo test --all-targets --no-run ' ]]
rg -q '^CARGO_HOME=.*/uwueave-hbox-checkpoint\.[A-Za-z0-9]+/cargo-home$' \
  "$cargo_artifacts/cargo-environment.txt"
rg -q '^CARGO_TARGET_DIR=.*/uwueave-hbox-checkpoint\.[A-Za-z0-9]+/cargo-target$' \
  "$cargo_artifacts/cargo-environment.txt"
[[ $(cat "$fixture/.lake/Preserve.olean") == 'preserve local olean' ]]
[[ -f $test_root/tank/dregg-build/SENTINEL ]]
rm -rf -- "$cargo_artifacts"

printf 'hbox-checkpoint adversarial tests passed (mocked; no real SSH)\n'
