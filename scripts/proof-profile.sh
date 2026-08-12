#!/usr/bin/env bash
# Profile Lean source modules serially and report warm-run medians as TSV.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/proof-profile.sh [LEAN_SOURCE ...]

Run Lean's built-in declaration profiler over each source, serially, without
writing an olean or clearing any cache. One unmeasured warmup precedes an odd
number of measured runs. The only stdout is a machine-readable TSV summary;
progress and failed-run logs go to stderr.

Defaults:
  LEAN_SOURCE                  Uwueave/Preo/Demo.lean
  UWUEAVE_PROFILE_RUNS         3 (must be a positive odd integer)
  UWUEAVE_PROFILE_WARMUPS      1 (must be a nonnegative integer)

Example:
  scripts/proof-profile.sh Uwueave/Preo/Elab.lean Uwueave/Preo/Demo.lean
EOF
}

case "${1:-}" in
  -h|--help)
    usage
    exit 0
    ;;
esac

runs=${UWUEAVE_PROFILE_RUNS:-3}
warmups=${UWUEAVE_PROFILE_WARMUPS:-1}

if ! [[ $runs =~ ^[0-9]+$ ]] || (( runs == 0 || runs % 2 == 0 )); then
  echo "proof-profile: UWUEAVE_PROFILE_RUNS must be a positive odd integer" >&2
  exit 2
fi
if ! [[ $warmups =~ ^[0-9]+$ ]]; then
  echo "proof-profile: UWUEAVE_PROFILE_WARMUPS must be a nonnegative integer" >&2
  exit 2
fi

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
cd -- "$repo_root"

if (( $# == 0 )); then
  set -- Uwueave/Preo/Demo.lean
fi

for source in "$@"; do
  if [[ ! -f $source ]]; then
    echo "proof-profile: source does not exist: $source" >&2
    exit 2
  fi
done

tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/uwueave-proof-profile.XXXXXX")
trap 'rm -rf -- "$tmp_dir"' EXIT HUP INT TERM

median_file() {
  local values=$1
  local middle=$((runs / 2 + 1))
  LC_ALL=C sort -n -- "$values" | sed -n "${middle}p"
}

profile_ms() {
  local log=$1
  local label=$2
  LC_ALL=C awk -v wanted="$label" '
    /^cumulative profiling times:/ { cumulative = 1; next }
    cumulative && /^[[:space:]]/ {
      line = $0
      sub(/^[[:space:]]+/, "", line)
      if (index(line, wanted " ") != 1) next
      value = $NF
      if (value ~ /ms$/) {
        sub(/ms$/, "", value)
        total += value
      } else if (value ~ /s$/) {
        sub(/s$/, "", value)
        total += 1000 * value
      }
    }
    END { printf "%.6f\n", total + 0 }
  ' "$log"
}

compile_ms() {
  local log=$1
  LC_ALL=C awk '
    /^cumulative profiling times:/ { cumulative = 1; next }
    cumulative && /^[[:space:]]/ {
      line = $0
      sub(/^[[:space:]]+/, "", line)
      if (index(line, "compilation (") != 1) next
      value = $NF
      if (value ~ /ms$/) {
        sub(/ms$/, "", value)
        total += value
      } else if (value ~ /s$/) {
        sub(/s$/, "", value)
        total += 1000 * value
      }
    }
    END { printf "%.6f\n", total + 0 }
  ' "$log"
}

time_value() {
  local log=$1
  local key=$2
  LC_ALL=C awk -v wanted="$key" '
    wanted == "maximum resident set size" && $0 ~ /^[[:space:]]*[0-9]+[[:space:]]+maximum resident set size$/ {
      value = $1
      next
    }
    wanted != "maximum resident set size" && $1 == wanted && NF == 2 {
      value = $2
    }
    END {
      if (value == "") exit 1
      print value
    }
  ' "$log"
}

printf 'module\truns\twarmups\twall_s\tuser_s\tsys_s\trss_bytes\timport_ms\tinterpretation_ms\telaboration_ms\ttypecheck_ms\ttypeclass_ms\ttactic_ms\tcompile_ms\n'

module_index=0
for source in "$@"; do
  module_index=$((module_index + 1))
  echo "proof-profile: warming $source ($warmups run(s))" >&2
  for ((i = 1; i <= warmups; i++)); do
    warm_log="$tmp_dir/warm-${module_index}-${i}.log"
    if ! lake env lean "$source" >"$warm_log" 2>&1; then
      echo "proof-profile: warmup failed for $source" >&2
      sed -n '1,240p' "$warm_log" >&2
      exit 1
    fi
  done

  metrics=(wall user sys rss import interpretation elaboration typecheck typeclass tactic compile)
  for metric in "${metrics[@]}"; do
    : >"$tmp_dir/${module_index}-${metric}.values"
  done

  echo "proof-profile: measuring $source ($runs serialized run(s))" >&2
  for ((i = 1; i <= runs; i++)); do
    log="$tmp_dir/run-${module_index}-${i}.log"
    if ! /usr/bin/time -lp lake env lean --profile "$source" >"$log" 2>&1; then
      echo "proof-profile: measured run $i failed for $source" >&2
      sed -n '1,320p' "$log" >&2
      exit 1
    fi

    time_value "$log" 'real' >>"$tmp_dir/${module_index}-wall.values"
    time_value "$log" 'user' >>"$tmp_dir/${module_index}-user.values"
    time_value "$log" 'sys' >>"$tmp_dir/${module_index}-sys.values"
    time_value "$log" 'maximum resident set size' >>"$tmp_dir/${module_index}-rss.values"
    profile_ms "$log" 'import' >>"$tmp_dir/${module_index}-import.values"
    profile_ms "$log" 'interpretation' >>"$tmp_dir/${module_index}-interpretation.values"
    profile_ms "$log" 'elaboration' >>"$tmp_dir/${module_index}-elaboration.values"
    profile_ms "$log" 'type checking' >>"$tmp_dir/${module_index}-typecheck.values"
    profile_ms "$log" 'typeclass inference' >>"$tmp_dir/${module_index}-typeclass.values"
    profile_ms "$log" 'tactic execution' >>"$tmp_dir/${module_index}-tactic.values"
    compile_ms "$log" >>"$tmp_dir/${module_index}-compile.values"
  done

  printf '%s\t%s\t%s' "$source" "$runs" "$warmups"
  for metric in "${metrics[@]}"; do
    printf '\t%s' "$(median_file "$tmp_dir/${module_index}-${metric}.values")"
  done
  printf '\n'
done
