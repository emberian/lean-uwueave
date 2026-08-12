#!/usr/bin/env bash
# Deterministic Preoscript command corpus: exact goldens plus low-noise profiles.

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/preo-bench.sh MODE [ARG ...]

Modes:
  golden                    Check diagnostics, rollback, names/types/rows, report.
  record-goldens DIR        Write freshly canonicalized goldens below DIR.
  profile [ROOT]            Profile the corpus in ROOT (default: this checkout).
  baseline [COMMIT]         Profile COMMIT in an isolated temporary worktree.
                            Default: ab4c767.
  compare BASELINE CURRENT  Apply regression and scaling thresholds to two TSVs.
  all                       Run goldens, current profile, and compare with the
                            committed ab4c767 baseline.

Profiling uses two warmups and five measured serialized `lean -j1 --profile`
runs by default. If wall or user MAD exceeds 8%, it retries with nine measured
runs and marks persistent noise in the TSV. No cache is cleared and no trace
profiler is enabled.

Environment:
  PREO_BENCH_WARMUPS   warmups (default 2)
  PREO_BENCH_RUNS      measured runs (default 5; positive odd)
  PREO_BENCH_CASE      exact case-name filter (default all)
  PREO_BENCH_SKIP_BUILD=1  trust existing dependency oleans
EOF
}

script_dir=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH='' cd -- "$script_dir/.." && pwd)
golden_dir="$repo_root/tests/preo-bench/golden"
expected_dir="$golden_dir/expected"
baseline_file="$repo_root/tests/preo-bench/baselines/ab4c767.tsv"

warmups=${PREO_BENCH_WARMUPS:-2}
runs=${PREO_BENCH_RUNS:-5}
case_filter=${PREO_BENCH_CASE:-}

if ! [[ $warmups =~ ^[0-9]+$ ]]; then
  echo "preo-bench: PREO_BENCH_WARMUPS must be a nonnegative integer" >&2
  exit 2
fi
if ! [[ $runs =~ ^[0-9]+$ ]] || (( runs == 0 || runs % 2 == 0 )); then
  echo "preo-bench: PREO_BENCH_RUNS must be a positive odd integer" >&2
  exit 2
fi

cases=(
  'import_syntax|tests/preo-bench/perf/ImportSyntax.lean|import|0'
  'import_elab|tests/preo-bench/perf/ImportElab.lean|import|0'
  'import_protocol_surface|tests/preo-bench/perf/ImportProtocolSurface.lean|import|0'
  'fields_1|tests/preo-bench/perf/Fields1.lean|fields|1'
  'fields_8|tests/preo-bench/perf/Fields8.lean|fields|8'
  'fields_32|tests/preo-bench/perf/Fields32.lean|fields|32'
  'custom_1|tests/preo-bench/perf/Custom1.lean|custom|1'
  'custom_8|tests/preo-bench/perf/Custom8.lean|custom|8'
  'custom_32|tests/preo-bench/perf/Custom32.lean|custom|32'
  'typed_0|tests/preo-bench/perf/Typed0.lean|typed|0'
  'typed_1|tests/preo-bench/perf/Typed1.lean|typed|1'
  'typed_4|tests/preo-bench/perf/Typed4.lean|typed|4'
  'typed_16|tests/preo-bench/perf/Typed16.lean|typed|16'
  'future_certificate|tests/preo-bench/perf/FutureCertificate.lean|command|1'
  'protocol_session|tests/preo-bench/perf/ProtocolSession.lean|command|1'
  'native_protocol|tests/preo-bench/perf/NativeProtocol.lean|command|1'
  'budget|tests/preo-bench/perf/Budget.lean|command|1'
  'export|tests/preo-bench/perf/Export.lean|command|1'
  'report|tests/preo-bench/perf/Report.lean|command|1'
  'all_commands|tests/preo-bench/perf/AllCommands.lean|command|1'
  'rollback_negative|tests/preo-bench/perf/RollbackReuse.lean|rollback|1'
)

tmp_dir=''
worktree_path=''
cleanup() {
  if [[ -n $worktree_path && -d $worktree_path ]]; then
    git -C "$repo_root" worktree remove --force "$worktree_path" >/dev/null 2>&1 || true
    worktree_path=''
  fi
  if [[ -n $tmp_dir && -d $tmp_dir ]]; then
    rm -rf -- "$tmp_dir"
  fi
}
trap cleanup EXIT HUP INT TERM

make_tmp() {
  if [[ -z $tmp_dir ]]; then
    tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/uwueave-preo-bench.XXXXXX")
  fi
}

prepare_root() {
  local root=$1
  if [[ ${PREO_BENCH_SKIP_BUILD:-0} != 1 ]]; then
    echo "preo-bench: refreshing benchmark dependencies in $root" >&2
    (cd -- "$root" && lake build Uwueave.Preo.Elab Uwueave.Preo.ProtocolSurface) >&2
  fi
}

run_lean() {
  local root=$1
  shift
  (cd -- "$root" && lake env lean -j1 "$@")
}

canonical_json_messages() {
  local json=$1
  jq -r 'select(.severity == "information") | .data // empty' "$json"
}

capture_goldens() {
  local root=$1
  local out=$2
  make_tmp
  mkdir -p -- "$out"
  local raw_dir
  raw_dir=$(mktemp -d "$tmp_dir/golden-raw.XXXXXX")
  local names_json="$raw_dir/names.json"
  local report_json="$raw_dir/report.json"
  local diagnostics_json="$raw_dir/diagnostics.json"

  run_lean "$root" --json tests/preo-bench/golden/NamesTypesRows.lean >"$names_json"
  canonical_json_messages "$names_json" |
    LC_ALL=C awk '/^(CONST|ROW)\t/' >"$out/names-types-rows.tsv"

  run_lean "$root" --json tests/preo-bench/golden/Report.lean >"$report_json"
  jq -r 'select(.severity == "information" and
      (.data | startswith("preo PreoBench.Golden.Report.Subject\n"))) | .data' \
    "$report_json" >"$out/report.txt"

  # The exact diagnostics are embedded in #guard_msgs. Reusing both failed
  # names successfully in the same environment is the transactional gate.
  run_lean "$root" --json tests/preo-bench/golden/DiagnosticsRollback.lean \
    >"$diagnostics_json"
  printf 'diagnostics-and-rollback\tOK\n' >"$out/diagnostics-rollback.tsv"
}

golden_check() {
  make_tmp
  prepare_root "$repo_root"
  local actual="$tmp_dir/golden"
  capture_goldens "$repo_root" "$actual"
  local failed=0
  for file in names-types-rows.tsv report.txt diagnostics-rollback.tsv; do
    if ! cmp -s -- "$expected_dir/$file" "$actual/$file"; then
      echo "preo-bench: golden mismatch: $file" >&2
      diff -u -- "$expected_dir/$file" "$actual/$file" >&2 || true
      failed=1
    fi
  done
  (( failed == 0 )) || exit 1
  local count
  count=$(LC_ALL=C awk '$1 == "CONST" { n++ } END { print n + 0 }' \
    "$actual/names-types-rows.tsv")
  printf 'gate\tstatus\tdeclarations\nexact-goldens\tpass\t%s\n' "$count"
}

median() {
  local file=$1
  local n
  n=$(wc -l <"$file" | tr -d ' ')
  LC_ALL=C sort -n -- "$file" | sed -n "$((n / 2 + 1))p"
}

mad_pct() {
  local file=$1
  local med
  med=$(median "$file")
  if awk -v m="$med" 'BEGIN { exit !(m == 0) }'; then
    printf '0.000000\n'
    return
  fi
  local deviations="$file.mad"
  LC_ALL=C awk -v m="$med" '{ d = $1 - m; if (d < 0) d = -d; print d }' \
    "$file" >"$deviations"
  local mad
  mad=$(median "$deviations")
  awk -v mad="$mad" -v med="$med" 'BEGIN { printf "%.6f\n", 100 * mad / med }'
}

time_value() {
  local log=$1
  local key=$2
  LC_ALL=C awk -v wanted="$key" '
    wanted == "maximum resident set size" &&
      $0 ~ /^[[:space:]]*[0-9]+[[:space:]]+maximum resident set size$/ {
        value = $1; next
      }
    wanted != "maximum resident set size" && $1 == wanted && NF == 2 {
      value = $2
    }
    END { if (value == "") exit 1; print value }
  ' "$log"
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
      if (value ~ /ms$/) { sub(/ms$/, "", value); total += value }
      else if (value ~ /s$/) { sub(/s$/, "", value); total += 1000 * value }
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
      if (value ~ /ms$/) { sub(/ms$/, "", value); total += value }
      else if (value ~ /s$/) { sub(/s$/, "", value); total += 1000 * value }
    }
    END { printf "%.6f\n", total + 0 }
  ' "$log"
}

measure_case() {
  local root=$1 name=$2 source=$3 group=$4 items=$5 requested_runs=$6
  local case_dir="$tmp_dir/profile-$name"
  mkdir -p -- "$case_dir"
  local metrics=(wall user sys rss import interpretation elaboration typecheck typeclass tactic compile)

  echo "preo-bench: warming $name ($warmups run(s))" >&2
  local i
  for ((i = 1; i <= warmups; i++)); do
    if ! run_lean "$root" "$source" >"$case_dir/warm-$i.log" 2>&1; then
      echo "preo-bench: warmup failed: $name" >&2
      sed -n '1,240p' "$case_dir/warm-$i.log" >&2
      return 1
    fi
  done

  run_measurements() {
    local count=$1
    local metric
    for metric in "${metrics[@]}"; do
      : >"$case_dir/$metric.values"
    done
    echo "preo-bench: measuring $name ($count run(s), serialized)" >&2
    for ((i = 1; i <= count; i++)); do
      local log="$case_dir/run-$i.log"
      if ! (cd -- "$root" && /usr/bin/time -lp lake env lean -j1 --profile "$source") \
          >"$log" 2>&1; then
        echo "preo-bench: measured run failed: $name/$i" >&2
        sed -n '1,320p' "$log" >&2
        return 1
      fi
      time_value "$log" real >>"$case_dir/wall.values"
      time_value "$log" user >>"$case_dir/user.values"
      time_value "$log" sys >>"$case_dir/sys.values"
      time_value "$log" 'maximum resident set size' >>"$case_dir/rss.values"
      profile_ms "$log" import >>"$case_dir/import.values"
      profile_ms "$log" interpretation >>"$case_dir/interpretation.values"
      profile_ms "$log" elaboration >>"$case_dir/elaboration.values"
      profile_ms "$log" 'type checking' >>"$case_dir/typecheck.values"
      profile_ms "$log" 'typeclass inference' >>"$case_dir/typeclass.values"
      profile_ms "$log" 'tactic execution' >>"$case_dir/tactic.values"
      compile_ms "$log" >>"$case_dir/compile.values"
    done
  }

  run_measurements "$requested_runs"
  local used_runs=$requested_runs
  local wall_mad user_mad noisy=0
  wall_mad=$(mad_pct "$case_dir/wall.values")
  user_mad=$(mad_pct "$case_dir/user.values")
  if awk -v w="$wall_mad" -v u="$user_mad" 'BEGIN { exit !(w > 8 || u > 8) }'; then
    echo "preo-bench: $name MAD exceeded 8%; retrying with 9 runs" >&2
    run_measurements 9
    used_runs=9
    wall_mad=$(mad_pct "$case_dir/wall.values")
    user_mad=$(mad_pct "$case_dir/user.values")
    if awk -v w="$wall_mad" -v u="$user_mad" 'BEGIN { exit !(w > 8 || u > 8) }'; then
      noisy=1
      echo "preo-bench: $name remains infrastructure-noisy" >&2
    fi
  fi

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s' \
    "$name" "$group" "$items" "$used_runs" "$warmups" "$noisy" "$wall_mad"
  local metric
  for metric in "${metrics[@]}"; do
    printf '\t%s' "$(median "$case_dir/$metric.values")"
  done
  printf '\n'
}

profile_root() {
  local root=${1:-$repo_root}
  make_tmp
  prepare_root "$root"
  printf 'case\tgroup\titems\truns\twarmups\tnoisy\twall_mad_pct\twall_s\tuser_s\tsys_s\trss_bytes\timport_ms\tinterpretation_ms\telaboration_ms\ttypecheck_ms\ttypeclass_ms\ttactic_ms\tcompile_ms\n'
  local spec name source group items
  local saw_noisy=0
  for spec in "${cases[@]}"; do
    IFS='|' read -r name source group items <<<"$spec"
    if [[ -n $case_filter && $name != "$case_filter" ]]; then
      continue
    fi
    local row
    row=$(measure_case "$root" "$name" "$source" "$group" "$items" "$runs")
    printf '%s\n' "$row"
    if [[ $(cut -f6 <<<"$row") == 1 ]]; then saw_noisy=1; fi
  done
  if (( saw_noisy )); then
    echo "preo-bench: one or more cases remain infrastructure-noisy" >&2
    return 3
  fi
}

baseline_profile() {
  local commit=${1:-ab4c767}
  make_tmp
  local worktree="$tmp_dir/baseline-worktree"
  worktree_path=$worktree
  git -C "$repo_root" worktree add --detach "$worktree" "$commit" >&2
  # The benchmark corpus is intentionally not part of the historical commit.
  # Copy only new benchmark inputs; production sources remain exactly COMMIT.
  mkdir -p -- "$worktree/tests"
  cp -R -- "$repo_root/tests/preo-bench" "$worktree/tests/preo-bench"
  local status=0
  profile_root "$worktree" || status=$?
  git -C "$repo_root" worktree remove --force "$worktree" >&2
  worktree_path=''
  return "$status"
}

compare_profiles() {
  local baseline=$1 current=$2
  [[ -f $baseline ]] || { echo "preo-bench: missing baseline: $baseline" >&2; exit 2; }
  [[ -f $current ]] || { echo "preo-bench: missing current profile: $current" >&2; exit 2; }
  awk -F '\t' '
    BEGIN {
      OFS = "\t"
      print "case", "metric", "baseline", "current", "delta", "percent", "status"
    }
    FNR == 1 { next }
    NR == FNR {
      for (i = 1; i <= NF; i++) base[$1, i] = $i
      known[$1] = 1
      next
    }
    {
      name = $1
      if (!known[name]) {
        print name, "case", "", "", "", "", "FAIL_MISSING_BASELINE"
        failed = 1
        next
      }
      # Rollback is a negative path with a deliberately looser work threshold.
      if (name == "rollback_negative") {
        check(name, "wall_s", base[name,8], $8, 15, .050, 25, .100)
        check(name, "user_s", base[name,9], $9, 15, .050, 25, .100)
        check(name, "elaboration_ms", base[name,14], $14, 15, 50, 25, 100)
      } else {
        # wall: warn +12%/+250ms, fail +20%/+500ms.
        check(name, "wall_s", base[name,8], $8, 12, .250, 20, .500)
        check(name, "user_s", base[name,9], $9, 10, .050, 20, .100)
        check(name, "elaboration_ms", base[name,14], $14, 10, 50, 20, 100)
      }
      # Other cumulative phases share the +10/+50 warn, +20/+100 fail gate.
      check(name, "import_ms", base[name,12], $12, 10, 50, 20, 100)
      check(name, "interpretation_ms", base[name,13], $13, 10, 50, 20, 100)
      check(name, "typecheck_ms", base[name,15], $15, 10, 50, 20, 100)
      check(name, "typeclass_ms", base[name,16], $16, 10, 50, 20, 100)
      check(name, "tactic_ms", base[name,17], $17, 10, 50, 20, 100)
      check(name, "compile_ms", base[name,18], $18, 10, 50, 20, 100)
      check(name, "rss_bytes", base[name,11], $11, 5, 67108864, 10, 134217728)
      if ($6 == 1) {
        print name, "noise", "0", "1", "1", "", "NOISY"
        noisy = 1
      }
      if (name == "typed_0") {
        typed0_user = $9; typed0_elab = $14; typed0_rss = $11
      } else if (name == "typed_4") {
        typed4_user = $9; typed4_elab = $14; typed4_rss = $11
      } else if (name == "typed_16") {
        typed16_user = $9; typed16_elab = $14; typed16_rss = $11
      }
    }
    END {
      if (typed0_user != "" && typed4_user != "" && typed16_user != "") {
        scaling("typed_16", "incremental_user_s_per_item",
          (typed4_user - typed0_user) / 4,
          (typed16_user - typed0_user) / 16, .010)
        scaling("typed_16", "incremental_elaboration_ms_per_item",
          (typed4_elab - typed0_elab) / 4,
          (typed16_elab - typed0_elab) / 16, 10)
        rss4 = (typed4_rss - typed0_rss) / 4
        rss16 = (typed16_rss - typed0_rss) / 16
        rssDelta = rss16 - rss4
        status = rss16 > 4194304 ? "FAIL_SCALE" : "PASS"
        if (status == "FAIL_SCALE") failed = 1
        print "typed_16", "incremental_rss_bytes_per_item", rss4,
          rss16, rssDelta, percent(rss4, rss16), status
      }
      if (failed) exit 1
      if (noisy) exit 3
    }
    function percent(old, new) {
      if (old == 0) return (new == 0 ? 0 : 999999)
      return 100 * (new - old) / old
    }
    function check(name, metric, old, new, wp, wa, fp, fa, p, d, status) {
      d = new - old; p = percent(old, new); status = "PASS"
      if (p > fp && d > fa) { status = "FAIL"; failed = 1 }
      else if (p > wp && d > wa) status = "WARN"
      print name, metric, old, new, d, p, status
    }
    function scaling(name, metric, old, new, absolute, p, d, status) {
      d = new - old; p = percent(old, new)
      status = (p > 25 && d > absolute) ? "FAIL_SCALE" : "PASS"
      if (status == "FAIL_SCALE") failed = 1
      print name, metric, old, new, d, p, status
    }
  ' "$baseline" "$current"
}

mode=${1:-}
case "$mode" in
  -h|--help|'') usage; [[ -n $mode ]] || exit 2 ;;
  golden) golden_check ;;
  record-goldens)
    [[ $# == 2 ]] || { usage >&2; exit 2; }
    prepare_root "$repo_root"
    capture_goldens "$repo_root" "$2"
    ;;
  profile) profile_root "${2:-$repo_root}" ;;
  baseline) baseline_profile "${2:-ab4c767}" ;;
  compare)
    [[ $# == 3 ]] || { usage >&2; exit 2; }
    compare_profiles "$2" "$3"
    ;;
  all)
    make_tmp
    golden_check
    current="$tmp_dir/current.tsv"
    profile_root "$repo_root" >"$current"
    echo "preo-bench: current profile: $current" >&2
    compare_profiles "$baseline_file" "$current"
    ;;
  *) usage >&2; exit 2 ;;
esac
