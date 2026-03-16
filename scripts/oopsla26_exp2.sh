#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
source "$SCRIPT_DIR/oopsla26_common.sh"

ITERATIONS=1

while [[ $# -gt 0 ]]; do
  case "$1" in
    --iterations)
      shift
      ITERATIONS="${1:?missing value for --iterations}"
      ;;
    -h|--help)
      cat <<'EOF'
Usage: ./scripts/oopsla26_exp2.sh [--iterations N]

Runs Table 2 from the OOPSLA 2026 paper.
For supported cases, a failing equivalence check is the expected outcome because
Table 2 reports whether the bug is reproduced.
EOF
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      exit 1
      ;;
  esac
  shift
done

ensure_results_dir
require_command cargo
require_command z3
ensure_binary

MANIFEST="$MANIFEST_DIR/exp2_audits.tsv"
OUT_TSV="$RESULTS_DIR/exp2_audits.tsv"

printf "source\tid\tcat\tpaper_result\tpaper_time_s\tstatus\tcli_observation\treproduced\tcurrent_time_s\tcase_key\tfinding\n" >"$OUT_TSV"

supported_count=0
reproduced_count=0
unsupported_count=0
local_reproduced=0
cross_reproduced=0
semantic_gap_count=0

while IFS=$'\t' read -r source id category paper_result paper_time_s local_status case_key solver rel_path finding; do
  if [[ "$source" == "source" ]]; then
    continue
  fi

  if [[ "$local_status" == "supported" ]]; then
    supported_count=$((supported_count + 1))
    IFS=$'\t' read -r cli_status reason avg_s < <(run_case_average "$rel_path" "$solver" "$ITERATIONS")

    if [[ "$cli_status" == "FAIL" ]]; then
      reproduced="✓"
      reproduced_count=$((reproduced_count + 1))
      if [[ "$category" == "L" ]]; then
        local_reproduced=$((local_reproduced + 1))
      elif [[ "$category" == "X" ]]; then
        cross_reproduced=$((cross_reproduced + 1))
      fi
    else
      reproduced="✗"
    fi

    cli_observation="$cli_status ($reason)"
    status="supported"
    current_time_s="$avg_s"
  else
    unsupported_count=$((unsupported_count + 1))
    if [[ "$category" == "S" ]]; then
      semantic_gap_count=$((semantic_gap_count + 1))
    fi
    status="unsupported"
    cli_observation="SKIP (not modeled)"
    reproduced="✗"
    current_time_s="-"
  fi

  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
    "$source" "$id" "$category" "$paper_result" "$paper_time_s" "$status" \
    "$cli_observation" "$reproduced" "$current_time_s" "$case_key" "$finding" >>"$OUT_TSV"
done <"$MANIFEST"

echo "Experiment 2: Table 2 audit-driven benchmarks"
echo "Average over $ITERATIONS run(s) per supported case"
echo
pretty_print_tsv "$OUT_TSV"
echo
echo "Summary"
echo "  reproduced:      $reproduced_count / 25"
echo "  supported now:   $supported_count / 25"
echo "  unsupported now: $unsupported_count / 25"
echo "  reproduced L:    $local_reproduced"
echo "  reproduced X:    $cross_reproduced"
echo "  semantic-gap:    $semantic_gap_count"
echo
echo "[ok] results written to $OUT_TSV"
