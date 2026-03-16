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
Usage: ./scripts/oopsla26_exp1.sh [--iterations N]

Runs Table 1 from the OOPSLA 2026 paper against the local ZIVER checkout.
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
require_command cvc5
require_command z3
ensure_binary

MANIFEST="$MANIFEST_DIR/exp1_components.tsv"
OUT_TSV="$RESULTS_DIR/exp1_components.tsv"
OUT_TSV_REL=$(repo_relpath "$OUT_TSV")

printf "component\tpattern\tsolver\tpaper_result\tpaper_time_s\tcurrent_cli\tcurrent_time_s\ttime_delta_s\ttime_match\tpaper_match\tcase\n" >"$OUT_TSV"

while IFS=$'\t' read -r component pattern solver paper_time_s paper_result case_key rel_path; do
  if [[ "$component" == "component" ]]; then
    continue
  fi

  IFS=$'\t' read -r cli_status reason avg_s < <(run_case_average "$rel_path" "$solver" "$ITERATIONS" "-")

  if [[ "$paper_result" == "✓" ]]; then
    expected_cli="PASS"
  else
    expected_cli="FAIL"
  fi

  if [[ "$cli_status" == "$expected_cli" ]]; then
    paper_match="yes"
  else
    paper_match="no"
  fi

  delta_s=$(time_delta_s "$avg_s" "$paper_time_s")
  time_match=$(time_match_3dp "$avg_s" "$paper_time_s")

  printf "%s\t%s\t%s\t%s\t%s\t%s (%s)\t%s\t%s\t%s\t%s\t%s\n" \
    "$component" "$pattern" "$solver" "$paper_result" "$paper_time_s" \
    "$cli_status" "$reason" "$avg_s" "$delta_s" "$time_match" "$paper_match" "$case_key" >>"$OUT_TSV"
done <"$MANIFEST"

echo "Experiment 1: Table 1 component benchmarks"
echo "Average over $ITERATIONS run(s) per case"
echo
pretty_print_tsv "$OUT_TSV"
echo
echo "[ok] results written to $OUT_TSV_REL"
