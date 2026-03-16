#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
BIN="$ROOT_DIR/target/debug/certzero"
MANIFEST_DIR="$ROOT_DIR/evaluation/oopsla26"
RESULTS_DIR="${RESULTS_DIR:-$ROOT_DIR/results/oopsla26}"
PAPER_OS="Ubuntu 22.04.5 LTS under WSL2 (kernel 6.6.87.2)"
PAPER_CPU="AMD Ryzen 9 9950X3D (16 cores / 32 threads)"
PAPER_RAM="30 GiB RAM"
PAPER_RUST="rustc 1.93.0-nightly"
PAPER_Z3="Z3 4.15.3 (64-bit)"
PAPER_CVC5="cvc5 1.3.2 (commit 84c7e48)"

ensure_results_dir() {
  mkdir -p "$RESULTS_DIR"
}

require_command() {
  local name="$1"
  if ! command -v "$name" >/dev/null 2>&1; then
    echo "missing required command: $name" >&2
    exit 1
  fi
}

ensure_binary() {
  if [[ ! -x "$BIN" || "${OOPSLA26_REBUILD:-0}" == "1" ]]; then
    echo "[build] cargo build --quiet"
    cargo build --quiet --manifest-path "$ROOT_DIR/Cargo.toml"
  fi
}

current_os() {
  local pretty kernel
  pretty=$(awk -F= '/^PRETTY_NAME=/{gsub(/"/, "", $2); print $2}' /etc/os-release 2>/dev/null || true)
  kernel=$(uname -r)
  if [[ -n "$pretty" ]]; then
    printf "%s (kernel %s)\n" "$pretty" "$kernel"
  else
    uname -srv
  fi
}

current_cpu() {
  local model cores
  model=$(awk -F: '/model name/{gsub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo 2>/dev/null || true)
  cores=$(nproc 2>/dev/null || echo "?")
  if [[ -n "$model" ]]; then
    printf "%s (%s cores)\n" "$model" "$cores"
  else
    printf "nproc=%s\n" "$cores"
  fi
}

current_ram() {
  free -h 2>/dev/null | awk '/^Mem:/{print $2; exit}'
}

single_line() {
  tr '\n' ' ' | tr '\t' ' ' | sed 's/  */ /g; s/^ //; s/ $//'
}

extract_cli_observation() {
  local exit_code="$1"
  local combined="$2"

  if [[ "$exit_code" -eq 0 ]]; then
    printf "PASS\t%s\n" "equivalence passed"
    return 0
  fi

  if grep -q "memory trace length mismatch" <<<"$combined"; then
    printf "FAIL\t%s\n" "trace mismatch"
    return 0
  fi

  if grep -q "SMT found a model" <<<"$combined"; then
    printf "FAIL\t%s\n" "model witness"
    return 0
  fi

  if grep -q "Equivalence check failed" <<<"$combined"; then
    printf "FAIL\t%s\n" "equivalence failed"
    return 0
  fi

  printf "ERROR\t%s\n" "$(printf "%s" "$combined" | single_line | cut -c1-120)"
}

run_case_average() {
  local rel_path="$1"
  local solver="$2"
  local iterations="$3"
  local extra_arg="${4:--}"
  local total_ns=0
  local last_cli="ERROR"
  local last_reason="not run"
  local out_file err_file start_ns end_ns exit_code combined cli_status reason

  out_file=$(mktemp)
  err_file=$(mktemp)
  trap 'rm -f "$out_file" "$err_file"' RETURN

  for ((i = 1; i <= iterations; i++)); do
    : >"$out_file"
    : >"$err_file"
    start_ns=$(date +%s%N)
    if [[ "$extra_arg" == "-" ]]; then
      if "$BIN" "$rel_path" --solver "$solver" >"$out_file" 2>"$err_file"; then
        exit_code=0
      else
        exit_code=$?
      fi
    elif "$BIN" "$rel_path" --solver "$solver" "$extra_arg" >"$out_file" 2>"$err_file"; then
      exit_code=0
    else
      exit_code=$?
    fi
    end_ns=$(date +%s%N)
    total_ns=$((total_ns + end_ns - start_ns))

    combined=$(cat "$out_file" "$err_file")
    IFS=$'\t' read -r cli_status reason < <(extract_cli_observation "$exit_code" "$combined")
    last_cli="$cli_status"
    last_reason="$reason"
  done

  rm -f "$out_file" "$err_file"
  trap - RETURN

  local avg_s
  avg_s=$(awk -v ns="$total_ns" -v it="$iterations" 'BEGIN { printf "%.3f", ns / 1000000000 / it }')
  printf "%s\t%s\t%s\n" "$last_cli" "$last_reason" "$avg_s"
}

pretty_print_tsv() {
  local path="$1"
  if command -v column >/dev/null 2>&1; then
    column -t -s $'\t' "$path"
  else
    cat "$path"
  fi
}

time_delta_s() {
  local current_s="$1"
  local paper_s="$2"

  if [[ "$current_s" == "-" || "$paper_s" == "-" ]]; then
    printf -- "-\n"
    return 0
  fi

  awk -v current="$current_s" -v paper="$paper_s" 'BEGIN { printf "%+.3f", current - paper }'
}

time_match_3dp() {
  local current_s="$1"
  local paper_s="$2"

  if [[ "$current_s" == "-" || "$paper_s" == "-" ]]; then
    printf -- "-\n"
    return 0
  fi

  if [[ "$current_s" == "$paper_s" ]]; then
    printf "yes\n"
  else
    printf "no\n"
  fi
}
