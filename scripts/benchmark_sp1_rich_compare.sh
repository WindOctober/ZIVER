#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
BIN="$ROOT_DIR/target/debug/certzero"
ITERATIONS="${1:-100}"
OUTPUT_PATH="${2:-/tmp/sp1_rich_compare.tsv}"

if [[ ! -x "$BIN" ]]; then
  echo "missing binary: $BIN" >&2
  echo "run 'cargo build' in $ROOT_DIR first" >&2
  exit 1
fi

cases=(
  "A2|benchmark/Audit/SP1/A2_next_pc_underconstrained_on_ecall.cz|benchmark/Audit/SP1/Rich/A2_next_pc_underconstrained_on_ecall_rich.cz"
  "A3|benchmark/Audit/SP1/A3_send_to_table_padding.cz|benchmark/Audit/SP1/Rich/A3_send_to_table_padding_rich.cz"
  "A4|benchmark/Audit/SP1/A4_padding_selector_leaks_lookup.cz|benchmark/Audit/SP1/Rich/A4_padding_selector_leaks_lookup_rich.cz"
  "A5|benchmark/Audit/SP1/A5_read_only_selector_incomplete.cz|benchmark/Audit/SP1/Rich/A5_read_only_selector_incomplete_rich.cz"
  "A9|benchmark/Audit/SP1/A9_program_zero_row_receive.cz|benchmark/Audit/SP1/Rich/A9_program_zero_row_receive_rich.cz"
  "A10|benchmark/Audit/SP1/A10_memory_access_slice_overflow.cz|benchmark/Audit/SP1/Rich/A10_memory_access_slice_overflow_rich.cz"
  "A11|benchmark/Audit/SP1/A11_unaligned_memory_access.cz|benchmark/Audit/SP1/Rich/A11_unaligned_memory_access_rich.cz"
  "A12|benchmark/Audit/SP1/A12_reduced_modulus_result_range.cz|benchmark/Audit/SP1/Rich/A12_reduced_modulus_result_range_rich.cz"
  "C312|benchmark/Audit/SP1/C312_syscall_arg_overflow.cz|benchmark/Audit/SP1/Rich/C312_syscall_arg_overflow_rich.cz"
  "H01|benchmark/Audit/SP1/H01_missing_limb_recomposition.cz|benchmark/Audit/SP1/Rich/H01_missing_limb_recomposition_rich.cz"
  "K2|benchmark/Audit/SP1/K2_recursion_is_real_not_boolean.cz|benchmark/Audit/SP1/Rich/K2_recursion_is_real_not_boolean_rich.cz"
  "K4|benchmark/Audit/SP1/K4_load_value_not_bound.cz|benchmark/Audit/SP1/Rich/K4_load_value_not_bound_rich.cz"
  "K5|benchmark/Audit/SP1/K5_jump_opcode_underconstrained.cz|benchmark/Audit/SP1/Rich/K5_jump_opcode_underconstrained_rich.cz"
  "K6|benchmark/Audit/SP1/K6_bneinc_upper_limbs.cz|benchmark/Audit/SP1/Rich/K6_bneinc_upper_limbs_rich.cz"
  "RKM11|benchmark/Audit/SP1/RKM11_exp_reverse_bits_boundary.cz|benchmark/Audit/SP1/Rich/RKM11_exp_reverse_bits_boundary_rich.cz"
  "V002|benchmark/Audit/SP1/V002_sponge_state_not_zero.cz|benchmark/Audit/SP1/Rich/V002_sponge_state_not_zero_rich.cz"
)

measure_case() {
  local case_path="$1"
  local start_ns end_ns status avg_ms

  start_ns=$(date +%s%N)
  for ((i = 0; i < ITERATIONS; i++)); do
    "$BIN" "$case_path" --solver z3_nia >/tmp/sp1_rich_case.out 2>/tmp/sp1_rich_case.err || true
  done
  end_ns=$(date +%s%N)

  avg_ms=$(awk -v ns="$((end_ns - start_ns))" -v it="$ITERATIONS" 'BEGIN { printf "%.3f", ns / 1000000 / it }')
  status=$(grep -E "Equivalence check failed|memory trace length mismatch|Equivalence check passed" /tmp/sp1_rich_case.err /tmp/sp1_rich_case.out | tail -n 1 | sed 's#^/tmp/sp1_rich_case\\.[a-z]*:##')

  printf "%s\t%s\n" "$avg_ms" "$status"
}

printf "label\tminimal_case\trich_case\tminimal_avg_ms\tminimal_status\trich_avg_ms\trich_status\n" > "$OUTPUT_PATH"

for entry in "${cases[@]}"; do
  IFS='|' read -r label minimal_case rich_case <<< "$entry"
  read -r minimal_avg_ms minimal_status < <(measure_case "$minimal_case")
  read -r rich_avg_ms rich_status < <(measure_case "$rich_case")
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" \
    "$label" "$minimal_case" "$rich_case" \
    "$minimal_avg_ms" "$minimal_status" \
    "$rich_avg_ms" "$rich_status" | tee -a "$OUTPUT_PATH"
done

echo "wrote $OUTPUT_PATH"
