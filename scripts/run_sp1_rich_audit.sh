#!/usr/bin/env bash

set -euo pipefail

cases=(
  "benchmark/Audit/SP1/Rich/A2_next_pc_underconstrained_on_ecall_rich.cz"
  "benchmark/Audit/SP1/Rich/A3_send_to_table_padding_rich.cz"
  "benchmark/Audit/SP1/Rich/A4_padding_selector_leaks_lookup_rich.cz"
  "benchmark/Audit/SP1/Rich/A5_read_only_selector_incomplete_rich.cz"
  "benchmark/Audit/SP1/Rich/A9_program_zero_row_receive_rich.cz"
  "benchmark/Audit/SP1/Rich/A10_memory_access_slice_overflow_rich.cz"
  "benchmark/Audit/SP1/Rich/A11_unaligned_memory_access_rich.cz"
  "benchmark/Audit/SP1/Rich/A12_reduced_modulus_result_range_rich.cz"
  "benchmark/Audit/SP1/Rich/C312_syscall_arg_overflow_rich.cz"
  "benchmark/Audit/SP1/Rich/H01_missing_limb_recomposition_rich.cz"
  "benchmark/Audit/SP1/Rich/K2_recursion_is_real_not_boolean_rich.cz"
  "benchmark/Audit/SP1/Rich/K4_load_value_not_bound_rich.cz"
  "benchmark/Audit/SP1/Rich/K5_jump_opcode_underconstrained_rich.cz"
  "benchmark/Audit/SP1/Rich/K6_bneinc_upper_limbs_rich.cz"
  "benchmark/Audit/SP1/Rich/RKM11_exp_reverse_bits_boundary_rich.cz"
  "benchmark/Audit/SP1/Rich/V002_sponge_state_not_zero_rich.cz"
)

for case_path in "${cases[@]}"; do
  echo "==> $case_path"
  cargo run --quiet -- "$case_path" --solver z3_nia || true
  echo
done
