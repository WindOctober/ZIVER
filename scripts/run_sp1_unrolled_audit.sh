#!/usr/bin/env bash

set -euo pipefail

cases=(
  "benchmark/Audit/SP1/Unrolled/A2_next_pc_underconstrained_on_ecall_unrolled.cz"
  "benchmark/Audit/SP1/Unrolled/A5_read_only_selector_incomplete_unrolled.cz"
  "benchmark/Audit/SP1/Unrolled/K4_load_value_not_bound_unrolled.cz"
  "benchmark/Audit/SP1/Unrolled/K6_bneinc_upper_limbs_unrolled.cz"
  "benchmark/Audit/SP1/Unrolled/A10_memory_access_slice_overflow_unrolled.cz"
  "benchmark/Audit/SP1/Unrolled/H01_missing_limb_recomposition_unrolled.cz"
)

for case_path in "${cases[@]}"; do
  echo "==> $case_path"
  cargo run --quiet -- "$case_path" --solver z3_nia || true
  echo
done
