#!/usr/bin/env bash

set -euo pipefail

cases=(
  "benchmark/Audit/SP1/A9_program_zero_row_receive.cz"
  "benchmark/Audit/SP1/A10_memory_access_slice_overflow.cz"
  "benchmark/Audit/SP1/A11_unaligned_memory_access.cz"
  "benchmark/Audit/SP1/A12_reduced_modulus_result_range.cz"
)

for case_path in "${cases[@]}"; do
  echo "==> $case_path"
  cargo run --quiet -- "$case_path" --solver z3_nia || true
  echo
done

echo "==> A8_frifold_state_closure"
echo "SKIP: current CZ DSL lacks next-row / transition primitives, so A8 is not faithfully expressible today."
echo

echo "==> A7_multibuilder_stacked_rows"
echo "SKIP: current CZ DSL lacks stacked-table first/last-row semantics, so A7 is not faithfully expressible today."
