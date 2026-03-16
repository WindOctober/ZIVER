#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)

cases=(
  "benchmark/Audit/SP1/A2_next_pc_underconstrained_on_ecall.cz"
  "benchmark/Audit/SP1/A3_send_to_table_padding.cz"
  "benchmark/Audit/SP1/A4_padding_selector_leaks_lookup.cz"
  "benchmark/Audit/SP1/A5_read_only_selector_incomplete.cz"
)

for case_path in "${cases[@]}"; do
  echo "==> $case_path"
  cargo run --quiet -- "$case_path" --solver z3_nia || true
  echo
done

echo "==> benchmark/Audit/SP1/A1_is_memory_underconstrained.cz"
echo "SKIP: this issue depends on missing cross-chip interaction schema information, not a self-contained single-chip compute-vs-constraint mismatch."
echo

echo "==> benchmark/Audit/SP1/A6_missing_initial_clk_pc.cz"
echo "SKIP: current CZ DSL has no built-in first-row / initial-state primitive, so A6 is not faithfully expressible as equivalence today."
