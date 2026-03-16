#!/usr/bin/env bash

set -euo pipefail

cases=(
  "benchmark/Audit/SP1/RKM11_exp_reverse_bits_boundary.cz"
  "benchmark/Audit/SP1/K2_recursion_is_real_not_boolean.cz"
  "benchmark/Audit/SP1/K4_load_value_not_bound.cz"
  "benchmark/Audit/SP1/K5_jump_opcode_underconstrained.cz"
  "benchmark/Audit/SP1/K6_bneinc_upper_limbs.cz"
  "benchmark/Audit/SP1/C312_syscall_arg_overflow.cz"
  "benchmark/Audit/SP1/H01_missing_limb_recomposition.cz"
  "benchmark/Audit/SP1/V002_sponge_state_not_zero.cz"
)

for case_path in "${cases[@]}"; do
  echo "==> $case_path"
  cargo run --quiet -- "$case_path" --solver z3_nia || true
  echo
done

echo "==> kalos_8_division_0_over_0"
echo "SKIP: current checker needs a committed semantic output to compare, but the audit explicitly treats 0/0 as semantically arbitrary rather than a concrete compute-vs-constraint mismatch."
echo

echo "==> cantina_3_1_4_uint256_mul_alias"
echo "SKIP: this is an overconstraint / false-negative issue (valid aliasing execution rejected), while current component equivalence is oriented around underconstraint and trace divergence, not proving rejection of a valid trace."
echo

echo "==> veridise_vul_007_poseidon_not_reduced"
echo "SKIP: the audit describes an intentional non-reduced API contract / documentation issue, not a stable local equivalence bug with a single faithful canonical output."
