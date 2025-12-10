#!/usr/bin/env bash
set -euo pipefail

# Run selected Component benchmarks with explicit (path, solver) tuples.
# Add entries to the CASES array to extend coverage.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/target/debug/certzero"
RESULTS="$ROOT/benchmark_results.txt"

CASES=(
  "Component/SP1/Add/add.cz z3_nia"
  "Component/SP1/Add4/add4.cz z3_nia"
  "Component/SP1/And/and.cz z3_nia"
  "Component/SP1/IsEqualWordOperation/is_equal.cz cvc5_ff"
  "Component/SP1/IsZeroOperation/is_zero.cz cvc5_ff"
  "Component/SP1/IsZeroWordOperation/is_zero_word.cz cvc5_ff"
  "Component/SP1/MapRead/map_read.cz z3_nia"
  "Component/Ziren/Or/or.cz z3_nia"
  "Component/Ziren/Xor/xor.cz z3_nia"
  "Component/Ziren/IsZeroOperation/is_zero.cz cvc5_ff"
  "Component/Ziren/IsZeroWordOperation/is_zero_word.cz cvc5_ff"
  "Component/Ziren/IsEqualWordOperation/is_equal.cz cvc5_ff"
  "Component/Ziren/KoalaBearRange/koala_bear_range.cz z3_nia"
  "Component/Ziren/KoalaBearWord/koala_bear_word.cz z3_nia"
  "Component/Ziren/FixedShiftRight/fixed_shift_right.cz z3_nia"
  "Component/Ziren/FixedRotateRight/fixed_rotate_right.cz z3_nia"
  "Component/Ziren/AddDouble/adddouble.cz z3_nia"
  "Component/Ziren/Cmp/gt_bytes.cz z3_nia"
  "Component/Ziren/Cmp/assert_lt_bytes.cz z3_nia"
  "Component/Ziren/Cmp/assert_lt_bits8.cz z3_nia"
)

echo "[bench] building..."
cargo build --quiet --manifest-path "$ROOT/Cargo.toml"

echo "path,solver,status,time_ms" >"$RESULTS"

for entry in "${CASES[@]}"; do
  read -r rel solver <<<"$entry"
  rel_path="benchmark/$rel"
  if [[ ! -f "$ROOT/$rel_path" ]]; then
    echo "[bench] skip missing $rel_path"
    continue
  fi

  start_ns=$(date +%s%N)
  # Explicitly run in component mode to match benchmark expectations.
  if output=$("$BIN" --mode component --solver "$solver" "$rel_path" 2>&1); then
    status="ok"
  else
    status="fail"
  fi
  end_ns=$(date +%s%N)
  elapsed_ms=$(( (end_ns - start_ns) / 1000000 ))

  echo "$rel_path,$solver,$status,${elapsed_ms}" >>"$RESULTS"

  echo "[bench] $rel_path ($solver) -> $status in ${elapsed_ms}ms"
  if [[ "$status" != "ok" ]]; then
    echo "$output" | sed 's/^/[bench]   /'
  fi
done

echo "[bench] results written to $RESULTS"
