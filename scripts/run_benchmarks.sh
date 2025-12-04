#!/usr/bin/env bash
set -euo pipefail

# Run selected Component benchmarks with explicit (path, solver) tuples.
# Add entries to the CASES array to extend coverage.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$ROOT/target/debug/certzero"
RESULTS="$ROOT/benchmark_results.txt"

CASES=(
  "benchmark/Component/Add/add.cz z3_nia"
  "benchmark/Component/Add4/add4.cz z3_nia"
  "benchmark/Component/And/and.cz z3_nia"
  "benchmark/Component/IsEqualWordOperation/is_equal.cz cvc5_ff"
  "benchmark/Component/IsZeroOperation/is_zero.cz cvc5_ff"
  "benchmark/Component/IsZeroWordOperation/is_zero_word.cz cvc5_ff"
)

echo "[bench] building..."
cargo build --quiet --manifest-path "$ROOT/Cargo.toml"

echo "path,solver,status,time_ms" >"$RESULTS"

for entry in "${CASES[@]}"; do
  read -r rel solver <<<"$entry"
  if [[ ! -f "$ROOT/$rel" ]]; then
    echo "[bench] skip missing $rel"
    continue
  fi

  start_ns=$(date +%s%N)
  if output=$("$BIN" --solver "$solver" "$rel" 2>&1); then
    status="ok"
  else
    status="fail"
  fi
  end_ns=$(date +%s%N)
  elapsed_ms=$(( (end_ns - start_ns) / 1000000 ))

  echo "$rel,$solver,$status,${elapsed_ms}" >>"$RESULTS"

  echo "[bench] $rel ($solver) -> $status in ${elapsed_ms}ms"
  if [[ "$status" != "ok" ]]; then
    echo "$output" | sed 's/^/[bench]   /'
  fi
done

echo "[bench] results written to $RESULTS"
