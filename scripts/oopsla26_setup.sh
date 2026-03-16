#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
source "$SCRIPT_DIR/oopsla26_common.sh"

ensure_results_dir
require_command cargo
require_command rustc
require_command z3
require_command cvc5
ensure_binary

ENV_REPORT="$RESULTS_DIR/environment.txt"
ENV_REPORT_REL=$(repo_relpath "$ENV_REPORT")
BIN_REL=$(repo_relpath "$BIN")

{
  echo "OOPSLA 2026 Evaluation Environment"
  echo
  echo "Paper target:"
  echo "  OS:    $PAPER_OS"
  echo "  CPU:   $PAPER_CPU"
  echo "  RAM:   $PAPER_RAM"
  echo "  Rust:  $PAPER_RUST"
  echo "  Z3:    $PAPER_Z3"
  echo "  cvc5:  $PAPER_CVC5"
  echo
  echo "Current machine:"
  echo "  OS:    $(current_os)"
  echo "  CPU:   $(current_cpu)"
  echo "  RAM:   $(current_ram)"
  echo "  Cargo: $(cargo --version)"
  echo "  Rust:  $(rustc --version)"
  echo "  Z3:    $(z3 --version | head -n 1)"
  echo "  cvc5:  $(cvc5 --version | head -n 1)"
  echo
  echo "Binary:"
  echo "  path:  $BIN_REL"
  echo "  git:   $(git -C "$ROOT_DIR" rev-parse --short HEAD)"
  echo "  date:  $(date -Iseconds)"
} >"$ENV_REPORT"

cat "$ENV_REPORT"
echo
echo "[ok] environment report written to $ENV_REPORT_REL"
