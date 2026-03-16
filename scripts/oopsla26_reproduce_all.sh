#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)

"$SCRIPT_DIR/oopsla26_setup.sh"
echo
"$SCRIPT_DIR/oopsla26_exp1.sh" "$@"
echo
"$SCRIPT_DIR/oopsla26_exp2.sh" "$@"
