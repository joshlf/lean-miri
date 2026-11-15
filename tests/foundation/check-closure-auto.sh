#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
TASK_DIR="$(mktemp -d "$ROOT/scratch/closure-auto.XXXXXX")"
printf 'fn main() {}\n' > "$TASK_DIR/main.rs"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationClosureAuto
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation --root main --root std::rt::lang_start --root 'std::rt::lang_start::{closure#0}' -- "$TASK_DIR/main.rs" --crate-name closure_auto
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationClosureAuto.lean "$TASK_DIR/source.json"
python3 tests/exporter/test_foundation_closure_auto.py
echo "fresh closure auto source evidence: $TASK_DIR"
