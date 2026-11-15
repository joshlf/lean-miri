#!/usr/bin/env bash
# Fresh source declarations + independent pinned compiler-generated shim MIR/ABI.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/closure-shims.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationClosureShims
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation \
  --root 'std::rt::lang_start::{closure#0}' -- tests/repro/startup/empty-main.rs --crate-name closure_shims
bash tools/export-mir.sh --output "$TASK_DIR/compiler-full.json" --root main -- \
  tests/repro/startup/empty-main.rs --crate-name closure_shims
python3 tests/foundation/project_callable_oracle.py "$TASK_DIR/compiler-full.json" "$TASK_DIR/compiler.json"
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationClosureShims.lean "$TASK_DIR/source.json" "$TASK_DIR/compiler.json"
