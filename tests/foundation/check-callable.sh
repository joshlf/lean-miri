#!/usr/bin/env bash
# Fresh generic closure source and independent compiler-selected callable shims.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/callable.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationCallable
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation \
  --root 'std::rt::lang_start::{closure#0}' -- tests/repro/startup/empty-main.rs --crate-name callable_std
bash tools/export-mir.sh --output "$TASK_DIR/compiler-full.json" --root main -- \
  tests/repro/startup/empty-main.rs --crate-name callable_std
python3 tests/foundation/project_callable_oracle.py "$TASK_DIR/compiler-full.json" "$TASK_DIR/compiler.json"
bash tools/export-mir.sh --output "$TASK_DIR/fnptr.json" --root concrete_vtable -- \
  exporter/fixtures/foundation_fn_vtable.rs --crate-name callable_fnptr
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationCallable.lean "$TASK_DIR/source.json" "$TASK_DIR/compiler.json" "$TASK_DIR/fnptr.json"
