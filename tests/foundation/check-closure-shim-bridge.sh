#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/closure-shim-bridge.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationClosureShimBridge
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation \
  --root 'use_closure::{closure#0}' -- exporter/fixtures/foundation_closure_shims.rs --crate-name closure_shims
bash tools/export-mir.sh --output "$TASK_DIR/reference.json" --root use_closure -- \
  exporter/fixtures/foundation_closure_shims.rs --crate-name closure_shims
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationClosureShimBridge.lean "$TASK_DIR/source.json" "$TASK_DIR/reference.json"
