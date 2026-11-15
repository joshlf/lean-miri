#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
OUT="$(mktemp -d "$ROOT/scratch/foundation-call-graph.XXXXXX")"
SOURCE="$ROOT/exporter/fixtures/foundation_call_graph.rs"

bash tools/export-mir.sh --foundation --output "$OUT/chain-foundation.json" \
  --root chain --root middle --root identity -- \
  "$SOURCE" --crate-type=lib --crate-name foundation_call_graph
bash tools/export-mir.sh --foundation --output "$OUT/twice-foundation.json" \
  --root twice --root identity -- \
  "$SOURCE" --crate-type=lib --crate-name foundation_call_graph
bash tools/export-mir.sh --foundation --output "$OUT/recursive-foundation.json" \
  --root recursive -- "$SOURCE" --crate-type=lib --crate-name foundation_call_graph
bash tools/export-mir.sh --foundation --output "$OUT/mutual_a-foundation.json" \
  --root mutual_a --root mutual_b -- \
  "$SOURCE" --crate-type=lib --crate-name foundation_call_graph
for name in chain twice; do
  bash tools/export-mir.sh --output "$OUT/$name-schema12.json" --root "$name" -- \
    "$SOURCE" --crate-type=lib --crate-name foundation_call_graph
done

export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationCallGraphProgram Miri.Frontend.FoundationCallExecute
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationCallGraph.lean \
  "$OUT/chain-foundation.json" "$OUT/chain-schema12.json" \
  "$OUT/twice-foundation.json" "$OUT/twice-schema12.json" \
  "$OUT/recursive-foundation.json" "$OUT/mutual_a-foundation.json"
