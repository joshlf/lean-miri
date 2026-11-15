#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
TASK_DIR="$(mktemp -d "$ROOT/scratch/existential.XXXXXX")"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationExistentialRegistry Miri.Frontend.FoundationObligations
for root in dynamic_input generic_dynamic_input; do
  bash tools/export-mir.sh --output "$TASK_DIR/$root.json" --foundation --root "$root" -- exporter/fixtures/foundation_dynamic.rs --crate-type=lib --crate-name foundation_dynamic
 done
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationExistential.lean "$TASK_DIR/dynamic_input.json" "$TASK_DIR/generic_dynamic_input.json"
echo "fresh existential source evidence: $TASK_DIR"
