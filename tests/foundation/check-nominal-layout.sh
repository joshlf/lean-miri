#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
bash tools/build-exporter.sh
RUN="$ROOT/scratch/foundation-nominal-layout-$(date -u +%Y%m%dT%H%M%S.%N)"
mkdir -p "$RUN"
for mode in source reference; do
  extra=()
  if [[ "$mode" == source ]]; then extra=(--foundation); fi
  bash tools/export-mir.sh --output "$RUN/$mode.json" "${extra[@]}" --root result_layout -- \
    tests/foundation/fixtures/nominal-layout.rs --crate-type=lib --crate-name=nominal_layout
done
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationNominalLayout
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationNominalLayout.lean "$RUN/source.json" "$RUN/reference.json"
