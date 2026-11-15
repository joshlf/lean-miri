#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${1:-$ROOT/scratch/rustc-boundary}"
mkdir -p "$OUT"
if [[ -n "${EXPORTER_BIN:-}" ]]; then
  source exporter/tests/fixture-env.sh
  export_document() { "$EXPORTER_BIN" "$@"; }
else
  export_document() { bash tools/export-mir.sh "$@"; }
fi
export_document --output "$OUT/fnptr.json" --root roundtrip -- \
  tests/compiler_queries/fn-pointer-shims.rs --crate-type=lib \
  --crate-name=fnptr_shim_boundary -Zmir-opt-level=0
export_document --output "$OUT/constants.json" --root miri_start -- \
  tests/compiler_queries/concrete-constants.rs --crate-name=concrete_constants \
  --edition=2024 -Cpanic=abort -Zmir-opt-level=0
export_document --output "$OUT/guest.json" --root miri_start -- \
  tests/compiler_queries/material-guest.rs --crate-name=material_guest \
  --edition=2024 -Cpanic=abort -Zmir-opt-level=0 --cfg=miri
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.CompilerInstanceAbi Miri.Input.CompilerMirConstants
python3 tools/check-rustc-constant-boundary.py "$OUT/constants.json"
lake env lean --run tests/compiler_queries/ConcreteConstBoundary.lean
lake env lean --run tests/compiler_queries/RawInstanceCallEvidence.lean
lake env lean --run tests/compiler_queries/StrictSourceWire.lean "$OUT/constants.json"
lake env lean --run tests/compiler_queries/RustcExactBoundary.lean "$OUT/fnptr.json" "$OUT/guest.json"
lake env lean --run tests/compiler_queries/RustcProjectionFamily.lean "$OUT/guest.json"
lake env lean --run tests/compiler_queries/FnPointerShimProduction.lean "$OUT/fnptr.json"
