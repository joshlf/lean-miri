#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="$PWD/.elan"
mkdir -p scratch/closure-mir-check
bash tools/build-exporter.sh
bash tools/export-mir.sh --output scratch/closure-mir-check/source.json --foundation \
  --root 'std::rt::lang_start::{closure#0}' -- exporter/fixtures/foundation_closure.rs --crate-name=foundation_closure
bash tools/export-mir.sh --output scratch/closure-mir-check/reference.json --root main \
  -- exporter/fixtures/foundation_closure.rs --crate-name=foundation_closure
flock /tmp/lean-miri-lake-build.lock bash -c '
  .elan/bin/lake build Miri.Frontend.FoundationClosureMIR
  .elan/bin/lake env lean --run tests/foundation/FoundationClosureMIR.lean \
    scratch/closure-mir-check/source.json scratch/closure-mir-check/reference.json
'
