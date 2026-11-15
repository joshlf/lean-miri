#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="$PWD/.elan"
mkdir -p scratch/closure-physical-check
bash tools/build-exporter.sh
bash tools/export-mir.sh --output scratch/closure-physical-check/source.json --foundation \
  --root 'std::rt::lang_start::{closure#0}' -- exporter/fixtures/foundation_closure.rs --crate-name=foundation_closure
bash tools/export-mir.sh --output scratch/closure-physical-check/reference.json --root main \
  -- exporter/fixtures/foundation_closure.rs --crate-name=foundation_closure
flock /tmp/lean-miri-lake-build.lock .elan/bin/lake build Miri.Frontend.FoundationClosurePhysical
.elan/bin/lake env lean --run tests/foundation/FoundationClosurePhysical.lean \
  scratch/closure-physical-check/source.json scratch/closure-physical-check/reference.json
