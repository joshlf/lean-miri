#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
bash tools/export-mir.sh --output scratch/foundation-std-source-closure.json --foundation \
  --root main --root std::rt::lang_start --root 'std::rt::lang_start::{closure#0}' \
  --root std::rt::lang_start_internal -- tests/foundation/fixtures/std-main.rs --crate-name=foundation_std_main
ELAN_HOME="$ROOT/.elan" flock /tmp/lean-miri-lake-build.lock .elan/bin/lake build \
  Miri.Frontend.FoundationStdSource Miri.Frontend.FoundationBodyCore
ELAN_HOME="$ROOT/.elan" .elan/bin/lake env lean --run tests/foundation/FoundationStdSource.lean \
  scratch/foundation-std-source-closure.json
