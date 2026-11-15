#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export ELAN_HOME="$PWD/.elan"
mkdir -p scratch/source-compiler-bodies
bash tools/build-exporter.sh
bash tools/export-mir.sh --foundation --output scratch/source-compiler-bodies/source.json \
  --root chain --root middle --root identity -- \
  "$PWD/exporter/fixtures/foundation_call_graph.rs" --crate-type=lib --crate-name=source_compiler_bodies
flock /tmp/lean-miri-lake-build.lock bash -c '
  .elan/bin/lake build Miri.Input.SourceCompilerBodies Miri.Input.CompilerCallPipeline Miri.Frontend.FoundationCallGraphProgram
  .elan/bin/lake env lean --run tests/input/SourceCompilerBodies.lean scratch/source-compiler-bodies/source.json
'
