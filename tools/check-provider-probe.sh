#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
PIN=miri-exporter-8144389c895d
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/$PIN/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

cargo +"$PIN" build --locked --manifest-path "$ROOT/exporter/Cargo.toml" \
  --bin lean-rustc-provider-probe
python3 "$ROOT/tools/measure-provider-probe.py" \
  "$ROOT/exporter/target/debug/lean-rustc-provider-probe" \
  "$ELAN_HOME/bin/lean" "$ROOT/tests/provider/Probe.lean" \
  "$ROOT/tests/provider/fixture.rs" "$@"
