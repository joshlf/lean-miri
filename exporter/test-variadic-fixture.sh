#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/exporter/tests/fixture-env.sh"
EXPORTER="${EXPORTER_BIN:-$ROOT/exporter/target/debug/lean-miri-mir-exporter}"
OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-variadic-XXXXXX.json")"
ORACLE="$(mktemp "${TMPDIR:-/tmp}/lean-miri-variadic-oracle-XXXXXX.json")"
ERR="$(mktemp "${TMPDIR:-/tmp}/lean-miri-variadic-XXXXXX.err")"
trap 'rm -f "$OUT" "$ERR" "$ORACLE"' EXIT

if ! LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=0 LEAN_MIRI_RUN_PREPARED_MIRI=0 "$EXPORTER" --output "$OUT" --oracle-output "$ORACLE" --root variadic_callsite \
  "$ROOT/exporter/fixtures/variadic_fnptr.rs" \
  --crate-type=lib --crate-name=variadic_fnptr \
  -Cpanic=abort --edition=2024 -Zmir-opt-level=0 \
  --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir \
  2>"$ERR"; then
  cat "$ERR" >&2
  exit 1
fi
python3 "$ROOT/exporter/tests/validate_variadic_fnptr_fixture.py" "$OUT" "$ORACLE"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
(cd "$ROOT" && "$ROOT/.elan/bin/lake" env lean --run tools/CheckSourceAbi.lean "$OUT" "$ORACLE")
