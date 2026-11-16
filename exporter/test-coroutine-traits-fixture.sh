#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/exporter/tests/fixture-env.sh"
EXPORTER="${EXPORTER_BIN:-$ROOT/exporter/target/debug/lean-miri-mir-exporter}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-coroutine-traits-XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=0 LEAN_MIRI_RUN_PREPARED_MIRI=0 "$EXPORTER" \
  --output "$WORK/input.json" --oracle-output "$WORK/oracle.json" --root root -- \
  "$ROOT/exporter/fixtures/fail_closed/coroutine_traits.rs" \
  --crate-type=lib --crate-name=coroutine_traits --edition=2024
python3 - "$WORK/input.json" "$WORK/oracle.json" <<'PY'
import json, sys
source, oracle = (json.load(open(path)) for path in sys.argv[1:])
expected = {
    'saved_cell::{closure#0}': (False, False, 'static'),
    'saved_scalar::{closure#0}': (True, False, 'static'),
    'captured_cell::{closure#0}': (False, False, 'static'),
    'movable::{closure#0}': (True, True, 'movable'),
}
booleans = {row['type_id']: row['booleans'] for row in oracle['types']}
coroutines = {row['shape']['def_path']: row for row in source['types']
              if row['source_layout']['coroutine'] is not None}
assert set(coroutines) == set(expected)
for name, (freeze, unpin, movability) in expected.items():
    node = coroutines[name]
    actual = booleans[node['type_id']]
    assert (actual['is_freeze'], actual['is_unpin'], actual['needs_drop']) == (freeze, unpin, True), name
    assert node['source_layout']['coroutine']['movability'] == movability
assert coroutines['saved_cell::{closure#0}']['source_layout']['coroutine']['prefix'] == []
assert coroutines['captured_cell::{closure#0}']['source_layout']['coroutine']['prefix']
print('compiler controls: saved/captured UnsafeCell, scalar witness and movable PhantomPinned')
PY
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
cd "$ROOT"
"$ROOT/.elan/bin/lake" env lean --run tools/CheckSourceTypeQueries.lean "$WORK/input.json" "$WORK/oracle.json"
"$ROOT/.elan/bin/lake" env lean --run tools/CheckSourceLayouts.lean "$WORK/input.json" "$WORK/oracle.json"
