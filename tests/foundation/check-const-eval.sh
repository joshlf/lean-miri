#!/usr/bin/env bash
# Fresh scalar const-item MIR source vs independently compiler-evaluated MIR.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/const-eval.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
cat > "$TASK_DIR/input.rs" <<'RS'
const VALUE: u8 = 37;
pub fn scalar() -> u8 { VALUE }
RS
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationConstOperand Miri.Frontend.FoundationConstBindings \
    Miri.Frontend.FoundationBodyCore Miri.Frontend.FoundationInstanceRegistry Miri.Frontend.FoundationFnAbiRegistry
bash tools/export-mir.sh --output "$TASK_DIR/foundation.json" --foundation --root scalar \
  -- "$TASK_DIR/input.rs" --crate-type=lib --crate-name finite_const
bash tools/export-mir.sh --output "$TASK_DIR/schema12.json" --root scalar \
  -- "$TASK_DIR/input.rs" --crate-type=lib --crate-name finite_const
python3 - "$TASK_DIR/foundation.json" "$TASK_DIR/schema12.json" <<'PY'
import json, sys
source, compiler = [json.load(open(path)) for path in sys.argv[1:]]
operand = source['bodies'][0]['blocks'][0]['statements'][0]['value']['operand']
assert operand['value']['kind'] == 'unevaluated'
expression = source['definitions'][operand['value']['definition']]['const_expression']
assert expression['operand']['value'] == {'kind':'scalar','bits':'37','size_bytes':1}
evaluated = compiler['statement_kinds'][0]['rvalue']['operand']['constant']['constant']['value']
assert (evaluated['bits_unsigned'], evaluated['size_bytes']) == ('37', 1)
assert len(source['bodies'][0]['required_consts']) == len(compiler['bodies'][0]['required_consts']) > 0
for constant in compiler['bodies'][0]['required_consts']:
    value = constant['constant']['value']
    assert (value['bits_unsigned'], value['size_bytes']) == ('37', 1)
PY
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationConstEval.lean "$TASK_DIR/foundation.json"
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationConstBodyCore.lean "$TASK_DIR/foundation.json"
cat > "$TASK_DIR/unsupported.rs" <<'RS'
const VALUE: u8 = 18 + 19;
pub fn scalar() -> u8 { VALUE }
RS
if bash tools/export-mir.sh --output "$TASK_DIR/unsupported.json" --foundation --root scalar \
    -- "$TASK_DIR/unsupported.rs" --crate-type=lib --crate-name unsupported_const \
    >"$TASK_DIR/unsupported.log" 2>&1; then
  echo 'unsupported const MIR arithmetic was accepted' >&2
  exit 1
fi
rg -q 'foundation: unsupported .*const' "$TASK_DIR/unsupported.log"
