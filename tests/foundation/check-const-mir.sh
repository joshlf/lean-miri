#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
TASK_DIR="$(mktemp -d "$ROOT/scratch/const-mir.XXXXXX")"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationConstOperand Miri.Frontend.FoundationConstBindings
for root in sum branch otherwise wide; do
  bash tools/export-mir.sh --output "$TASK_DIR/$root-foundation.json" --foundation --root "$root" -- exporter/fixtures/foundation_const_expr.rs --crate-type=lib --crate-name const_expr
  bash tools/export-mir.sh --output "$TASK_DIR/$root-schema12.json" --root "$root" -- exporter/fixtures/foundation_const_expr.rs --crate-type=lib --crate-name const_expr
  python3 - "$TASK_DIR" "$root" <<'PY'
import json,pathlib,sys
out=pathlib.Path(sys.argv[1]); root=sys.argv[2]
doc=json.loads((out/f'{root}-schema12.json').read_text())
value=doc['statement_kinds'][0]['rvalue']['operand']['constant']['constant']['value']
(out/f'{root}-reference.json').write_text(json.dumps({'root':root,'bits':value['bits_unsigned'],'size_bytes':value['size_bytes']}))
source=json.loads((out/f'{root}-foundation.json').read_text())
assert any(d.get('const_expression',{}).get('kind')=='mir' for d in source['definitions'])
assert not any(key.startswith('compiler_') for key in source)
PY
  "$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationConstMir.lean "$TASK_DIR/$root-foundation.json" "$TASK_DIR/$root-reference.json"
done
printf 'const VALUE: u8 = 255 + 1; pub fn scalar() -> u8 { VALUE }\n' > "$TASK_DIR/overflow.rs"
if "$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/bin/rustc" "$TASK_DIR/overflow.rs" --crate-type=lib --emit=metadata -o "$TASK_DIR/overflow.rmeta" > "$TASK_DIR/overflow.log" 2>&1; then
  echo 'compiler accepted overflowing CTFE control' >&2
  exit 1
fi
rg -q 'E0080' "$TASK_DIR/overflow.log"
echo "fresh const MIR comparison evidence: $TASK_DIR"
