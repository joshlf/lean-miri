#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/termination.XXXXXX")"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationObligations Miri.Frontend.FoundationItemResolution > "$TASK_DIR/build.log" 2>&1 || { tail -50 "$TASK_DIR/build.log"; exit 1; }
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation --root bound -- exporter/fixtures/foundation_termination.rs --crate-name foundation_termination --crate-type=lib
bash tools/export-mir.sh --output "$TASK_DIR/compiler.json" --root unit_report -- exporter/fixtures/foundation_termination.rs --crate-name foundation_termination --crate-type=lib
bash tools/export-mir.sh --output "$TASK_DIR/std.json" --foundation --root main --root std::rt::lang_start --root 'std::rt::lang_start::{closure#0}' --root std::rt::lang_start_internal -- tests/foundation/fixtures/std-main.rs --crate-name foundation_termination_std
cat > "$TASK_DIR/negative.rs" <<'RS'
fn require<T: std::process::Termination>(_: T) {}
fn main() { require(1u8); }
RS
if bash tools/export-mir.sh --output "$TASK_DIR/negative.json" --root main -- "$TASK_DIR/negative.rs" > "$TASK_DIR/negative.log" 2>&1; then
  echo 'compiler accepted unsupported Termination(u8)' >&2; exit 1
fi
rg -q 'Termination.*not satisfied|Termination.*not implemented' "$TASK_DIR/negative.log"
python3 - "$TASK_DIR" <<'PY'
import json,pathlib,sys
p=pathlib.Path(sys.argv[1]); c=json.loads((p/'compiler.json').read_text())
refs=[{'identity':{'crate':c['definitions'][i['def_id']]['crate'],'index':c['definitions'][i['def_id']]['index']},'display':i['def_path']} for i in c['instances'] if i['instance_kind']['kind']=='item']
(p/'methods.json').write_text(json.dumps(refs))
s=json.loads((p/'source.json').read_text()); t=s['termination_source']
print('complete_headers',len(t['implementations']),'source_bytes', (p/'source.json').stat().st_size,'material_bytes',len(json.dumps(t,separators=(',',':')).encode()))
PY
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationTermination.lean "$TASK_DIR/source.json" "$TASK_DIR/methods.json" "$TASK_DIR/std.json"
echo "fresh termination evidence: $TASK_DIR"
