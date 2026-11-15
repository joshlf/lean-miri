#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
TASK_DIR="$(mktemp -d "$ROOT/scratch/link-initializers.XXXXXX")"
printf 'fn main() {}\n' > "$TASK_DIR/std.rs"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationLinkInitializers > "$TASK_DIR/build.log" 2>&1 || { tail -50 "$TASK_DIR/build.log"; exit 1; }
bash tools/export-mir.sh --output "$TASK_DIR/local.json" --foundation --root main -- exporter/fixtures/foundation_link_initializers.rs --crate-name link_initializers
bash tools/export-mir.sh --output "$TASK_DIR/std.json" --foundation --root main -- "$TASK_DIR/std.rs" --crate-name link_initializers_std
bash tools/export-mir.sh --output "$TASK_DIR/compiler.json" --root probe --root probe3 -- exporter/fixtures/foundation_link_initializers.rs --crate-type=lib --crate-name link_initializers
python3 - "$TASK_DIR" <<'PY'
import json,pathlib,sys
p=pathlib.Path(sys.argv[1]); d=json.loads((p/'compiler.json').read_text()); references=[]
for static in d['allocations']:
 if static['kind']!='static' or static['def_path'] not in ['INIT','PRIORITY']:continue
 image=static['initializer']; relocs=d['relocations'][image['relocations']]
 assert len(relocs)==1 and relocs[0]['storage_offset_bytes']==0
 reloc=relocs[0]; assert reloc['target_offset_encoded_bytes']=='0000000000000000'
 function=next(node for node in d['allocations'] if node['kind']=='function' and any(alias[0]==reloc['target'] for alias in node['identities']))
 instance=d['instances'][function['instance_id']]; assert instance['instance_kind']['kind']=='item' and instance['generic_args']==[]
 staticDef=d['definitions'][static['def_id']]; functionDef=d['definitions'][instance['def_id']]
 assert staticDef['crate']==functionDef['crate']==0
 assert d['byte_images'][image['byte_image_id']]=='0000000000000000'
 assert d['initialization_ranges'][image['initialization_ranges']]==[{'state':'initialized','start_bytes':0,'end_bytes_exclusive':8}]
 references.append({'static_index':staticDef['index'],'function_index':functionDef['index'],'size_bytes':image['size_bytes'],'align_bytes':image['align_bytes']})
assert len(references)==2
(p/'reference.json').write_text(json.dumps(references))
source=json.loads((p/'local.json').read_text()); assert source['source_allocations']==[]
PY
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationLinkInitializers.lean "$TASK_DIR/local.json" "$TASK_DIR/std.json" "$TASK_DIR/reference.json"
echo "fresh link initializer evidence: $TASK_DIR"
