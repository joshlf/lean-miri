#!/usr/bin/env bash
# Fresh source literal -> canonical fixed frame and checked provenance read.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/literal-execute.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationLiteralExecute
for mode in foundation schema12; do
  foundation=()
  if [[ "$mode" == foundation ]]; then foundation=(--foundation); fi
  bash tools/export-mir.sh --output "$TASK_DIR/$mode.json" "${foundation[@]}" --root bytes -- \
    exporter/fixtures/foundation_allocations.rs --crate-name literal_bytes
 done
python3 - "$TASK_DIR/foundation.json" "$TASK_DIR/schema12.json" <<'PY'
import json, sys
source, compiler = [json.load(open(path)) for path in sys.argv[1:]]
a = source['bodies'][0]['blocks'][0]['statements'][0]['value']['operand']['value']
b = compiler['statement_kinds'][0]['rvalue']['operand']['constant']['constant']['value']
assert a['kind'] == 'allocation_pointer' and b['kind'] == 'pointer_scalar'
for field in ('offset_bytes', 'immutable', 'shared_ref'):
    assert a[field] == b[field]
image = source['source_allocations'][a['allocation']]
reference = compiler['allocations'][b['allocation']]
assert image['bytes_hex'] == compiler['byte_images'][reference['byte_image_id']] == b'Miri'.hex()
assert (image['size_bytes'],image['align_bytes'],image['mutable']) == (4,1,False)
assert (reference['size_bytes'],reference['align_bytes'],reference['mutability']) == (4,1,'immutable')
assert image['relocations'] == compiler['relocations'][reference['relocations']] == []
assert image['initialization_ranges'] == [{'initialized':True,'start_bytes':0,'end_bytes_exclusive':4}]
assert compiler['initialization_ranges'][reference['initialization_ranges']] == [{'state':'initialized','start_bytes':0,'end_bytes_exclusive':4}]
PY
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationLiteralExecute.lean "$TASK_DIR/foundation.json"
