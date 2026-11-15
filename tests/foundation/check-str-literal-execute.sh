#!/usr/bin/env bash
# Actual wide-pointer metadata drives the fixed memory read of Unicode bytes.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/str-literal-execute.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationStrLiteralExecute
for mode in foundation schema12; do
  foundation=()
  if [[ "$mode" == foundation ]]; then foundation=(--foundation); fi
  bash tools/export-mir.sh --output "$TASK_DIR/$mode.json" "${foundation[@]}" --root literal -- \
    exporter/fixtures/foundation_str_literal.rs --crate-name unicode_str
done
python3 - "$TASK_DIR/foundation.json" "$TASK_DIR/schema12.json" <<'PY'
import json, sys
source, compiler = [json.load(open(path)) for path in sys.argv[1:]]
a = source['bodies'][0]['blocks'][0]['statements'][0]['value']['operand']['value']
b = compiler['statement_kinds'][0]['rvalue']['operand']['constant']['constant']['value']
assert a['kind'] == 'allocation_slice' and b['kind'] == 'slice_allocation'
assert a['metadata'] == b['metadata_length'] == len('Lean🦀'.encode()) == 8
assert a['metadata'] != len('Lean🦀')
image = source['source_allocations'][a['allocation']]
reference = compiler['allocations'][b['allocation']]
assert image['bytes_hex'] == compiler['byte_images'][reference['byte_image_id']] == 'Lean🦀'.encode().hex()
assert (image['size_bytes'],image['align_bytes'],image['mutable']) == (8,1,False)
assert (reference['size_bytes'],reference['align_bytes'],reference['mutability']) == (8,1,'immutable')
assert image['relocations'] == compiler['relocations'][reference['relocations']] == []
assert image['initialization_ranges'] == [{'initialized':True,'start_bytes':0,'end_bytes_exclusive':8}]
assert compiler['initialization_ranges'][reference['initialization_ranges']] == [{'state':'initialized','start_bytes':0,'end_bytes_exclusive':8}]
PY
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationStrReferences.lean "$TASK_DIR/foundation.json" "$TASK_DIR/schema12.json"
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationStrLiteralExecute.lean "$TASK_DIR/foundation.json"
