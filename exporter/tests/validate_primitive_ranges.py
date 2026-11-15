#!/usr/bin/env python3
"""Check the exported u128 layout and niche range from rustc."""
from pathlib import Path
import json
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

output = Path(sys.argv[1])
document = load_mir_document(output)
lock = json.loads((ROOT / 'upstream/source-lock.json').read_text())
for source in ('rustc', 'miri'):
    assert document['producer'][source + '_commit'] == lock['pins'][source]['commit']
type_id = document['compiler_runtime_primitives']['u128']
node = next(row for row in document['types'] if row['type_id'] == type_id)
assert node['shape'] == {'kind': 'uint', 'unsigned_kind': 'u128'}
layout = pool_entry(document, 'layouts', node['layout'])
assert layout['size_bytes'] == 16 and layout['abi_align_bytes'] == 16
assert layout['backend_repr']['scalar']['primitive'] == {
    'kind': 'integer', 'integer_kind': 'i128', 'signed': False, 'size_bytes': 16}
assert layout['backend_repr']['scalar']['valid_range'] == {
    'start': '0', 'end': str(2**128 - 1)}
assert any(row.get('largest_niche', {}).get('valid_range', {}).get('end') == str(2**128 - 1)
           for row in document['layouts'] if row.get('largest_niche'))
print('validated rustc u128 layout and exact compiler niche range')
