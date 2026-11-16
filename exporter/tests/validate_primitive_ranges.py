#!/usr/bin/env python3
"""Check the actual u128/niche oracle paired with typed Lean layout comparison."""
from pathlib import Path
import json
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

output=Path(sys.argv[1])
document=load_mir_document(output);lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
for source in ['rustc','miri']:assert document['producer'][source+'_commit']==lock['pins'][source]['commit']
type_id=document['compiler_runtime_primitives']['u128']
node=next(t for t in document['types'] if t['type_id']==type_id)
oracle=json.loads(Path(sys.argv[2]).read_text())
layouts={row['type_id']:row['layout'] for row in oracle['types']}
assert 'layouts' not in document and 'compiler_facts' not in node
assert layouts[type_id]['backend_repr']['scalar']['valid_range']=={'start':'0','end':str(2**128-1)}
assert any(layout.get('largest_niche', {}).get('valid_range', {}).get('end') == str(2**128-1)
           for layout in layouts.values() if layout.get('largest_niche'))
print('validated exact compiler u128 range and niche oracle; typed layout comparison follows')
