#!/usr/bin/env python3
"""Select unchanged schema12 layout rows for genuine std internal locals.
Comparison-only projection. No rows are supplied to foundation readers.
"""
import json
import sys
source = json.load(open(sys.argv[1]))
assert source['schema_version'] == 12
items = [r for r in source['instances'] if r.get('def_path') == 'std::rt::lang_start_internal'
         and r['instance_kind']['kind'] == 'item']
assert len(items) == 1
body = source['bodies'][items[0]['body']]
rows = []
for local in body['locals']:
    node = source['types'][local['type']]
    rows.append(source['layout_values'][source['layouts'][node['layout']]])
closure = source['types'][body['locals'][6]['type']]
tuple_id = closure['shape']['generic_args'][-1]['value']
tuple_row = source['types'][tuple_id]
json.dump({'rustc_commit': source['producer']['rustc_commit'], 'local_layouts': rows,
           'capture_tuple_layout': source['layout_values'][source['layouts'][tuple_row['layout']]]},
          open(sys.argv[2], 'w'))
