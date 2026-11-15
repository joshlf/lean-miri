#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/source-graph.XXXXXX")"
export RUSTUP_HOME="$ROOT/.rustup" CARGO_HOME="$ROOT/.cargo"
export PATH="$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/bin:$ROOT/.cargo/bin:$PATH"
export LD_LIBRARY_PATH="$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cat > "$TASK_DIR/dependency.rs" <<'RUST'
#![no_std]
pub fn first<T>(value: T) -> T { second(value) }
pub fn second<T>(value: T) -> T { value }
pub fn unrequested(value: u8) -> u8 { value }
pub fn unsupported_body(value: u8) -> u8 { value + 1 }
pub fn creator(value: u8) -> u8 { let identity = |value: u8| value; identity(value) }
RUST
cat > "$TASK_DIR/caller.rs" <<'RUST'
#![no_std]
extern crate graph_dependency;
pub fn caller(value: u8) -> u8 { graph_dependency::first(value) }
pub fn closure_caller(value: u8) -> u8 { graph_dependency::creator(value) }
pub fn unsupported_caller(value: u8) -> u8 { graph_dependency::unsupported_body(value) }
unsafe extern "C" { fn foreign(value: u8) -> u8; }
pub unsafe fn foreign_caller(value: u8) -> u8 { unsafe { foreign(value) } }
RUST
rustc "$TASK_DIR/dependency.rs" --crate-name graph_dependency --crate-type rlib \
  --edition=2024 --sysroot "${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}" \
  -Zalways-encode-mir -Zmir-opt-level=0 -o "$TASK_DIR/libgraph_dependency.rlib"
export_source() {
  bash tools/export-mir.sh --foundation --output "$TASK_DIR/$1.json" "${@:2}" -- \
    "$TASK_DIR/caller.rs" --crate-name graph_caller --crate-type lib \
    --extern "graph_dependency=$TASK_DIR/libgraph_dependency.rlib"
}
export_source chain --root caller --root graph_dependency::first --root graph_dependency::second
export_source closure --root closure_caller --root graph_dependency::creator --root 'graph_dependency::creator::{closure#0}'
export_source unsupported_header --root unsupported_caller
export_source foreign --root foreign_caller
export_source partial --root caller --root graph_dependency::first
export_source header --root caller --foundation-signature-root graph_dependency::first
if export_source disconnected --root graph_dependency::second > "$TASK_DIR/disconnected.log" 2>&1; then
  echo 'Unconnected external source root unexpectedly selected' >&2; exit 1
fi
rg -F 'missing MIR root' "$TASK_DIR/disconnected.log"
if export_source absent --root caller --root graph_dependency::unrequested > "$TASK_DIR/absent.log" 2>&1; then
  echo 'Non-edge external source root unexpectedly selected' >&2; exit 1
fi
rg -F 'missing MIR root' "$TASK_DIR/absent.log"
if export_source unsupported --root unsupported_caller --root graph_dependency::unsupported_body > "$TASK_DIR/unsupported.log" 2>&1; then
  echo 'Selected unsupported source body unexpectedly omitted' >&2; exit 1
fi
rg -F 'foundation: unsupported terminator: assert(' "$TASK_DIR/unsupported.log"

python3 - "$TASK_DIR" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
def names(doc, field):
    return [doc['definitions'][row['definition']]['path'] for row in doc[field]]
chain = json.loads((root/'chain.json').read_text())
partial = json.loads((root/'partial.json').read_text())
header = json.loads((root/'header.json').read_text())
closure = json.loads((root/'closure.json').read_text())
unsupported = json.loads((root/'unsupported_header.json').read_text())
foreign = json.loads((root/'foreign.json').read_text())
assert names(chain,'bodies') == ['caller','graph_dependency::first','graph_dependency::second']
assert names(partial,'bodies') == ['caller','graph_dependency::first']
assert set(names(partial,'source_function_signatures')) == {'graph_dependency::first','graph_dependency::second'}
assert names(unsupported,'bodies') == ['unsupported_caller']
assert names(unsupported,'source_function_signatures') == ['graph_dependency::unsupported_body']
assert names(foreign,'bodies') == ['foreign_caller']
assert names(foreign,'source_function_signatures') == ['foreign']
assert foreign['source_function_signatures'][0]['function_attributes']['is_foreign']
assert foreign['source_function_signatures'][0]['owner_declaration']['kind'] == 'foreign_function'
assert names(header,'bodies') == ['caller']
assert names(header,'source_function_signatures') == ['graph_dependency::first']
assert not chain['closure_templates']
assert names(closure,'bodies') == ['closure_caller','graph_dependency::creator']
assert names(closure,'closure_templates') == ['graph_dependency::creator::{closure#0}']
assert any(row['owner_declaration']['kind'] == 'trait_method' for row in closure['source_function_signatures'])
for header in closure['source_function_signatures']:
    if header['owner_declaration']['kind'] != 'trait_method':
        continue
    layer = header['environment']['layers'][0]
    owner = closure['definitions'][layer['owner']]
    self_parameter = layer['parameters'][0]
    assert layer['has_self'] and owner['generic_declaration']['has_self']
    assert owner['kind'] in ['Trait', 'TraitAlias']
    assert self_parameter['kind'] == 'type' and self_parameter['index'] == 0
    assert self_parameter['definition'] == layer['owner']
    assert self_parameter['has_default'] is False and self_parameter['default'] is None

assert any(row['shape']['kind'] == 'projection_alias' for row in closure['types'])
print('generic finite source graph: direct dependency chain, header-only and exact frontier controls PASS')
PY
