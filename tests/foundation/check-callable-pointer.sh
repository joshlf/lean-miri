#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/callable-pointer.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationCallable
for mode in safe unsafe foreign; do
  bash tools/export-mir.sh --output "$TASK_DIR/$mode.json" --foundation --root "${mode}_pointer" -- \
    exporter/fixtures/foundation_callable_pointer.rs --crate-name callable_pointer
  ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
    tests/foundation/FoundationCallablePointer.lean "$TASK_DIR/$mode.json" "$mode"
done
bash tools/export-mir.sh --output "$TASK_DIR/identity.json" --foundation --root scalar_identity -- \
  exporter/fixtures/foundation_callable_pointer.rs --crate-name callable_pointer
python3 - "$TASK_DIR" <<'PY'
import json, pathlib, sys
root = pathlib.Path(sys.argv[1])
for mode in ('safe', 'unsafe', 'foreign'):
    source = json.loads((root / f'{mode}.json').read_text())
    assert source['fn_vtable_source'] is not None
    assert not source['closure_templates']
    assert all(row['shape']['kind'] != 'dynamic' for row in source['types'])
source = json.loads((root / 'identity.json').read_text())
assert source['fn_vtable_source'] is None
PY
# Independent pinned compiler trait checks distinguish source rejection from
# a successful builtin implementation; no resulting query answers are imported.
CALLABLE_RUSTC="$ROOT/.rustup/toolchains/miri-exporter-8144389c895d/bin/rustc"
for mode in safe unsafe foreign; do
  case "$mode" in
    safe) pointer_type='fn() -> i32' ;;
    unsafe) pointer_type='unsafe fn() -> i32' ;;
    foreign) pointer_type='extern "C" fn() -> i32' ;;
  esac
  cat > "$TASK_DIR/trait-$mode.rs" <<RS
#![no_std]
fn accepts<F: Fn() -> i32>(_value: F) {}
pub fn check(value: $pointer_type) { accepts(value); }
RS
  if [[ "$mode" == safe ]]; then
    "$CALLABLE_RUSTC" --crate-type=lib --emit=metadata --crate-name callable_trait \
      "$TASK_DIR/trait-$mode.rs" -o "$TASK_DIR/trait-$mode.rmeta"
  else
    if "$CALLABLE_RUSTC" --crate-type=lib --emit=metadata --crate-name callable_trait \
        "$TASK_DIR/trait-$mode.rs" -o "$TASK_DIR/trait-$mode.rmeta" >"$TASK_DIR/trait-$mode.log" 2>&1; then
      echo "compiler unexpectedly accepted $mode pointer as safe Fn" >&2
      exit 1
    fi
    rg -q 'error\[E0277\]' "$TASK_DIR/trait-$mode.log"
    rg -q 'Fn\(\)' "$TASK_DIR/trait-$mode.log"
  fi
done
