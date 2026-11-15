#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p scratch
# These are explicit rejection controls, not successful source/program captures.
for role in catch unwrap; do
  if [[ "$role" == catch ]]; then
    root='std::panic::catch_unwind'
    expected='unsupported predicate: ProjectionClause('
  else
    root='std::result::Result::<T, E>::unwrap_or_else'
    expected='unsupported caller location prerequisite:'
  fi
  if bash tools/export-mir.sh --output "scratch/foundation-std-frontier-$role.json" --foundation \
      --root "$root" -- tests/foundation/fixtures/std-main.rs --crate-name=foundation_std_main \
      > "scratch/foundation-std-frontier-$role.log" 2>&1; then
    printf 'Expected explicit source frontier rejection for %s\n' "$role" >&2
    exit 1
  fi
  rg -F "$expected" "scratch/foundation-std-frontier-$role.log"
done
bash tests/foundation/check-std-source.sh
