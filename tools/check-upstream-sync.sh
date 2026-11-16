#!/usr/bin/env bash
# Fresh same-TyCtxt comparisons for behavior changed by the November Miri pin.
# The ordinary UI driver keeps original Rust, profiles and failure-site oracles.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 tools/check-upstream-ui.py \
  --case pass/main_result.rs \
  --case pass/fn-traits-abi.rs \
  --case pass/function_calls/abi_compat.rs \
  --case pass/x87_f80.rs \
  --case pass/shims/x86/intrinsics-x86-sse42.rs \
  --case pass/concurrency/threadname.rs \
  --case fail/intrinsics/copy_overlapping2.rs \
  --case fail/intrinsics/write_bytes_unaligned.rs \
  --case fail/uninit/union-aggregate-init-padding.rs \
  "$@"
