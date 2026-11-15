The allocation snapshot exporter requires rustc commit
`8144389c895da997dbdecaa635e41d6a50be6ffd`, matching `upstream/miri-source/rust-version`.
The installed upstream toolchain does not expose the allocation map. Apply
`allocation-identity-snapshot.patch` to a separate checkout of that exact commit;
it adds one observation-only accessor and changes no allocation algorithm.
Do not patch the installed normal toolchain in place.

Build the compiler using rustc bootstrap with the pinned installed compiler as
`build.rustc`/`build.cargo`, `rust.download-rustc=false`, and a separate build
directory. The standard rustc compiler build is required only once:

```sh
python3 x.py --config /absolute/bootstrap.toml build --stage 1 compiler/rustc
```

Build matching MIR-enabled target std. Bootstrap normally enables MIR inlining
for std, so explicitly disable those bootstrap overrides to match the normal
Miri sysroot's unoptimized MIR. `--keep-stage 0` preserves the already built
compiler while rebuilding target std:

```sh
RUSTFLAGS_NOT_BOOTSTRAP='--cfg=miri -Zalways-encode-mir -Zextra-const-ub-checks -Zmir-preserve-ub -Zmir-opt-level=0 -Zinline-mir=no -Zinline-mir-preserve-debug=no -Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums -Zmir-enable-passes=-ReferencePropagation,-GVN -Zdeduplicate-diagnostics=no -Zembed-metadata=yes' \
  python3 x.py --config /absolute/bootstrap.toml build --stage 1 --keep-stage 0 library/std
```

From this repository, build the **normal exporter** with its explicit snapshot
feature against that build's private metadata and driver. Supply the exact
produced driver filename; the script obtains dependency hashes from its actual
metadata, checks the host compiler pin, and keeps artifacts separate:

```sh
python3 tools/build-snapshot-exporter.py \
  --compiler-build /absolute/build/x86_64-unknown-linux-gnu \
  --driver /absolute/build/x86_64-unknown-linux-gnu/stage1/lib/librustc_driver-HASH.so
python3 tools/export-snapshot-mir.py -- --foundation --output scratch/source.json \
  --root main --root std::rt::lang_start \
  --root 'std::rt::lang_start::{closure#0}' --root std::rt::lang_start_internal \
  -- tests/foundation/fixtures/std-main.rs --crate-name snapshot_std -Zthreads=1
```

The exporter captures the complete allocator map, dedup keys with their actual
salts, and next raw ID after all source collection. Serialization must leave a
second complete snapshot identical; otherwise export fails. This does not query
vtable slots, probe salts, evaluate a synthetic constant, or reserve an ID.
Non-vtable key equality remains an explicit unavailable capability. An exporter
built without the feature emits `allocation_identity_source: null`; it does not
assert an empty allocator state.

The first local build reused an existing matching custom compiler; rebuilding
its Miri-enabled target std took about 80 seconds. A clean compiler bootstrap
cost depends on the host and is substantially larger. Artifacts and absolute
local paths are intentionally excluded from version control.
