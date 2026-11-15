# MIR exporter

The exporter reads MIR and compiler results from the pinned rustc and writes the
`lean-miri-rustc-mir` schema 13 document consumed by Lean. It exports concrete
instance bodies and evaluated operands, layouts, ABIs, constants, trait and
instance answers, plus the type syntax needed to interpret those results.
See the [development guide](../docs/development.md#rust-toolchain-and-reference-setup)
for pinned toolchains and setup.

```bash
export CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup"
export MIRI_SYSROOT="$PWD/scratch/miri-sysroot"
toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d build --locked --manifest-path exporter/Cargo.toml
mkdir -p scratch/exports
exporter/target/debug/lean-miri-mir-exporter --output scratch/exports/add-one.json \
  --root add_one -- exporter/fixtures/scope/simple.rs --crate-type=lib --crate-name=scoped_closure
ELAN_HOME="$PWD/.elan" .elan/bin/lake build check_input
ELAN_HOME="$PWD/.elan" .elan/bin/lake exe check_input scratch/exports/add-one.json
```

`--root` selects an exact nongeneric local definition. Without it, closed local
bodies are roots. Generic bodies enter through concrete instances reached from
those roots; selecting a generic definition directly is an error. `check_input`
diagnoses readiness and does not execute a guest or prove safety. The
experimental `import_mir` command in `Miri.Frontend.ImportMIR` imports the
exported data as Lean constants.

For Cargo projects, use `exporter/target/debug/lean-miri-mir-exporter --cargo check
--manifest-path /path/to/Cargo.toml`. The wrapper rebuilds dependencies with
MIR, writes target crate JSON under `lean-miri-mir/` in the target directory,
and continues ordinary code generation. Host tools and proc macros use the
pinned compiler but are not exported. It rejects response files because their
exact arguments cannot be fingerprinted.

## Input contract

The document uses dense, document-local IDs for compiler types, layouts, ABIs,
instances, definitions, bodies, constants, allocations, spans and predicates.
Each executable body is rustc's concrete instance MIR. Constant operands carry
rustc's evaluated value. Layout and ABI rows carry the complete queried
compiler result, including field and variant layouts. Lean keeps type and
binder syntax to interpret these results, not to compute replacement answers.
Missing MIR, constant evaluation, normalization, layout, ABI or instance
results fail the export; they are never encoded as a successful empty value.
Successful `false`, `None` and empty compiler answers retain their meaning.

The exporter reserves IDs before recursively visiting a definition and rejects
unfinished graph entries. Allocation identity stays separate from allocation
bytes. Equal immutable payloads may share JSON storage, while distinct
compiler keys retain their IDs. The prepared allocation world records the
compiler's source allocation IDs and selected dedup keys needed to start Miri
execution. It is captured after export; it does not import a mutable compiler
query cache into Lean.

Runtime data still determines dynamic calls, vtables, external effects and the
execution path. A successful export establishes only that the requested
compiler data was captured. It does not establish interpreter correspondence
or undefined behavior freedom. See the [compiler result boundary](../docs/compiler-result-boundary.md)
for the detailed trust boundary and [connected tests](../tests/connected/README.md)
for fresh reference comparison versus saved replay.

Set `LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1` for prepared execution such as `main`.
Building with `--features miri-reference` and setting
`LEAN_MIRI_RUN_PREPARED_MIRI=1` generates a Miri reference sidecar in the same
TyCtxt after export. That comparison uses the prepared allocation history; it
is not a vanilla Miri allocation history.

[build.rs](build.rs) checks the exact rustc commit. On Linux the exporter also
checks the loaded `librustc_driver`; other hosts fail this check. The optional
`tools/exporter_provenance.py` manifest records input and binary SHA-256 values.
FNV fingerprints are consistency checks, not cryptographic hashes.

## Tests

With the pinned toolchain and MIR-enabled sysroot, run:

```bash
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d test --locked --offline --manifest-path exporter/Cargo.toml
```

Cargo runs Rust unit tests, Python tests under `exporter/tests/`, fixture
scripts and producer checks. Fixture tests require the pinned compiler and
matching MIR-enabled sysroot; missing prerequisites fail explicitly. The
exporter tests check this boundary only. Lean decoder, frontend, execution and
reference comparisons under root `tests/` are separate checks.

Prepared allocation coverage is finite: selected function, vtable, static and
TypeId keys have checked outcomes; general constant-memory keys are not
complete. The decoder rejects missing selected keys or truncated salts, and a
runtime request outside the selected domain remains an error. A fresh prepared
snapshot can be checked with:

```bash
EXPORTER_BIN=exporter/target/release/lean-miri-mir-exporter \
  bash exporter/tests/run-producer.sh selected_alloc_world scratch/selected-keys.json
lake env lean --run tests/input/SelectedKeyCoverageStrict.lean scratch/selected-keys.json
lake env lean --run tests/input/AllocWorldRuntime161.lean scratch/selected-keys.json
```
