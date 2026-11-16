# Third-party source and attribution

Lean-Miri ports implementations from [Miri](https://github.com/rust-lang/miri),
at the revision recorded in `upstream/source-lock.json`. Credit for the upstream
implementations and their design belongs to the Miri contributors.
See [AUTHORS](AUTHORS) for authors of the Lean translation and project-specific
code.

The Rust project distributes the Miri source under
MIT OR Apache-2.0; the applicable license texts are retained in `LICENSE-MIT`
and `LICENSE-APACHE`, and in the upstream source snapshot.

The snapshots under `upstream/` are reference materials with their own license
notices. The upstream Miri snapshot retains its optional GenMC bridge;
retain its notices with that code. Listing external code in the
source lock does not mean it has been ported or that all its dependencies have
been audited.

The local Lean/Elan and Rust/Rustup installations are development tools, not
Lean-Miri semantics. They are excluded from version control. The Lean version is
pinned in `lean-toolchain`; the compiler used for the standalone Rust comparison
is recorded with that test's evidence, separately from Miri's rustc source pin.

The `localtime_r` timezone table is translated from chrono-tz 0.10.4's
generated IANA 2025b tables. The matching generated source is retained
compressed under `third_party/chrono-tz-0.10.4`; its dual MIT/Apache-2.0
license text is retained in `third_party/licenses/chrono-tz-0.10.4/LICENSE`.
The IANA tzdb files included in that generated table are public domain as
stated by chrono-tz's license. Exact source hashes and the offline generator
are documented in [chrono-tz translation](docs/chrono-tz-source-port.md).

The randomized field-layout implementation in
`Miri/Input/ConcreteFieldShuffle.lean` translates Rand 0.9.3's slice shuffle and
integer sampling, and rand_xoshiro 0.7.0's Xoshiro128** and SplitMix64 generators.
The source files retain these notices: “Copyright 2018-2023 Developers of the
Rand project” (`rand/src/seq/{slice,increasing_uniform}.rs`), “Copyright 2018-2020 Developers of the
Rand project” and “Copyright 2017 The Rust Project Developers”
(`rand/src/distr/uniform_int.rs`), and “Copyright 2018 Developers of the Rand
project” (`rand_xoshiro/src/{xoshiro128starstar,splitmix64}.rs`). Both crates are
licensed under MIT OR Apache-2.0; their license and copyright texts are retained
under `third_party/licenses/rand-0.9.3/` and
`third_party/licenses/rand_xoshiro-0.7.0/`.
The seed word order follows rand_core 0.9.3's little-endian implementation
helpers, bearing “Copyright 2018 Developers of the Rand project.” Its MIT OR
Apache-2.0 texts are retained in `third_party/licenses/rand_core-0.9.3/`.
