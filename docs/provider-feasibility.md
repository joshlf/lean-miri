# Live rustc query provider feasibility experiment

This focused experiment runs Lean while rustc's `after_analysis` callback still
owns a live `TyCtxt`. Lean writes newline-delimited JSON requests on stdout;
the pinned rustc process reads them, calls `tcx.layout_of` on a concrete
`Foo<T>`, and writes JSON answers to Lean's stdin. A final request follows a
100 ms pause in Lean. The successful answer establishes that this callback
kept the same compilation context alive across Lean's execution and the pause.

The request vocabulary is deliberately narrow: `layout_of` for `Foo<u8>` and
`Foo<u64>` in [the fixture](../tests/provider/fixture.rs). Rust maps the
request to a `Ty<'tcx>` inside the callback, with a fully monomorphized typing
environment. Lean asserts `Foo<u8>` has size 2, alignment 1 and `Foo<u64>`
has size 16, alignment 8 on the pinned x86-64 target. Unknown operations and
type arguments fail. The Rust `TyCtxt` cannot safely escape the callback; the
Lean child must complete before the callback returns.

## Reproduce

Install the pinned toolchains in [development setup](development.md), then run:

```bash
bash tools/check-provider-probe.sh
```

The script builds the dedicated `lean-rustc-provider-probe` binary with the
pinned rustc commit `8144389c895d`, then executes five sequential trials with
both processes pinned to the first available CPU. It saves full raw records in
ignored `scratch/provider-probe/trial-*.json`. If the toolchains live elsewhere,
set `RUSTUP_HOME`, `CARGO_HOME` and `ELAN_HOME` first. The probe's JSON output
includes all 21 requests, rustc query durations, Lean request/answer round
trips, Lean startup and callback duration. The trial record includes process
wall and waited-child CPU time, selected CPU steal ticks and cgroup throttling delta.

## Observed results

Five runs on 2026-11-15, pinned compiler and Lean 4.35.0, CPU 0, one Lean
process and no parallel trials:

| Measure | Observation |
| --- | ---: |
| Requests | 21 each: 10 `Foo<u8>`, 11 `Foo<u64>` |
| Result | All sizes and alignments passed, including delayed final query |
| Median of per-trial median Lean round trips | 43.245 µs |
| Median cached rustc `layout_of` time after first two queries | 0.15–0.16 µs per trial |
| First `Foo<u8>` rustc query | 0.125–2.610 ms |
| Lean startup to `ready` | 0.994–1.317 s |
| Full process wall | 1.165–1.558 s; median 1.423 s |
| Waited-child process CPU | 1.059–1.411 s; median 1.271 s |
| Selected CPU steal | 5–9 ticks per trial |
| Cgroup throttling | 0 µs in all trials |

The median round trip includes JSON serialization, flushing, pipes, scheduling,
request parsing, rustc query, response parsing and Lean checks. The rustc query
measurement wraps only `tcx.layout_of`; it does not include type construction.
This shared host shows feasibility and approximate cost for this tiny request,
not a stable latency guarantee or a throughput estimate for real MIR execution.

The probe does not connect to the Lean Miri interpreter, support arbitrary
types or queries, prove general demand closure, or show that rustc's context
could survive beyond `after_analysis`. A production provider needs an explicit
type identity protocol, query-specific error handling, cancellation and a
plan for contexts spanning multiple compilations.
