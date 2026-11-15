# Finite compiler material and demand-time Lean queries

The intended execution boundary is a finite rustc export followed by pure Lean
computation. rustc may produce MIR, definition templates, type structure, generic
parameters, clauses and target data once. Neither execution nor a proof may ask a
running rustc process for an answer. Compiler query results should instead be
computed from the exported material when Lean needs them. Reusing a result within
one evaluation is an implementation choice; no answer may depend on a writable
cache shared between runs.

`--foundation` starts that boundary with the separate `lean-miri-foundation` v1
input. It exports selected **generic** MIR templates, structural type and
definition graphs, complete target evidence, source metadata, signatures,
compilation settings, entry and frame source metadata, producer identity,
foreign linkage selectors, required-constant source material and generic clauses. IDs name rows
within the document. Type and const parameters retain rustc's shared parameter
indices. It does not enumerate substitutions or serialize layout, ABI, predicate,
instance or interpreter query-answer catalogs. Unsupported source constructs
abort export. The producer and decoder reject a different pinned rustc commit.

In Lean, `Foundation.decode` loads this finite document, `typeExpr` resolves a
requested type, `instantiate` substitutes a requested type/const argument tuple,
and `checkEnvironment` checks the known `Sized`, `Copy` and `usize` obligations
for the restricted structural type domain. Each is a pure function of the
document and explicit arguments. Known scalar required constants are checked
on frame demand, including unreachable obligations; unevaluated const MIR
remains unsupported. Unknown obligations are errors. The existing
fixed interpreter also now computes canonical nested-array layouts on demand
from its imported type graph, with explicit cycle, overflow and contradiction
errors.

The restricted foundation evaluator still exercises identity and array-body
fixtures as a fixture validator. Separately, Lean derives physical primitive
types and layouts, a limited direct function ABI, ordinary item and frame
identities, source spans, session settings, primitive and foreign catalogs, and
the required input graph from the finite document. For a checked `u8` identity
body, the canonical compiler provider preparation and the **fixed Miri
interpreter** execute the actual assignment and Return from a direct call
frame; the observed return is 42 and the frame stack becomes empty. The run
uses an explicit fixed scheduling profile and finite address choices. It is a
bounded observation, not process startup or a safety proof. The schema-12 path
still supplies general fixed-interpreter programs. The active missing work is
tracked in [STATUS.md](../STATUS.md).

Lean rejects demands outside the supported source domain. In particular,
general trait resolution, const-MIR evaluation, indirect ABI, calls,
allocations and provenance from source, runtime symbol identities and broader
MIR are not yet supplied by pure foundation queries. Coroutines, inlined
frames, target features and caller-location tracking also stop. The direct
identity frame needs none of those facts; its effect-domain check excludes
their use before constructing the limited program. General migration requires
computing each demanded query from finite source material and expanding the
supported interpreter domain without invented compiler answers.

## Proof and trust boundary

rustc's MIR generation, compiler revision, target description and the exporter's
faithful encoding remain assumptions about the external Rust program. A Lean
theorem would then need to state the exact exported document, initial state,
external contracts and permitted choices, and cover every reachable permitted
finite prefix of the **fixed** interpreter. A successful export, decoder check,
restricted fixture evaluation, concrete run or finite Miri comparison establishes
none of those universal claims. Missing semantics, query answers, overflow and
unsupported forms must stop with errors rather than successful execution.

## Measured export cost

For one 134-byte concrete `[u16; 3]` source, five alternating sequential trials
used the same pinned release exporter binary, CPU 2 and one Lean thread. The
ordinary schema-12 export had median wall/CPU time 0.136176/0.131818 s and a
137,397-byte output. Foundation v1 had median wall/CPU time
0.133546/0.132906 s and a 23,058-byte output. Wall ranges were 0.131504–0.224531
and 0.123980–0.166751 s respectively. Two trials per format saw 0.01 s selected
CPU steal; cgroup throttling deltas were zero. Raw timings, hashes and counters
are in ignored `scratch/performance/export-e0f5f3f3/` in the measuring workspace. The ordinary
measurements vary substantially and these formats support different operations,
so this is an export-only comparison, not a claim of equivalent executions or
interpreter speedup.
