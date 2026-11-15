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
compilation settings, required-constant source material and generic clauses. IDs name rows
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

The restricted foundation evaluator exercises identity and array-body fixtures
after those checks. It accepts only fully initialized scalar and aggregate
values with a single straight-line block and whole-local assignments. It is a
fixture validator, **not** the fixed Miri interpreter and not a safety proof.
Pure item preparation also joins requested type arguments, target evidence,
source locations and function signature fields. A separate syntax lowering
produces an `MIR.Body` candidate for the restricted straight-line subset. The
current schema-12 input still feeds the fixed interpreter. The migration is
complete only when the fixed interpreter receives its required data from the
finite foundation material and Lean computes its remaining compiler queries.
The active missing work is tracked in [STATUS.md](../STATUS.md).

A direct bridge to the fixed interpreter cannot correctly pad the new document
with placeholders. It still needs complete physical type/layout identity,
function ABI, instance and `BodyCore` joins, as well as relevant allocation
material. Lean computes a limited Rust ABI/unwind component, but its IDs are
not yet validated against fixed-interpreter physical pools. Foundation supports
no general trait-resolution or const-MIR evaluation algorithm. It rejects
coroutines, inlined frames, target features and caller-location tracking, plus
many MIR forms. The bridge must calculate every remaining answer in Lean before
claiming fixed-interpreter execution.

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

For one 134-byte concrete `[u16; 3]` source, three alternating sequential trials
used the same pinned release exporter binary, CPU 2 and one Lean thread. The
ordinary schema-12 export had median wall/CPU time 0.141958/0.134849 s and a
137,397-byte output. Foundation v1 had median wall/CPU time
0.037632/0.028979 s and a 7,822-byte output. Wall ranges were 0.136678–0.234222
and 0.035744–0.038428 s respectively. One ordinary trial saw 0.01 s selected
CPU steal; cgroup throttling deltas were zero. Raw timings, hashes and counters
are in ignored `scratch/performance/` in the measuring workspace. The ordinary
measurements vary substantially and these formats support different operations,
so this is an export-only comparison, not a claim of equivalent executions or
interpreter speedup.
