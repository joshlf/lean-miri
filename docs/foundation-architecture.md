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
definition graphs, the target data layout, and generic clauses. IDs name rows
within the document. Type and const parameters retain rustc's shared parameter
indices. It does not enumerate substitutions or serialize layout, ABI, predicate,
instance or interpreter query-answer catalogs. Unsupported source constructs
abort export. The producer and decoder reject a different pinned rustc commit.

In Lean, `Foundation.decode` loads this finite document, `typeExpr` resolves a
requested type, `instantiate` substitutes a requested type/const argument tuple,
and `checkEnvironment` checks the known `Sized`, `Copy` and `usize` obligations
for the restricted structural type domain. Each is a pure function of the
document and explicit arguments. Unknown obligations are errors. The existing
fixed interpreter also now computes canonical nested-array layouts on demand
from its imported type graph, with explicit cycle, overflow and contradiction
errors.

The restricted foundation evaluator exercises identity and array-body fixtures
after those checks. It accepts only fully initialized scalar and aggregate
values with a single straight-line block and whole-local assignments. It is a
fixture validator, **not** the fixed Miri interpreter and not a safety proof.
The current schema-12 input still feeds the fixed interpreter. The migration is
complete only when the fixed interpreter receives its required data from the
finite foundation material and Lean computes its remaining compiler queries.
The active missing work is tracked in [STATUS.md](../STATUS.md).

A direct bridge to the fixed interpreter cannot correctly pad the new document
with placeholders. Its preparation requires complete target alignment and
pointer evidence, physical type layouts, function ABI and instance metadata,
source MIR details, and relevant allocation material. Foundation currently
omits function signatures and many MIR forms, and supports no general ABI or
trait-resolution algorithm. It rejects frame-entry features that the restricted
domain cannot reproduce, including nonempty or unknown `required_consts`,
coroutines, inlined frames, target features and caller-location tracking. The
next bridge must retain the remaining finite source facts and compute the
needed answers in Lean before claiming fixed-interpreter execution.

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
ordinary schema-12 export had median wall/CPU time 0.220478/0.178710 s and a
137,397-byte output. Foundation v1 had median wall/CPU time
0.062050/0.051717 s and a 955-byte output. Wall ranges were 0.167829–0.236291
and 0.038194–0.125017 s respectively. One trial in each mode saw 0.01 s
selected CPU steal; cgroup throttling deltas were zero. Raw timings, hashes and
counters are in ignored `scratch/performance/` in the measuring workspace. The
shared-host spread is substantial and these formats currently support different
operations, so this is an export-only comparison, not a claim of equivalent
executions or interpreter speedup.
