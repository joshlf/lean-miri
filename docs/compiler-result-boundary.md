# Compiler result boundary

An export captures one pinned rustc invocation. The interpreter uses its
concrete results for executable constants, layouts, function ABI and selected
instances. A changed program or compiler setting requires a new export.

Rustc results are keyed by the complete request: physical type or instance,
generic arguments, typing environment and, where applicable, projection or
call-site identity. Lean checks those keys and the result shape before use.
It may intern type syntax to form a request, but structural resemblance does
not authorize reusing a result for a new identity. A missing result stops the
demand explicitly.

The exporter includes evaluated concrete MIR constants, full canonical and
contextual field or variant layouts, instance and function-pointer ABIs, and
resolved call targets. An array or slice element layout may serve any element
index because rustc gives those homogeneous fields the same layout; other
fields require their own result. Type-level constant aliases also require an
exact rustc evaluation row before Lean can reify their value.

The export closes a finite set of reachable bodies and compiler queries.
Concrete Item, demanded FnPtr conversion and no-op DropGlue bodies come from rustc MIR,
with exact ABI rows. If execution first constructs an identity outside that
closure, the runtime cannot ask rustc for it and reports the missing body or
query. Neither a successful export nor one completed guest establishes closure
for arbitrary executions.
An array first constructed with a runtime count may likewise lack a layout row.
OS string allocation and array subslice require that typed layout; their
missing demand remains explicit because replacing it with untyped byte storage
has not been shown to preserve the pinned interpreter's effect order.

The decoded tables are immutable. Each interpreter execution owns its World
and any runtime memoization; mutable answers are never shared across runs.
The correctness boundary still includes rustc export coverage, decoding and
interpreter correspondence. See [STATUS.md](../STATUS.md) for validation gaps.
