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

## Normal execution path

`FoundationInput` decodes the finite document into typed source material and
constructs the initial input for the normal runner. The existing lowerer,
preparation, evaluator and finalizer execute it through the fixed interpreter.
A persistent `SourceCompilerWorld` belongs to that evaluation and retains the
typed definitions, generic MIR, type structure and target evidence. Runtime
queries share its canonical instance, body, type and ABI identities. Supported
queries derive missing rows on demand; they do not enumerate all substitutions
or consult a running compiler. No cache is shared between evaluations.

Free-function resolution checks the source declaration and full generic
arguments before interning an instance. Body loading substitutes the selected
source template and installs its actual body in the same World. Frame, span,
layout and ABI consumers read that current World rather than preparation-time
copies. Foreign-symbol lookup selects a source declaration before resolving the
selected callable. Unsupported selection, missing source and contradictory
identities remain errors.

The supported domain includes selected scalar and aggregate layouts, source
signatures, ordinary direct calls, required constants, closure and dynamic-object
material, and finite startup metadata. Compiler comparisons test these components;
they do not establish support for every Rust type, trait, constant or MIR form.
The normal custom-entry control reaches finalization. Ordinary std main has
advanced into its actual startup MIR but does not yet complete. Broader trait
selection, indirect calls, allocation identities and interpreter effects still
have unsupported cases. The current concrete stop and remaining work are tracked
in [STATUS.md](../STATUS.md).

The schema-12 route remains available for compiler-produced inputs. Its existing
answer tables are an input trust boundary, not evidence that the corresponding
foundation queries have been implemented. Unsupported foundation demands must
remain visible rather than falling back to those tables.

## Proof and trust boundary

rustc's MIR generation, compiler revision, target description and the exporter's
faithful encoding remain assumptions about the external Rust program. A Lean
theorem would then need to state the exact exported document, initial state,
external contracts and permitted choices, and cover every reachable permitted
finite prefix of the **fixed** interpreter. A successful export, decoder check,
concrete run or finite Miri comparison establishes
none of those universal claims. Missing semantics, query answers, overflow and
unsupported forms must stop with errors rather than successful execution.

## Measured export cost

For one 134-byte concrete `[u16; 3]` source, five alternating sequential trials
used the same pinned release exporter binary, CPU 2 and one Lean thread. The
ordinary schema-12 export had median wall/CPU time 0.130594/0.130036 s and a
137,397-byte output. Foundation v1 had median wall/CPU time
0.133806/0.130078 s and a 67,207-byte output. Wall ranges were 0.129520–0.210109
and 0.129057–0.155803 s respectively. One trial per format saw 0.01 s selected
CPU steal; cgroup throttling deltas were zero. Raw timings, hashes and counters
are in ignored `scratch/performance/export-00134f49/` in the measuring workspace. The ordinary
measurements vary substantially and these formats support different operations,
so this is an export-only comparison, not a claim of equivalent executions or
interpreter speedup.
