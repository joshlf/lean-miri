# duplicate_prefix VC generation

`VCGen.zero_test` checks the actual imported MIR switch for both successors.
`VCGen.prepared_root_call` uses the shared call rule to combine checked frame
preparation with a body contract. `VCGen.zero_count` checks the complete
prepared zero-count path under the memory and frame conditions of the pinned
proof. Its result includes the verified driver program, scoped `UBFree`,
`NormalPost` over the final machine state, and the stored true Boolean.

`VCGen.ordinary_call` covers every `UInt64` count in PR #12's
`OrdinaryInput` domain. It composes the real resolved frame preparation
with the prepared body's `UBFree` and `NormalPost`, then checks the call
and the finite body program against the same final machine state. This
uses the existing source-level trace proof for the memory and pointer
obligations.

From the repository root, fetch the immutable proof input and run the check:

```bash
git fetch origin 7950c01b18013969c360df535b8b888dd6181dff
python3 tools/check-duplicate-prefix-vcgen.py
python3 tools/check-duplicate-prefix-vcgen.py --all-counts
```

The checker builds the pinned client sources against the Lean interpreter in
this checkout and audits the new theorems' transitive axioms. The all-counts
mode checks the larger ordinary-input proof closure. A proof-only patch
makes the imported proofs unfold the current control-flow and driver
definitions. Build artifacts and logs go under
`scratch/duplicate-prefix-vcgen.*`.
