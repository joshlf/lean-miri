# duplicate_prefix VC generation

`VCGen.zero_test` checks the actual imported MIR switch for both successors.
`VCGen.prepared_root_call` uses the shared call rule to combine checked frame
preparation with a body contract. `VCGen.zero_count` checks the complete
prepared zero-count path under the memory and frame conditions of the pinned
proof. Its result includes the verified driver program, scoped `UBFree`,
`NormalPost` over the final machine state, and the stored true Boolean.

From the repository root, fetch the immutable proof input and run the check:

```bash
git fetch origin 7950c01b18013969c360df535b8b888dd6181dff
python3 tools/check-duplicate-prefix-vcgen.py
```

The checker builds the pinned client sources against the Lean interpreter in
this checkout and audits the new theorems' transitive axioms. A proof-only
patch makes the imported switch proof unfold the current control-flow
definitions. Build artifacts and logs go under
`scratch/duplicate-prefix-vcgen.*`.
