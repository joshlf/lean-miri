import Miri.Input.Decoder
import Miri.Input.CallerLocationConstruction

open Lean Miri.Input Miri.Memory Miri.ABI
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def field [FromJson α] (value : Json) (name : String) : IO α :=
  must (value.getObjValAs? α name)

def main (args : List String) : IO Unit := do
  let [input,tracePath] := args | throw (IO.userError "expected source input and post-execution allocation trace")
  let decoded ← must (decodeJson (← IO.FS.readFile input))
  let document := decoded.document
  let runtime ← must (RuntimeMetadata.ofDocument document |>.mapError toString)
  let some reference := document.queries.primitives.callerLocationType |
    throw (IO.userError "caller-location primitive is absent")
  let reference ← must (runtime.lookup reference |>.mapError toString)
  let location ← must (runtime.pointee reference |>.mapError toString)
  let trace ← must (Json.parse (← IO.FS.readFile tracePath))
  check ((← field trace "schema") == ("post_execution_raw_ctfe_allocations_v1" : String)) "unexpected allocation trace"
  let rows : Array Json ← field trace "allocations"
  let policy := document.queries.session.locationDetail
  let mut compared := 0
  let mut filenames : Array Nat := #[]
  for row in rows do
    let relocations : Array Json ← field row "relocations"
    if (← field row "created_during_reference") &&
        (← field row "size_bytes") == location.layout.size.bytes.toNat && relocations.size == 1 then
      let some relocation := relocations[0]? | throw (IO.userError "trace relocation invariant")
      let raw : Nat ← field relocation "target_source_alloc_id"
      let some filename := rows.find? (fun candidate => candidate.getObjValAs? Nat "source_alloc_id" == .ok raw) |
        throw (IO.userError "relocation target is absent from generic trace")
      let filenameBytes ← must (decodeAllocationHex (← field filename "bytes"))
      let some id := AllocId.ofUInt64 (UInt64.ofNat raw) | throw (IO.userError "zero filename ID")
      let bytes ← must (decodeAllocationHex (← field row "bytes"))
      let mut matched := false
      for span in document.spans do
        let some name := document.files[span.expansionLocation.file]? | throw (IO.userError "missing expansion file")
        let name := if policy.file then name else "<redacted>"
        if name.toUTF8.data.push 0 == filenameBytes then
          let storage : Allocation CtfeProvenance Unit ← must
            (Allocation.tryNew location.layout.size location.layout.align.abi .Uninit
              (fun size _ => some (Array.replicate size.bytes.toNat 0)) |>.mapError toString)
          let allocation ← must (CallerLocationConstruction.initializeFields runtime location storage id name.toUTF8.size
            (if policy.line then span.expansionLocation.line else 0)
            (if policy.column then span.expansionLocation.column else 0))
          let actual ← must (allocation.inspectWithUninitAndPtrOutsideInterpreter 0 bytes.size |>.mapError toString)
          if actual == bytes then
            check ((← field row "align_bytes") == (← must (allocation.align.bytes |>.mapError reprStr)).toNat &&
              (← field row "mutability") == ("immutable" : String) && allocation.mutability == .Not)
              "caller allocation alignment or mutability differs from Miri"
            let pointers := allocation.provenanceMap.ptrs
            let some (offset,provenance) := pointers[0]? | throw (IO.userError "caller filename lost provenance")
            check (pointers.size == 1 && offset.bytes.toNat == (← field relocation "storage_offset_bytes") &&
              provenance.allocId == id && provenance.immutable == (← field relocation "immutable") &&
              provenance.sharedRef == (← field relocation "shared_ref")) "caller pointer provenance differs from Miri"
            let ranges : Array Json ← field row "initialization_ranges"
            for index in [:bytes.size] do
              let expected := ranges.any fun range =>
                range.getObjValAs? String "state" == .ok "initialized" &&
                (range.getObjValAs? Nat "start_bytes").toOption.any (· ≤ index) &&
                (range.getObjValAs? Nat "end_bytes_exclusive").toOption.any (index < ·)
              check ((← must (allocation.initializationMask.get (.ofBytes (UInt64.ofNat index)) |>.mapError reprStr)) == expected)
                "caller initialization mask differs from Miri"
            matched := true
            break
      check matched "new Miri allocation is not reproducible from finite expansion positions"
      check (!(← field filename "created_during_reference")) "ordinary filename bytes were not reused"
      filenames := filenames.push raw
      compared := compared + 1
  check (compared == 3 && filenames.all (· == filenames[0]?.getD 0))
    "expected three fresh roots sharing the existing ordinary filename allocation"
  let some filename := AllocId.ofUInt64 77 | throw (IO.userError "padding test identity")
  let padded := {location with layout := {location.layout with size := .ofBytes (location.layout.size.bytes + 8)}}
  let storage : Allocation CtfeProvenance Unit ← must
    (Allocation.tryNew padded.layout.size padded.layout.align.abi .Uninit
      (fun size _ => some (Array.replicate size.bytes.toNat 0)) |>.mapError toString)
  let allocation ← must (CallerLocationConstruction.initializeFields runtime padded storage filename 4 12 34)
  for index in [location.layout.size.bytes.toNat:allocation.byteSize.bytes.toNat] do
    check (!(← must (allocation.initializationMask.get (.ofBytes (UInt64.ofNat index)) |>.mapError reprStr)))
      "synthetic trailing padding was initialized"
  IO.println s!"caller allocation oracle: roots={compared}; bytes, initialization, provenance, alignment and filename reuse match Miri; synthetic trailing padding stays uninitialized"
