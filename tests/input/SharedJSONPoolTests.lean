import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def reject (value : Json) (label : String) (diagnostic : String := "") : IO Unit := do
  match decodeJson value.compress with
  | .ok _ => throw (IO.userError s!"accepted invalid {label}")
  | .error error =>
    check (diagnostic.isEmpty || error.contains diagnostic) s!"{label}: unexpected diagnostic {error}"

private def poolNames := #["initialization_ranges", "relocations", "statement_kinds", "source_infos"]

private def memory (id size image ranges relocations : Nat) : Json := Json.mkObj [
  ("allocation_id", toJson id), ("source_alloc_id", toJson (id + 1)),
  ("kind", .str "memory"), ("size_bytes", toJson size), ("align_bytes", toJson (1 : Nat)),
  ("mutability", .str "mutable"), ("byte_image_id", toJson image),
  ("initialization_ranges", toJson ranges), ("relocations", toJson relocations)]

def main : IO Unit := do
  let original ← must (Json.parse (← IO.FS.readFile "tests/input/fixtures/strict-unit.json"))
  let _ ← must (decodeJson original.compress)
  for name in poolNames do
    let fields ← must original.getObj?
    reject (Json.mkObj (fields.toList.filter (fun field => field.1 != name))) s!"missing {name} pool"
    reject (← must (set original name (.arr #[.bool false]))) s!"malformed unused {name} payload"
  let allocations ← must ((← must (original.getObjVal? "allocations")).getArr?)
  for name in #["initialization_ranges", "relocations"] do
    let bad ← must (set allocations[0]! name (toJson (999999 : Nat)))
    reject (← must (set original "allocations" (.arr (allocations.set! 0 bad)))) s!"dangling allocation {name} pool"

  let types ← must ((← must (original.getObjVal? "types")).getArr?)
  let attrs ← must (types[0]!.getObjVal? "source_layout")
  let decoded ← must (decodeJson original.compress)
  let some firstNode := decoded.document.types[0]? | throw (IO.userError "missing typed source declaration")
  let first := firstNode.sourceLayout
  check (!first.isUnsafeCell && first.captureNames.isNone && first.discriminants.isEmpty)
    "source declarations changed false, null or empty-array values"
  for invalid in #[.str "false", .null, toJson (0 : Nat)] do
    let badAttrs ← must (set attrs "is_unsafe_cell" invalid)
    let first ← must (set types[0]! "source_layout" badAttrs)
    reject (← must (set original "types" (.arr (types.set! 0 first)))) "malformed source declaration boolean"

  -- One mask is valid for a one-byte allocation and invalid for a two-byte one.
  -- Pooling must retain the allocation-size check at each use.
  let range ← must (Json.parse "{\"state\":\"initialized\",\"start_bytes\":0,\"end_bytes_exclusive\":1}")
  let source ← must (set original "byte_images" (.arr #[.str "00", .str "0000"]))
  let source ← must (set source "initialization_ranges" (.arr #[.arr #[range]]))
  let source ← must (set source "relocations" (.arr #[.arr #[]]))
  let valid ← must (set source "allocations" (.arr #[memory 0 1 0 0 0]))
  let _ ← must (decodeJson valid.compress)
  let invalid ← must (set source "allocations" (.arr #[memory 0 1 0 0 0, memory 1 2 1 0 0]))
  reject invalid "shared initialization mask in incompatible allocation" "initialization_ranges"

  -- Identical relocation metadata must be checked against each allocation's size.
  let range8 ← must (Json.parse "{\"state\":\"initialized\",\"start_bytes\":0,\"end_bytes_exclusive\":8}")
  let range4 ← must (Json.parse "{\"state\":\"initialized\",\"start_bytes\":0,\"end_bytes_exclusive\":4}")
  let relocation ← must (Json.parse "{\"storage_offset_bytes\":0,\"target\":0,\"target_offset_encoded_bytes\":\"0000000000000000\",\"immutable\":false,\"shared_ref\":false}")
  let source ← must (set original "byte_images" (.arr #[.str "0000000000000000", .str "00000000"]))
  let source ← must (set source "initialization_ranges" (.arr #[.arr #[range8], .arr #[range4]]))
  let source ← must (set source "relocations" (.arr #[.arr #[relocation]]))
  let valid ← must (set source "allocations" (.arr #[memory 0 8 0 0 0]))
  let _ ← must (decodeJson valid.compress)
  let invalid ← must (set source "allocations" (.arr #[memory 0 8 0 0 0, memory 1 4 1 1 0]))
  reject invalid "shared relocation in incompatible allocation" "relocations"
  IO.println "shared JSON pools: required tables, payload IDs and per-use allocation bounds passed"
