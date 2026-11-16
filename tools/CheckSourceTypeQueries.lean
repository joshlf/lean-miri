import Miri.Input.Decoder
import Miri.Input.ConcreteTypeQueries

open Lean Miri.Input

def main (args : List String) : IO UInt32 := do
  let [inputPath,oraclePath] := args
    | throw (IO.userError "usage: CheckSourceTypeQueries <fresh-source-input.json> <same-producer-oracle.json>")
  let .ok input ← decodeFile inputPath | throw (IO.userError "source input decode failed")
  let .ok runtime := RuntimeMetadata.ofDocument input.document | throw (IO.userError "target decode failed")
  let .ok oracle := Json.parse (← IO.FS.readFile oraclePath) | throw (IO.userError "oracle JSON is invalid")
  let .ok types := (oracle.getObjVal? "types").bind Json.getArr? | throw (IO.userError "oracle types absent")
  let booleanKeys := ["is_unsafe_cell","has_erasable_regions","is_c_void","is_simd","is_box",
    "is_global_box","is_dynamic","is_too_generic","is_monomorphic","is_monomorphic_enough",
    "is_like_maybe_dangling","is_x87_f80_raw","is_freeze","is_unpin","is_unsafe_unpin","needs_drop","opsem_inhabited","is_sized"]
  let mut checked := 0
  let mut failures := 0
  for value in types do
    let .ok id := (value.getObjVal? "type_id").bind Json.getNat? | throw (IO.userError "oracle type ID absent")
    let .ok expected := value.getObjVal? "booleans" | throw (IO.userError "oracle booleans absent")
    for key in booleanKeys do
      let .ok expected := (expected.getObjVal? key).bind Json.getBool? | throw (IO.userError s!"oracle boolean {key} absent")
      let actual := ConcreteTypeQueries.boolean runtime id key
      checked := checked + 1
      unless actual == .ok expected do
        failures := failures + 1
        IO.println s!"type={id} query={key} rustc={expected} Lean={reprStr actual}"
  IO.println s!"source type queries: compared={checked}, failures={failures}; finite compiler comparison only"
  return if checked > 0 && failures == 0 then 0 else 1
