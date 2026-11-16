import Miri.Input.Model.Types
import Miri.Input.JsonReader

namespace Miri.Input.SourceCastTargetsCodec
open JsonReader

def parse : Parser SourceCastTarget := do
  let (kind, input, target) ← object (none, none, none) fun (kind, input, target) key => do
    match key with
    | "kind" => return (some (← string), input, target)
    | "input_type" => return (kind, some (← natural), target)
    | "instance_id" => return (kind, input, some (← nullable natural))
    | _ => skipValue; return (kind, input, target)
  let input ← required input "input_type"
  let target ← required target "instance_id"
  match ← required kind "kind" with
  | "function_pointer" => return .functionPointer input target
  | "closure_once" =>
    let some target := target | fail "closure cast requires a concrete FnOnce target"
    return .closureOnce input target
  | _ => fail "unknown source cast target kind"

def validate (types : Array TypeNode) (targets : Array SourceCastTarget) : Except String Unit := do
  let mut seen : Array (Bool × DefinitionRef × Array Miri.MIR.GenericArg) := #[]
  for target in targets do
    let (closure, input) := match target with
      | .functionPointer input _ => (false, input)
      | .closureOnce input _ => (true, input)
    let some source := types[input]? | throw "source_cast_targets: missing source type"
    let key ← match source.shape with
      | .functionDefinition definition args _ _ =>
        if closure then throw "closure target attached to a function definition"
        pure (false, definition, args)
      | .closure definition args _ =>
        unless closure do throw "function target attached to a closure"
        pure (true, definition, args)
      | _ => throw "source_cast_targets: source is not a function definition or closure"
    if seen.contains key then throw "duplicate concrete source cast target"
    seen := seen.push key

end Miri.Input.SourceCastTargetsCodec
