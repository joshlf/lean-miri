import Miri.Frontend.FoundationCompilerEntryProgram
import Miri.Input.Decoder

/-! Normal-runner input dispatch. Valid schema-12 inputs retain the existing
single decoder path. Foundation material produces a checked source-derived
ImportDocument and then uses the normal lowerer/preparation/interpreter. Unknown
source demands are errors, never a fallback to a special evaluator. -/
namespace Miri.Frontend.Foundation
open Lean

private def inputSchema (text : String) : Except String (Option String) :=
  Input.JsonReader.run (Input.JsonReader.object none fun schema key => do
    if key == "schema" then return some (← Input.JsonReader.string)
    Input.JsonReader.skipValue
    return schema) text

/-- Decode the ordinary input first, so successful ordinary runs incur no extra
schema scan or generic JSON tree. Only its decoder rejection activates the
foundation schema dispatch; malformed/unknown ordinary inputs retain that error. -/
def decodeRunnerInputProfiled (text : String) (profile : Options) : Except String Input.ExecutionInput :=
  match Input.decodeJsonProfiled text profile with
  | .ok input => .ok input
  | .error ordinaryError => do
    unless (inputSchema text).toOption == some (some "lean-miri-foundation") do throw ordinaryError
    let source ← (Json.parse text >>= decode).mapError fun error => s!"invalid foundation source: {error}"
    let document ← (restrictedCompilerEntryDocument source).mapError fun error =>
      s!"foundation compiler-entry Unsupported: {error}"
    return ⟨document⟩

end Miri.Frontend.Foundation
