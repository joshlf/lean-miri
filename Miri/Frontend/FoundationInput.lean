import Miri.Frontend.FoundationEntrySeed
import Miri.Input.Decoder

/-! Transitional normal-runner input dispatch while general foundation entry
assembly is incomplete. Valid schema-12 inputs retain the existing
single decoder path. Foundation material produces a checked source-derived
ImportDocument and then uses the normal lowerer/preparation/interpreter. Unknown
source demands are errors, never a fallback to a special evaluator. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Decoder handoff preserves the single source World and its derived startup
memo. Recreating it from the document would discard derivation provenance. -/
structure RunnerInput where
  document : Input.ImportDocument
  initialWorld : Option Input.SourceCompilerWorld.World

private def inputSchema (text : String) : Except String (Option String) :=
  Input.JsonReader.run (Input.JsonReader.object none fun schema key => do
    if key == "schema" then return some (← Input.JsonReader.string)
    Input.JsonReader.skipValue
    return schema) text

/-- Decode the ordinary input first, so successful ordinary runs incur no extra
schema scan or generic JSON tree. Only its decoder rejection activates the
foundation schema dispatch; malformed/unknown ordinary inputs retain that error. -/
def decodeRunnerInputProfiled (text : String) (profile : Options) : Except String RunnerInput :=
  match Input.decodeJsonProfiled text profile with
  | .ok input => .ok ⟨input.document,none⟩
  | .error ordinaryError => do
    unless (inputSchema text).toOption == some (some "lean-miri-foundation") do throw ordinaryError
    let source ← (Json.parse text >>= decode).mapError fun error => s!"invalid foundation source: {error}"
    let world ← (compilerEntrySeed source).mapError fun error =>
      s!"foundation compiler-entry Unsupported: {error}"
    return ⟨world.canonical,some world⟩

end Miri.Frontend.Foundation
