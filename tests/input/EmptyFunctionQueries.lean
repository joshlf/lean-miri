import Miri.Input.Decoder
import Miri.Input.CompilerProviders

/-! Concrete provider checks complement the empty-function theorem's explicit
metadata premises; successful assertions are not a safety proof. -/
open Miri Miri.ABI Miri.Input

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "usage: EmptyFunctionQueries <exported empty_function.json>")
  let decoded ← decodeFile path
  let checked : Except String Unit := do
    let input ← decoded
    let program ← lowerProgram input.document
    let compiler ← CompilerProviders.prepare program
    let definition ← compiler.program.rootDefinitionId 0
    let function ← CompilerInstance.item compiler.program.input.instances definition #[]
    let loaded ← CallResolution.loadedBodyOfInstance compiler.lifecycle.calls.calls function
    let abi ← CompilerInstanceAbi.abiOfInstance compiler.lifecycle.instances function #[]
    let unit ← CompilerPrimitiveFacts.unitLayout compiler.runtime
    unless decide (abi.args = #[] ∧ abi.fixedCount = 0 ∧ abi.ret.mode = .Ignore ∧ abi.cVariadic = false ∧
        abi.ret.layout = unit) do
      throw "empty_function source ABI is not the expected () -> () ABI"
    unless decide (unit.layout.size = Size.ZERO ∧ unit.layout.align.abi = Align.ONE ∧
        unit.layout.backendRepr = .Memory (sized := true) ∧ unit.layout.isSized = true ∧
        unit.layout.fields = .Arbitrary #[] #[] ∧ unit.layout.variants = .Single 0) do
      throw "empty_function source unit layout differs from the required layout"
    unless loaded.body.argumentCount == 0 && loaded.body.locals == #[unit.ty] do
      throw "empty_function concrete MIR does not use its computed unit return type"
    let facts := compiler.lifecycle.calls.symbols.facts
    unless (← CompilerFacts.boolean facts.context unit.ty "is_freeze") do
      throw "empty_function source unit Freeze query returned false"
    unless (← CompilerFacts.boolean facts.context unit.ty "opsem_inhabited") do
      throw "empty_function source unit inhabited query returned false"
    unless decide ((← CompilerFactAdapters.validityKind facts unit.ty) =
        .aggregate false false false) do
      throw "empty_function source unit validity query differs from aggregate validity"
  match checked with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "empty_function source ABI/layout/trait providers checked; safety=not_evaluated"
