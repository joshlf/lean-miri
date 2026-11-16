import Miri.Input.Decoder
import Miri.Input.SourceAbiRuntime

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error reason => throw (IO.userError reason)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def setField (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  return Json.mkObj ((key,child) :: fields.toList.filter (·.1 != key))

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected source-material MIR input")
  let text ← IO.FS.readFile path
  let decoded ← must (decodeJson text)
  let document := decoded.document
  let some material := document.sourceAbi | throw (IO.userError "missing source ABI material")
  let raw ← must (Json.parse text)
  let source ← must (raw.getObjVal? "source_abi")
  let definitions ← must ((source.getObjVal? "definitions").bind Json.getArr?)
  let some selected := material.definitions.findSome? id
    | throw (IO.userError "control requires a concrete callable instance")
  let some row := definitions[selected.instanceId]? | throw (IO.userError "missing raw source signature")
  let reject (source : Json) (message : String) : IO Unit := do
    let modified ← must (setField raw "source_abi" source)
    check (!(decodeJson modified.compress).isOk) message
  let fields ← must raw.getObj?
  let missing := Json.mkObj (fields.toList.filter (·.1 != "source_abi"))
  check (!(decodeJson missing.compress).isOk) "missing source ABI material accepted"
  reject (← must (setField source "definitions" (.arr (definitions.push row))))
    "duplicate source instance signature accepted"
  let wrongIdentity ← must (setField row "instance_id" (toJson document.instances.size))
  reject (← must (setField source "definitions" (.arr (definitions.set! selected.instanceId wrongIdentity))))
    "out-of-bounds source instance accepted"
  let signature ← must (row.getObjVal? "signature")
  let wrongReturn ← must (setField signature "output" (toJson document.types.size))
  let wrongReturn ← must (setField row "signature" wrongReturn)
  reject (← must (setField source "definitions" (.arr (definitions.set! selected.instanceId wrongReturn))))
    "dangling source signature type accepted"
  let invalidUsage ← must (setField row "parameter_uses" (.arr #[toJson (16 : Nat)]))
  reject (← must (setField source "definitions" (.arr (definitions.set! selected.instanceId invalidUsage))))
    "unknown optimized-body usage bit accepted"
  let policy ← must (source.getObjVal? "policy")
  let policyFields ← must policy.getObj?
  let missingIncremental := Json.mkObj (policyFields.toList.filter (·.1 != "incremental"))
  reject (← must (setField source "policy" missingIncremental)) "missing incremental ABI policy accepted"
  let invalidAlignment ← must (setField policy "max_reliable_alignment" (toJson (3 : Nat)))
  reject (← must (setField source "policy" invalidAlignment)) "non-power-of-two ABI alignment accepted"
  let program ← must (lowerProgram document)
  let runtime ← must (RuntimeMetadata.ofDocument document |>.mapError toString)
  let _ ← must (SourceAbiRuntime.ofInstance ⟨runtime, program, none⟩ selected.instanceId #[])
  let context : CompilerFacts.Context := ⟨runtime, program, none⟩
  let layout ← must (runtime.lookup selected.signature.output |>.mapError toString)
  let layout := {layout with layout := {layout.layout with size := Miri.ABI.Size.ofBytes 32, backendRepr := .Memory (sized := true)}}
  let queries := {SourceAbiRuntime.queries context material.policy with
    lookup := fun _ => pure layout
    needsDrop := fun _ => throw "control: unexpected needsDrop"
    isFreeze := fun _ => throw "control: unexpected isFreeze"}
  let signature := {selected.signature with inputs := #[layout.ty], output := layout.ty, abi := .Rust}
  let definition := {selected with signature, parameterUses := #[1, 1], virtualCall := false, callerLocation := none}
  let compute (optimize incremental : Bool) := SourceAbi.compute
    {material.policy with optimize, incremental} runtime.target queries signature #[] (some definition) true
  check ((compute false false).isOk) "unoptimized ABI requested deduced-attribute queries"
  check ((compute true true).isOk) "incremental ABI requested deduced-attribute queries"
  check (!(compute true false).isOk) "optimized nonincremental ABI skipped deduced-attribute queries"
  let incomplete := {material with definitions := material.definitions.set! selected.instanceId none}
  let incompleteRuntime := {runtime with source := {document with sourceAbi := some incomplete}}
  check (!(SourceAbiRuntime.ofInstance ⟨incompleteRuntime, program, none⟩ selected.instanceId #[]).isOk)
    "missing concrete ABI source silently fell back to an answer table"
  IO.println "source ABI boundary: required material, dense identities, type references, usage bits and policy checked; missing source fails at demand"
