import Miri.Input.Model
import Miri.Input.RuntimeArrayTypes
import Miri.Interpreter.BodyIdentity

namespace Miri.Input.SourceMir

structure Metadata extends BodyMetadata where
  instanceId : InstanceId
  promotedBodies : Array PromotedBody
  callSites : Array (Nat × MIR.Operand)

private def body (document : ImportDocument) (index : Nat) : Except String Body :=
  match document.bodies[index]? with
  | some value => pure value
  | none => .error "canonical body index is absent"

private def materialCallSites (mir : MIR.Body) : Array (Nat × MIR.Operand) := Id.run do
  let mut result := #[]
  for (block,index) in mir.basicBlocks.zipIdx do
    match block.terminator.kind with
    | .Call function .. | .TailCall function .. => result := result.push (index,function)
    | _ => pure ()
  return result

def metadata (document : ImportDocument) (index : Nat) : Except String Metadata := do
  let value ← body document index
  pure ⟨value.toBodyCore.toBodyMetadata,value.instanceId,value.promotedBodies,materialCallSites value.mir⟩

def resolveBody (document : ImportDocument) (index : Nat)
    (role : CompilerBodyRole := .runtime) : TypeArena.WorldM BodyCore := do
  let value ← match body document index with
    | .ok value => pure value | .error error => throw error
  unless value.sourceRole == role do throw "body compiler source role mismatch"
  pure value.toBodyCore

private def validateMaterialBodyInstance (world : RuntimeArrayTypes.World) (index : Nat) : Except String Unit := do
  let some source := world.metadata.source.bodies[index]? | throw "body source is absent"
  let some expected := world.metadata.source.instances[source.instanceId]?
    | throw "body instance source is absent"
  let expected ← InstanceArena.Key.ofSource world.arena expected.instanceKind expected.genericArgs
  let actual ← match ← world.instances.lookup source.instanceId with
    | .material key | .constructed key => pure key
  unless actual == expected do throw "body source differs from execution instance store"

def resolveBodyIdentity (identity : Miri.Interpreter.BodyIdentity) :
    RuntimeArrayTypes.CompilerM BodyCore := do
  let world ← get
  let index := identity.index
  let some source := world.metadata.source.bodies[index]? | throw "body identity is absent"
  unless source.sourceRole == .runtime do throw "CTFE body cannot enter runtime resolution"
  match validateMaterialBodyInstance world index with
  | .ok () => pure () | .error error => throw error
  RuntimeArrayTypes.liftType (resolveBody world.metadata.source index)

def metadataIdentity (identity : Miri.Interpreter.BodyIdentity) :
    RuntimeArrayTypes.CompilerM BodyMetadata := do
  let world ← get
  let index := identity.index
  let some source := world.metadata.source.bodies[index]? | throw "body identity is absent"
  unless source.sourceRole == .runtime do throw "CTFE body cannot enter runtime metadata"
  match validateMaterialBodyInstance world index with
  | .ok () => pure () | .error error => throw error
  pure source.toBodyCore.toBodyMetadata

end Miri.Input.SourceMir
