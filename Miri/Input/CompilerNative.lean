import Miri.Input.EvalNativeConstruction
import Miri.Input.CompilerProviders
import Miri.Input.RuntimeEffectfulLayout
import Miri.Interpreter.NativeAbi

/-! Native libffi compiler queries from native_lib/mod.rs:367–435. Shape is
actual compiler ADT/tuple evidence, not diagnostic spelling or ABI size. -/
namespace Miri.Input.CompilerNative
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error reason => throw (.callback s!"native compiler query unavailable: {reason}")

private def sourceShape (p : CompilerProviders.Prepared)
    (layout : LocalLayout) : TypeArena.WorldM Native.TypeShape := do
  let world ← get
  let constructor ← match ← world.lookupType layout.ty with
    | .constructed key => pure key
    | .material node => do
      let some key ← world.materialKey node | throw "native source constructor unavailable"
      pure key
  match constructor with
  | .tuple elements => pure (if elements.isEmpty then .emptyTuple else .other)
  | .adt .. =>
    let declaration ← RuntimeMetadata.adtDeclarationInWorld p.runtime layout.ty
    let reprC := declaration.representation.c
    let isEnum := declaration.kind == .enumKind
    let isStruct := declaration.kind == .structKind
    if let .Scalar .. := layout.layout.backendRepr then return .adt isEnum isStruct reprC #[]
    if !isStruct || !reprC then return .adt isEnum isStruct reprC #[]
    let fields ← (declaration.fields.filter (·.variantIndex == 0)).mapM fun field =>
      RuntimeMetadata.fieldTypeInWorld p.runtime layout.ty 0 field.fieldIndex
    pure (.adt isEnum isStruct reprC fields)
  | _ => pure .other

def abiQueries (p : CompilerProviders.Prepared) (arrays : RuntimeArrayQueries.Access S)
    (_provider : RuntimeEffectfulLayout.Provider S := RuntimeEffectfulLayout.unavailable) : NativeAbi.Queries S C :=
  { typeShape := fun _ layout => RuntimeArrayQueries.perform arrays (sourceShape p layout)
    layoutOf := fun _ ty => return .ok (← RuntimeArrayQueries.perform arrays (RuntimeMetadata.layoutInWorld p.runtime ty)) }

def make (p : CompilerProviders.Prepared)
    (arrays : RuntimeArrayQueries.Access (NativeMachine.State MiriMemoryKind U))
    (provider : RuntimeEffectfulLayout.Provider (NativeMachine.State MiriMemoryKind U) := RuntimeEffectfulLayout.unavailable) :
    EvalNativeConstruction.Compiler U C where
  typeShape := (abiQueries p arrays provider).typeShape
  layoutOf := (abiQueries p arrays provider).layoutOf
end Miri.Input.CompilerNative
