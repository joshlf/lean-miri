import Miri.Input.ConcreteCoroutineLayout
open Miri.Input Miri.ABI
private def target : RuntimeTargetDataLayout := {
  RuntimeTargetDataLayout.default with i64Align := ⟨3⟩, i128Align := ⟨4⟩ }
private def scalar (i : Integer) : Except String LayoutData := do
  let range ← WrappingRange.full i.size |>.mapError reprStr
  ConcreteLayout.scalarLayout target (.Initialized (value := .Int i false) (validRange := range))
private def cases : Array (Array Integer × Array Integer × Array (Array Nat) × Array (Array Nat)) := #[
  (#[],#[],#[#[],#[],#[]],#[]),
  (#[.I32,.I64],#[],#[#[],#[0],#[1]],#[#[],#[]]),
  (#[.I32,.I64],#[],#[#[],#[0],#[1]],#[#[1],#[0]]),
  (#[.I8,.I32,.I64],#[],#[#[],#[0,1],#[1,2]],#[#[],#[],#[]]),
  (#[.I128,.I32,.I64],#[.I64,.I8],#[#[],#[0],#[1],#[2]],#[#[1,2],#[0],#[0]])]
private def numbers (xs : Array Nat) : String :=
  "[" ++ String.intercalate ", " (xs.toList.map toString) ++ "]"
def main : IO Unit := do
  for index in Array.finRange cases.size do
    let (locals,upvars,variants,conflicts) := cases[index]
    let result : Except String LayoutData := do
      ConcreteCoroutineLayout.calculate target (← locals.mapM scalar) (← upvars.mapM scalar) variants conflicts
    let layout ← match result with | .ok value => pure value | .error err => throw (IO.userError err)
    let .Arbitrary offsets order := layout.fields | throw (IO.userError "outer fields")
    let align ← match layout.align.abi.bytes with | .ok value => pure value | .error err => throw (IO.userError (toString err))
    IO.println s!"case{index.val} {layout.size.bytes} {align} {numbers (offsets.map (·.bytes.toNat))} {numbers order}"
    let .Multiple _ .Direct _ variants := layout.variants | throw (IO.userError "variant layout")
    for i in Array.finRange variants.size do
      let variant := variants[i]
      IO.println s!"v{i.val} {variant.size.bytes} {numbers (variant.fieldOffsets.map (·.bytes.toNat))} {numbers variant.fieldsInMemoryOrder}"
