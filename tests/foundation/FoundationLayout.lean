import Miri.Frontend.FoundationLayout

open Lean Miri.Frontend.Foundation

private def target (dataLayout := "e-i64:64-i128:128") (pointerSizeBits := 64) : Target :=
  { triple := "test", dataLayout, pointerSizeBits, endian := "little" }

private def expect (r : Except String FoundationLayout) (size align : Nat) : IO Unit := do
  match r with
  | .ok actual => unless actual == ⟨size, align⟩ do throw (IO.userError s!"wrong layout {repr actual}")
  | .error e => throw (IO.userError e)

private def fails (r : Except String FoundationLayout) : IO Unit := do
  match r with
  | .error _ => pure ()
  | .ok v => throw (IO.userError s!"unexpected layout {repr v}")

def main : IO Unit := do
  expect (layoutOf target (.primitive "bool" "")) 1 1
  expect (layoutOf target (.primitive "char" "")) 4 4
  expect (layoutOf target (.primitive "int" "i128")) 16 16
  expect (layoutOf (target "e") (.primitive "int" "i64")) 8 4
  expect (layoutOf (target "e-i64:64-i96:128") (.primitive "uint" "u128")) 16 16
  expect (layoutOf (target "e-i128:128-i64:64") (.primitive "uint" "u128")) 16 16
  expect (layoutOf (target "e-i16:32:64") (.array (.primitive "uint" "u16") 3)) 6 4
  expect (layoutOf (target "e" 32) (.primitive "uint" "usize")) 4 4
  expect (layoutOf target (.array (.primitive "uint" "u16") 0)) 0 2
  expect (layoutOf target (.tuple #[])) 0 1
  fails (layoutOf target (.array (.primitive "uint" "u8") (2 ^ 61)))
  fails (layoutOf target (.array (.tuple #[]) (2 ^ 64)))
  fails (layoutOf target (.tuple #[.primitive "uint" "u8"]))
  fails (layoutOf target (.primitive "float" "f32"))
  fails (layoutOf (target "e-i16:24") (.primitive "uint" "u16"))
  fails (layoutOf (target "e" 128) (.primitive "uint" "u8"))
  for (path, id, args, consts) in #[
      ("scratch/foundation-array.json", 2, #[some (ConcreteType.primitive "uint" "u16")], #[none, some 3]),
      ("scratch/foundation-concrete.json", 0, #[], #[])] do
    let raw ← IO.FS.readFile path
    let d ← match Json.parse raw >>= decode with
      | .ok d => pure d
      | .error e => throw (IO.userError e)
    expect (layoutOfType d id args consts) 6 2
    fails (layoutOfType d 999 args consts)
  IO.println "foundation layout: 20 checks passed (including fresh array/concrete exports)"
