import Miri.Input.ConcreteEnumLayout

open Miri.ABI Miri.Input

private def target : RuntimeTargetDataLayout := {
  RuntimeTargetDataLayout.default with
  base := ⟨.little,.w64⟩
  i64Align := ⟨3⟩
  i128Align := ⟨4⟩ }

private def reprRust : ReprOptions := ⟨none,none,none,0,none,0⟩

private def integer (kind : Integer) (first last : Nat) : Except String LayoutData :=
  ConcreteLayout.scalarLayout target (.Initialized (value := .Int kind false)
    (validRange := ⟨BitVec.ofNat 128 first,BitVec.ofNat 128 last⟩))

private def cases : Except String (Array (String × LayoutData)) := do
  let bool ← integer .I8 0 1
  let u8 ← integer .I8 0 255
  let u32 ← integer .I32 0 (2^32-1)
  let u64 ← integer .I64 0 (2^64-1)
  let nonzero ← integer .I32 1 (2^32-1)
  let reference ← ConcreteLayout.scalarLayout target (.Initialized (value := .Pointer .ZERO)
    (validRange := ⟨1,BitVec.ofNat 128 (2^64-1)⟩))
  let boolean ← ConcreteEnumLayout.calculate target reprRust #[#[],#[bool]] #[0,1]
  let nonzeroOption ← ConcreteEnumLayout.calculate target reprRust #[#[],#[nonzero]] #[0,1]
  let referenceOption ← ConcreteEnumLayout.calculate target reprRust #[#[],#[reference]] #[0,1]
  let direct ← ConcreteEnumLayout.calculate target reprRust #[#[u64],#[u64]] #[0,1]
  match direct.variants with
  | .Multiple _ _ _ variants =>
    unless variants.all (fun variant => variant.backendRepr == direct.backendRepr && variant.size == direct.size) do
      throw "downcast scalar-pair variants must preserve the enum ABI"
  | _ => throw "direct scalar enum lost its variants"
  let c ← ConcreteEnumLayout.calculate target {reprRust with flagsBits := 1} #[#[u8],#[u64]] #[0,1]
  let signedRepr : ReprOptions := {reprRust with integer := some (.fixed (.known .i8) 8 true)}
  let signed ← ConcreteEnumLayout.calculate target signedRepr #[#[],#[]] #[-1,1]
  let unsignedRepr : ReprOptions := {reprRust with integer := some (.fixed (.known .u64) 64 false)}
  let unsigned ← ConcreteEnumLayout.calculate target unsignedRepr #[#[],#[]] #[0,2^63]
  let absent ← ConcreteEnumLayout.calculate target reprRust #[#[ConcreteLayout.neverLayout target],#[u32]] #[0,1]
  let partiallyInitialized ← ConcreteEnumLayout.calculate target reprRust #[#[ConcreteLayout.neverLayout target,u32],#[u8]] #[0,1]
  let range ← match signed.backendRepr with
    | .Scalar scalar => scalar.validRange target |>.mapError reprStr
    | _ => throw "signed enum lost scalar ABI"
  unless range == ⟨255,1⟩ do throw "signed enum wrapping validity range differs"
  match boolean.variants with
  | .Multiple _ (.Niche 1 0 0 start) _ _ =>
    unless start == 2 do throw "bool niche must preserve the pinned zero-selection exception"
  | _ => throw "Option<bool> lost its niche encoding"
  match nonzeroOption.variants with
  | .Multiple _ (.Niche 1 0 0 start) _ _ =>
    unless start == 0 do throw "Option<NonZeroU32> does not reserve zero"
  | _ => throw "Option<NonZeroU32> lost its niche encoding"
  unless absent.variants == .Single 1 do throw "uninhabited 1-ZST variant was not eliminated"
  return #[
    ("bool",boolean),("nonzero",nonzeroOption),("reference",referenceOption),
    ("direct",direct),("c",c),("signed",signed),("unsigned",unsigned),
    ("absent",absent),("partial",partiallyInitialized)]

def main : IO Unit := do
  let cases ← match cases with
    | .ok values => pure values
    | .error error => throw (IO.userError error)
  for (name,layout) in cases do
    let align ← match layout.align.abi.bytes with
      | .ok value => pure value
      | .error error => throw (IO.userError (toString error))
    IO.println s!"{name} {layout.size.bytes} {align}"
