import Miri.Input.ConcreteAggregateLayout
open Miri.Input Miri.ABI

private def target : RuntimeTargetDataLayout := {
  RuntimeTargetDataLayout.default with i64Align := ⟨3⟩, i128Align := ⟨4⟩ }

private def field (code : Nat) : Except String LayoutData := do
  if code == 6 then return ConcreteLayout.unitLayout target
  if code == 7 then
    let base ← ConcreteLayout.scalarLayout target (.Initialized (value := .Int .I8 false) (validRange := ⟨0,255⟩))
    return {ConcreteLayout.unitLayout target false with
      fields := .Array (Size.ofBytes 1) 0
      randomizationSeed := base.randomizationSeed }
  let (kind,first,last) ← match code with
    | 0 => pure (Integer.I8,0,255)
    | 1 => pure (.I8,0,1)
    | 2 => pure (.I16,0,65535)
    | 3 => pure (.I32,0,2^32-1)
    | 4 => pure (.I32,1,2^32-1)
    | 5 => pure (.I64,0,2^64-1)
    | _ => throw "unknown randomized-layout fixture field"
  ConcreteLayout.scalarLayout target (.Initialized (value := .Int kind false)
    (validRange := ⟨BitVec.ofNat 128 first,BitVec.ofNat 128 last⟩))

private def numbers (values : Array Nat) : String :=
  "[" ++ String.intercalate ", " (values.toList.map toString) ++ "]"

private def patterns : Array (Array Nat) := #[
  #[0,1,3,1,5,2],#[5,0,4,3,0],#[6,3,1,6,5,1],#[0,1,3,1,5,7]]

def main : IO Unit := do
  for seed in #[0,1,42,2^64-1] do
    for pattern in Array.finRange patterns.size do
      for mode in [:3] do
        if pattern.val == 3 && mode != 1 then continue
        for pack in #[0,2] do
          for requested in #[0,16] do
            let result : Except String LayoutData := do
              let repr : ReprOptions := {
                integer := none
                flagsBits := 16
                fieldShuffleSeed := seed
                packBytes := if pack == 0 then none else some pack
                alignBytes := if requested == 0 then none else some requested
                scalableElement := none }
              let fields ← patterns[pattern].mapM field
              let kind := match mode with
                | 0 => ConcreteLayout.StructKind.alwaysSized
                | 1 => .maybeUnsized
                | _ => .prefixed (Size.ofBytes 4) ⟨3⟩
              ConcreteLayout.univariant target repr fields kind
            let layout ← match result with
              | .ok value => pure value
              | .error error => throw (IO.userError error)
            unless !layout.reprC && !layout.uninhabited && layout.variants == .Single 0 do
              throw (IO.userError "randomized aggregate fixture properties differ")
            let .Memory (sized := sized) := layout.backendRepr
              | throw (IO.userError "randomized aggregate unexpectedly has scalar ABI")
            let .Arbitrary offsets order := layout.fields
              | throw (IO.userError "randomized aggregate field shape differs")
            let output : Except String String := do
              let align ← layout.align.abi.bytes |>.mapError toString
              let unadjusted ← layout.unadjustedAbiAlign.bytes |>.mapError toString
              let maxRepr ← layout.maxReprAlign.mapM fun a => a.bytes |>.mapError toString
              let niche ← match layout.largestNiche with
                | none => pure "none"
                | some n => do
                  let size ← n.value.size target |>.mapError reprStr
                  pure s!"{n.offset.bytes},{size.bytes},{n.validRange.start.toNat},{n.validRange.end.toNat}"
              pure s!"a {seed} {pattern.val} {mode} {pack} {requested} {layout.size.bytes} {align} {unadjusted} {maxRepr.getD 0} {layout.randomizationSeed} {sized} {numbers (offsets.map (·.bytes.toNat))} {numbers order} {niche}"
            match output with
            | .ok line => IO.println line
            | .error error => throw (IO.userError error)
