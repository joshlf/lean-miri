import Miri.Input.ConcreteAggregateLayout

namespace Miri.Input.ConcreteCoroutineLayout
open Miri.ABI

private inductive Eligibility where
  | unassigned
  | assigned (variant : Nat)
  | ineligible (prefixField : Option Nat)
  deriving BEq

/-- Pinned rustc_abi coroutine overlap assignment and prefix/variant layout.
Saved-slot types include the compiler's MaybeUninit wrapping. -/
def calculate (target : RuntimeTargetDataLayout) (locals prefixTypes : Array LayoutData)
    (variantFields conflicts : Array (Array Nat)) : Except String LayoutData := do
  if variantFields.isEmpty then throw "coroutine has no reserved variants"
  let variantFields ← variantFields.mapM fun fields => fields.mapM fun slot => do
    if h : slot < locals.size then pure (⟨slot,h⟩ : Fin locals.size)
    else throw "coroutine variant references missing saved slot"
  let conflicts ← conflicts.mapM fun fields => do
    let mut previous := none
    let mut result := #[]
    for slot in fields do
      if let some old := previous then
        unless old < slot do throw "coroutine storage-conflict row is not strictly ordered"
      previous := some slot
      if h : slot < locals.size then result := result.push (⟨slot,h⟩ : Fin locals.size)
      else throw "coroutine storage conflict references missing saved slot"
    pure result
  let conflicts : Vector (Array (Fin locals.size)) locals.size ←
    if h : conflicts.size = locals.size then pure ⟨conflicts,h⟩
    else throw "coroutine storage-conflict matrix height mismatch"
  let mut assignments : Vector Eligibility locals.size := Vector.replicate _ .unassigned
  let mut ineligible : Vector Bool locals.size := Vector.replicate _ false
  for variant in Array.finRange variantFields.size do
    for slot in variantFields[variant] do
      match assignments.get slot with
      | .unassigned => assignments := assignments.set slot.val (.assigned variant.val) slot.isLt
      | .assigned _ =>
        ineligible := ineligible.set slot.val true slot.isLt
        assignments := assignments.set slot.val (.ineligible none) slot.isLt
      | .ineligible _ => pure ()
  for a in Array.finRange locals.size do
    let countA := (conflicts.get a).size
    if ineligible.get a then continue
    for b in conflicts.get a do
      if ineligible.get b || assignments.get a == assignments.get b then continue
      let remove := if countA > (conflicts.get b).size then a else b
      ineligible := ineligible.set remove.val true remove.isLt
      assignments := assignments.set remove.val (.ineligible none) remove.isLt
  let mut usedVariants : Array Nat := #[]
  for assignment in assignments.toArray do
    if let .assigned variant := assignment then
      unless usedVariants.contains variant do usedVariants := usedVariants.push variant
  if usedVariants.size < 2 then
    assignments := Vector.replicate _ (.ineligible none)
    ineligible := Vector.replicate _ true
  let promoted := (Array.finRange locals.size).filter (ineligible.get ·)
  for index in Array.finRange promoted.size do
    let slot := promoted[index]
    assignments := assignments.set slot.val (.ineligible (some index.val)) slot.isLt

  let tagIndex := prefixTypes.size
  let lastDiscriminant := variantFields.size-1
  let integer := Integer.fitUnsigned (BitVec.ofNat 128 lastDiscriminant)
  let tag := Scalar.Initialized (value := .Int integer false)
    (validRange := ⟨0,BitVec.ofNat 128 lastDiscriminant⟩)
  let tagLayout ← ConcreteLayout.scalarLayout target tag
  let prefixFields := prefixTypes.push tagLayout ++ promoted.map (locals[·])
  let repr : ReprOptions := ⟨none,none,none,0,none,0⟩
  let prefixLayout ← ConcreteLayout.univariant target repr prefixFields .alwaysSized
  let .Arbitrary prefixOffsets prefixOrder := prefixLayout.fields
    | throw "coroutine prefix field layout invariant"
  let outerCount := tagIndex+1
  let outerFields := FieldsShape.Arbitrary (prefixOffsets.extract 0 outerCount)
    (prefixOrder.filter (· < outerCount))
  let promotedOffsets := prefixOffsets.extract outerCount prefixOffsets.size
  let promotedOrder := (prefixOrder.filter (· ≥ outerCount)).map (·-outerCount)
  let mut promotedMemoryIndex := Array.replicate promotedOrder.size 0
  for index in Array.finRange promotedOrder.size do
    let field := promotedOrder[index]
    if bound : field < promotedMemoryIndex.size then
      promotedMemoryIndex := promotedMemoryIndex.set field index.val bound
    else throw "coroutine promoted memory permutation invariant"

  let mut size := prefixLayout.size
  let mut align := prefixLayout.align
  let mut layouts : Array VariantLayout := #[]
  for variantIndex in Array.finRange variantFields.size do
    let fields := variantFields[variantIndex]
    let mut variantOnly := #[]
    for slot in fields do
      match assignments.get slot with
      | .assigned owner =>
        unless owner == variantIndex.val do throw "coroutine saved-slot variant assignment invariant"
        variantOnly := variantOnly.push locals[slot]
      | .ineligible _ => pure ()
      | .unassigned => throw "coroutine saved-slot assignment invariant"
    let variant ← ConcreteLayout.univariant target repr variantOnly
      (.prefixed prefixLayout.size prefixLayout.align.abi)
    let .Arbitrary offsets order := variant.fields
      | throw "coroutine variant field layout invariant"
    let mut memoryIndex := Array.replicate order.size 0
    for index in Array.finRange order.size do
      let field := order[index]
      if bound : field < memoryIndex.size then
        memoryIndex := memoryIndex.set field index.val bound
      else throw "coroutine variant memory permutation invariant"
    let mut combinedOrder : Array (Option Nat) := Array.replicate (promotedMemoryIndex.size+memoryIndex.size) none
    let mut combinedOffsets := #[]
    let mut nextVariantOnly := 0
    for fieldIndex in Array.finRange fields.size do
      let slot := fields[fieldIndex]
      let (offset,index) ← match assignments.get slot with
        | .unassigned => throw "coroutine saved-slot assignment invariant"
        | .assigned _ => do
          let some offset := offsets[nextVariantOnly]?
            | throw "coroutine variant-only field offset invariant"
          let some memory := memoryIndex[nextVariantOnly]?
            | throw "coroutine variant-only memory index invariant"
          nextVariantOnly := nextVariantOnly+1
          pure (offset,promotedMemoryIndex.size+memory)
        | .ineligible position => do
          let some position := position | throw "coroutine promoted field assignment invariant"
          let some offset := promotedOffsets[position]?
            | throw "coroutine promoted field offset invariant"
          let some memory := promotedMemoryIndex[position]?
            | throw "coroutine promoted memory index invariant"
          pure (offset,memory)
      if bound : index < combinedOrder.size then
        combinedOrder := combinedOrder.set index (some fieldIndex.val) bound
      else throw "coroutine combined memory permutation invariant"
      combinedOffsets := combinedOffsets.push offset
    let variant := {variant with fields := .Arbitrary combinedOffsets (combinedOrder.filterMap id)}
    size := if size.bytes < variant.size.bytes then variant.size else size
    align := align.max variant.align
    layouts := layouts.push (← VariantLayout.fromLayout variant |>.mapError reprStr)
  size ← size.alignTo align.abi |>.mapError toString
  let _ ← ConcreteLayout.checkedSize target size.bytes.toNat
  return {
    variants := .Multiple tag .Direct tagIndex layouts
    fields := outerFields
    backendRepr := .Memory (sized := true)
    largestNiche := none
    uninhabited := prefixLayout.uninhabited || layouts.all (·.uninhabited)
    size
    align
    maxReprAlign := none
    unadjustedAbiAlign := align.abi
    reprC := false
    randomizationSeed := 0 }

end Miri.Input.ConcreteCoroutineLayout
