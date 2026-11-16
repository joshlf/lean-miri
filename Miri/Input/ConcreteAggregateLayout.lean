import Miri.Input.Model
import Miri.ABI.Layout
import Miri.Input.ConcreteFieldShuffle

namespace Miri.Input.ConcreteLayout
open Miri.ABI

inductive StructKind where
  | alwaysSized
  | maybeUnsized
  | prefixed (size : Size) (align : Align)
  deriving BEq

def checkedSize (target : RuntimeTargetDataLayout) (bytes : Nat) : Except String Size := do
  unless bytes < target.objSizeBound.toNat do throw "type exceeds target object size bound"
  pure (Size.ofBytes (UInt64.ofNat bytes))

def nicheAvailable (target : RuntimeTargetDataLayout) (niche : Niche) : Except String Nat := do
  let size ← niche.value.size target |>.mapError toString
  let modulus := 2 ^ (size.bytes.toNat * 8)
  pure ((niche.validRange.start.toNat + modulus - (niche.validRange.end.toNat + 1)) % modulus)

def nicheFromScalar (target : RuntimeTargetDataLayout) (offset : Size) (scalar : Scalar) :
    Except String (Option Niche) := do
  let .Initialized (value := value) (validRange := range) := scalar | return none
  let niche : Niche := ⟨offset,value,range⟩
  return if (← nicheAvailable target niche) > 0 then some niche else none

def nicheReserve (target : RuntimeTargetDataLayout) (niche : Niche) (count : Nat) :
    Except String (Option (Nat × Scalar)) := do
  if count == 0 then throw "zero niche reservation"
  if count > (← nicheAvailable target niche) then return none
  let size ← niche.value.size target |>.mapError toString
  let modulus := 2 ^ (size.bytes.toNat * 8)
  let first := niche.validRange.start.toNat
  let last := niche.validRange.end.toNat
  let moveStart : Bool ← if count == 1 && !(first == 0 && last == 1) then do
      let nextUp ← size.signExtend (BitVec.ofNat 128 (last+1)) |>.mapError toString
      let nextDown ← size.signExtend (BitVec.ofNat 128 ((first+modulus-1)%modulus)) |>.mapError toString
      pure (nextDown.natAbs ≤ nextUp.natAbs)
    else if first > last then pure false
    else if first ≤ modulus-1-last then pure (count ≤ first)
    else pure (let finish := (last+count)%modulus; 1 ≤ finish && finish ≤ last)
  if moveStart then
    let start := (first+modulus-count)%modulus
    return some (start,.Initialized (value := niche.value) (validRange := ⟨BitVec.ofNat 128 start,niche.validRange.end⟩))
  let start := (last+1)%modulus
  return some (start,.Initialized (value := niche.value) (validRange := ⟨niche.validRange.start,BitVec.ofNat 128 ((last+count)%modulus)⟩))

def scalarLayout (target : RuntimeTargetDataLayout) (scalar : Scalar) : Except String LayoutData := do
  let size ← scalar.size target |>.mapError reprStr
  let align ← scalar.defaultAlign target |>.mapError reprStr
  let range ← scalar.validRange target |>.mapError reprStr
  let code := match scalar.primitive with | .Int _ true => 1 | .Int _ false => 2 | .Float _ => 3 | .Pointer _ => 4
  let rotate := fun n : Nat => UInt64.ofNat ((n % 2^64)/2^16 + (n % 2^16)*2^48)
  return {
    fields := .Primitive, variants := .Single 0, backendRepr := .Scalar scalar
    largestNiche := ← nicheFromScalar target Size.ZERO scalar, uninhabited := false
    align, size, maxReprAlign := none, unadjustedAbiAlign := align.abi, reprC := false
    randomizationSeed := size.bytes + UInt64.ofNat (code*2^32) + rotate range.start.toNat + rotate range.end.toNat }

def scalarPair (target : RuntimeTargetDataLayout) (a b : Scalar) : Except String LayoutData := do
  let aa ← a.defaultAlign target |>.mapError reprStr
  let ba ← b.defaultAlign target |>.mapError reprStr
  let align := aa.abi.max ba.abi |>.max target.aggregateAlign
  let aSize ← a.size target |>.mapError reprStr
  let bSize ← b.size target |>.mapError reprStr
  let offset ← aSize.alignTo ba.abi |>.mapError toString
  let size ← checkedSize target (offset.bytes.toNat+bSize.bytes.toNat)
  let size ← size.alignTo align |>.mapError toString
  let an ← nicheFromScalar target Size.ZERO a
  let bn ← nicheFromScalar target offset b
  let niche ← match an,bn with
    | none,n | n,none => pure n
    | some a,some b => pure (if (← nicheAvailable target a) ≥ (← nicheAvailable target b) then some a else some b)
  return {
    fields := .Arbitrary #[Size.ZERO,offset] #[0,1], variants := .Single 0
    backendRepr := .ScalarPair (a := a) (b := b) (bOffset := offset), largestNiche := niche, uninhabited := false
    align := .new align, size, maxReprAlign := none, unadjustedAbiAlign := align
    reprC := false, randomizationSeed := aSize.bytes+bSize.bytes }

def neverLayout (target : RuntimeTargetDataLayout) : LayoutData := {
  fields := .Primitive, variants := .Empty, backendRepr := .Memory (sized := true)
  largestNiche := none, uninhabited := true, align := .new target.i8Align
  size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := target.i8Align
  reprC := false, randomizationSeed := 0 }

def unitLayout (target : RuntimeTargetDataLayout) (sized : Bool := true) : LayoutData := {
  fields := .Arbitrary #[] #[], variants := .Single 0, backendRepr := .Memory (sized := sized)
  largestNiche := none, uninhabited := false, align := .new target.i8Align
  size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := target.i8Align
  reprC := false, randomizationSeed := 0 }

private def univariantBiased (target : RuntimeTargetDataLayout) (repr : ReprOptions)
    (fields : Array LayoutData) (kind : StructKind) (endBias : Bool) : Except String LayoutData := do
  let packed ← repr.packBytes.mapM fun bytes => Align.fromBytes (UInt64.ofNat bytes) |>.mapError toString
  let reprAlign ← repr.alignBytes.mapM fun bytes => Align.fromBytes (UInt64.ofNat bytes) |>.mapError toString
  let mut align := if packed.isSome then target.i8Align else target.aggregateAlign
  let mut maxReprAlign := reprAlign
  let endIndex := if kind == .maybeUnsized then fields.size-1 else fields.size
  let mut order := Array.finRange fields.size
  let fieldSeed := (fields.extract 0 endIndex).foldl (fun s f => s+f.randomizationSeed) (0 : UInt64)
  unless repr.inhibitStructFieldReordering || fields.size ≤ 1 do
    if repr.canRandomizeTypeLayout then
      order := (← ConcreteFieldShuffle.shuffle (order.extract 0 endIndex) (fieldSeed+UInt64.ofNat repr.fieldShuffleSeed)) ++ order.extract endIndex order.size
    else
      let mut maxAlign := 1
      let mut maxNiche := 0
      for field in fields.extract 0 endIndex do
        maxAlign := max maxAlign (← field.align.abi.bytesNat |>.mapError toString)
        if let some niche := field.largestNiche then maxNiche := max maxNiche (← nicheAvailable target niche)
      let mut keys : Array (Nat × Nat × Nat × Fin fields.size) := #[]
      for i in (Array.finRange fields.size).extract 0 endIndex do
        let field := fields[i]
        let fieldAlign ← field.align.abi.bytesNat |>.mapError toString
        let nicheSize ← field.largestNiche.mapM (nicheAvailable target)
        let nicheSize := nicheSize.getD 0
        let key ← match packed with
          | some pack => pure (min fieldAlign (← pack.bytesNat |>.mapError toString))
          | none =>
            let pseudo := (Align.maxAlignedFactor (Size.ofBytes (UInt64.ofNat (max fieldAlign field.size.bytes.toNat)))).pow2
            pure (if maxNiche == 0 then pseudo else if !endBias then min (Nat.log2 maxAlign) pseudo
              else if nicheSize == maxNiche then Nat.log2 fieldAlign else pseudo)
        let inside ← match field.largestNiche with
          | none => pure 0
          | some niche =>
            if !endBias then pure niche.offset.bytes.toNat
            else
              let size ← niche.value.size target |>.mapError toString
              pure (2^64-1-(field.size.bytes.toNat-size.bytes.toNat-niche.offset.bytes.toNat))
        let key := match kind with
          | .prefixed .. => (key,nicheSize,0,i)
          | _ => (2^64-1-key,if endBias then nicheSize else 2^128-1-nicheSize,inside,i)
        keys := keys.push key
      keys := keys.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 ||
        (a.2.1 == b.2.1 && (a.2.2.1 < b.2.2.1 || (a.2.2.1 == b.2.2.1 && a.2.2.2 < b.2.2.2))))))
      order := (keys.map (·.2.2.2)) ++ order.extract endIndex order.size
  let mut offsets := Vector.replicate fields.size Size.ZERO
  let mut offset := Size.ZERO
  let mut unsized := false
  let mut largestNiche := none
  let mut largestAvailable := 0
  if let .prefixed size prefixAlign := kind then
    let prefixAlign := packed.map (prefixAlign.min ·) |>.getD prefixAlign
    align := align.max prefixAlign
    offset ← size.alignTo prefixAlign |>.mapError toString
  for i in order do
    let field := fields[i]
    if unsized then throw "unsized field is not the final field"
    if field.isUnsized then
      unless kind == .maybeUnsized do throw "unexpected unsized field"
      unsized := true
    let fieldAlign := packed.map (field.align.abi.min ·) |>.getD field.align.abi
    offset ← offset.alignTo fieldAlign |>.mapError toString
    align := align.max fieldAlign
    if let some requested := field.maxReprAlign then
      maxReprAlign := some (maxReprAlign.map (·.max requested) |>.getD requested)
    offsets := offsets.set i.val offset i.isLt
    if let some niche := field.largestNiche then
      let available ← nicheAvailable target niche
      if (if endBias then available ≥ largestAvailable else available > largestAvailable) then
        largestAvailable := available
        largestNiche := some {niche with offset := Size.ofBytes (niche.offset.bytes+offset.bytes)}
    offset ← checkedSize target (offset.bytes.toNat+field.size.bytes.toNat)
  let mut unadjusted := align
  if let some requested := reprAlign then align := align.max requested
  let size ← offset.alignTo align |>.mapError toString
  let _ ← checkedSize target size.bytes.toNat
  let mut backend := ABI.BackendRepr.Memory (sized := !unsized)
  let nonZero := (Array.finRange fields.size).filter (fun i => !fields[i].isZst)
  let single := if nonZero.size == 1 then nonZero[0]?.map (fun i => fields[i]) else none
  if !unsized && size.bytes > 0 then
    if let some field := single then
      let some i := nonZero[0]? | throw "nonzero field index invariant"
      if offsets.get i == Size.ZERO && align == field.align.abi && size == field.size then
        match field.backendRepr with
        | .Scalar _ | .SimdVector .. => if !repr.inhibitNewtypeAbiOptimization then backend := field.backendRepr
        | .ScalarPair .. => backend := field.backendRepr
        | _ => pure ()
    else if nonZero.size == 2 then
      let some i := nonZero[0]? | throw "nonzero field index invariant"
      let some j := nonZero[1]? | throw "nonzero field index invariant"
      if let .Scalar a := fields[i].backendRepr then
        if let .Scalar b := fields[j].backendRepr then
          let (i,a,j,b) := if (offsets.get i).bytes < (offsets.get j).bytes then (i,a,j,b) else (j,b,i,a)
          let pair ← scalarPair target a b
          if let .Arbitrary ps _ := pair.fields then
            let some firstOffset := ps[0]? | throw "scalar pair first offset invariant"
            let some secondOffset := ps[1]? | throw "scalar pair second offset invariant"
            if offsets.get i == firstOffset && offsets.get j == secondOffset && align == pair.align.abi && size == pair.size then
              backend := pair.backendRepr
  if repr.transparent then unadjusted := single.map (·.unadjustedAbiAlign) |>.getD align
  return {
    fields := .Arbitrary offsets.toArray (order.map (·.val)), variants := .Single 0, backendRepr := backend
    largestNiche, uninhabited := fields.any (·.uninhabited), align := .new align
    size, maxReprAlign, unadjustedAbiAlign := unadjusted
    reprC := repr.c || (repr.transparent && fields.any (·.reprC))
    randomizationSeed := fieldSeed+UInt64.ofNat repr.fieldShuffleSeed }

def univariant (target : RuntimeTargetDataLayout) (repr : ReprOptions)
    (fields : Array LayoutData) (kind : StructKind) : Except String LayoutData := do
  let layout ← univariantBiased target repr fields kind false
  if kind != .maybeUnsized && fields.size > 1 then
    if let some niche := layout.largestNiche then
      let head := niche.offset.bytes.toNat
      let width ← niche.value.size target |>.mapError toString
      let tail := layout.size.bytes.toNat-head-width.bytes.toNat
      if head != 0 && tail > 0 then
        let alternative ← univariantBiased target repr fields kind true
        let some other := alternative.largestNiche | throw "alternative layout lost its niche"
        if other.offset.bytes.toNat > head && other.offset.bytes.toNat > tail then return alternative
  pure layout

def unionLayout (target : RuntimeTargetDataLayout) (repr : ReprOptions)
    (fields : Array LayoutData) : Except String LayoutData := do
  unless !fields.isEmpty do throw "empty union"
  let packed ← repr.packBytes.mapM fun bytes => Align.fromBytes (UInt64.ofNat bytes) |>.mapError toString
  let reprAlign ← repr.alignBytes.mapM fun bytes => Align.fromBytes (UInt64.ofNat bytes) |>.mapError toString
  let mut align := if packed.isSome then target.i8Align else target.aggregateAlign
  let mut maxReprAlign := reprAlign
  let mut size := 0
  let mut common : Option ABI.BackendRepr := none
  let mut mismatch := repr.c
  for field in fields do
    if field.isUnsized then throw "unsized union field"
    align := align.max field.align.abi
    if let some requested := field.maxReprAlign then maxReprAlign := some (maxReprAlign.map (·.max requested) |>.getD requested)
    size := max size field.size.bytes.toNat
    unless field.isZst || mismatch do
      let candidate : ABI.BackendRepr := field.backendRepr.toUnion
      if let some previous := common then
        if previous != candidate then mismatch := true
      else common := some candidate
  if let some pack := packed then align := align.min pack
  let unadjusted := align
  if let some requested := reprAlign then align := align.max requested
  let mut backend := ABI.BackendRepr.Memory (sized := true)
  if !mismatch then
    if let some candidate := common then
      let acceptable ← match candidate with
        | .Scalar .. | .ScalarPair .. => pure ((← candidate.scalarPlatformAlign target |>.mapError reprStr) == some align)
        | .SimdVector (element := element) => pure ((← element.defaultAlign target |>.mapError reprStr).abi.pow2 ≤ align.pow2)
        | _ => pure true
      if acceptable then backend := candidate
  let rounded ← checkedSize target size
  let finalSize ← rounded.alignTo align |>.mapError toString
  let _ ← checkedSize target finalSize.bytes.toNat
  return {
    fields := .Union fields.size, variants := .Single 0, backendRepr := backend
    largestNiche := none, uninhabited := false, align := .new align, size := finalSize, maxReprAlign
    unadjustedAbiAlign := unadjusted, reprC := repr.c || (repr.transparent && fields.any (·.reprC))
    randomizationSeed := fields.foldl (fun s f => s+f.randomizationSeed) (UInt64.ofNat repr.fieldShuffleSeed) }
end Miri.Input.ConcreteLayout
