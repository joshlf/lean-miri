import Miri.Input.ConcreteAggregateLayout

namespace Miri.Input.ConcreteEnumLayout
open Miri.ABI

private def absent (fields : Array LayoutData) : Bool :=
  fields.any (·.uninhabited) && fields.all (·.is1zst)

private def maximumInteger (a b : Integer) : Integer :=
  if a.size.bytes < b.size.bytes then b else a

private def reprInteger (target : RuntimeTargetDataLayout) (repr : ReprInteger) :
    Except String (Integer × Bool) := do
  match repr with
  | .pointerSized signed => return (← target.ptrSizedInteger.mapError reprStr, signed)
  | .fixed _ bits signed =>
    let integer ← Integer.fromSize (Size.fromBits (UInt64.ofNat bits)) |>.mapError reprStr
    return (integer, signed)

def hideNiches (target : RuntimeTargetDataLayout) (layout : LayoutData) : Except String LayoutData := do
  let hide : Scalar → Except String Scalar := fun scalar => do
    match scalar with
    | .Initialized (value := value) (validRange := _) =>
      let width ← value.size target |>.mapError reprStr
      let range ← WrappingRange.full width |>.mapError reprStr
      pure (Scalar.Initialized (value := value) (validRange := range))
    | .Union (value := _) => pure scalar
  let backend : ABI.BackendRepr ← match layout.backendRepr with
    | .Scalar value => do pure (ABI.BackendRepr.Scalar (← hide value))
    | .ScalarPair (a := a) (b := b) (bOffset := offset) => do pure (ABI.BackendRepr.ScalarPair (a := ← hide a) (b := ← hide b) (bOffset := offset))
    | .SimdVector (element := element) (count := count) => do pure (ABI.BackendRepr.SimdVector (element := ← hide element) (count := count))
    | .SimdScalableVector (element := element) (count := count) (numberOfVectors := number) => do pure (ABI.BackendRepr.SimdScalableVector (element := ← hide element) (count := count) (numberOfVectors := number))
    | .Memory (sized := sized) => pure (.Memory (sized := sized))
  return {layout with backendRepr := backend, largestNiche := none}

/-- `layout_of_enum` from the pinned rustc_abi. Discriminants retain their
source signed interpretation; the exporter has already evaluated them. -/
def calculate (target : RuntimeTargetDataLayout) (repr : ReprOptions)
    (variants : Array (Array LayoutData)) (discriminants : Array Int)
    (dontNiche : Bool := false) : Except String LayoutData := do
  if equalSizes : discriminants.size = variants.size then
    let present := (Array.finRange variants.size).filter fun i =>
      repr.inhibitEnumLayoutOptimization || !(absent variants[i])
    if present.isEmpty then return ConcreteLayout.neverLayout target
    if present.size == 1 && !repr.inhibitEnumLayoutOptimization then
      let some i := present[0]? | throw "present enum variant index invariant"
      let layout ← ConcreteLayout.univariant target repr variants[i] .alwaysSized
      let layout := {layout with variants := .Single i.val}
      if !dontNiche then return layout
      return ← hideNiches target layout
    if repr.packed then throw "conflicting packed enum representation"

    let nicheLayout : Except String (Option LayoutData) := do
      if repr.inhibitEnumLayoutOptimization || variants.size < 2 then return none
      let mut align := target.aggregateAlign
      let mut maxRepr := ← repr.alignBytes.mapM fun bytes => Align.fromBytes (UInt64.ofNat bytes) |>.mapError toString
      let mut unadjusted := align
      let mut seed := UInt64.ofNat repr.fieldShuffleSeed
      let mut infos : Array (VariantLayout × Align) := #[]
      for fields in variants do
        let source ← ConcreteLayout.univariant target repr fields .alwaysSized
        infos := infos.push (← VariantLayout.fromLayout source |>.mapError reprStr,source.align.abi)
        align := align.max source.align.abi
        maxRepr := match maxRepr,source.maxReprAlign with
          | some a,some b => some (a.max b) | a,none => a | none,b => b
        unadjusted := unadjusted.max source.unadjustedAbiAlign
        seed := seed + source.randomizationSeed
      let largest := (Array.finRange infos.size).foldl (fun best i => match best with
        | none => some i
        | some previous => if infos[i].1.size.bytes >= infos[previous].1.size.bytes then some i else best)
        (none : Option (Fin infos.size))
      let some largest := largest | return none
      let original := infos[largest].1
      let originalAlign := infos[largest].2
      let needsTag := (Array.finRange variants.size).filter fun i =>
        i.val != largest.val && !(absent variants[i])
      if needsTag.isEmpty then return none
      let some firstIndex := needsTag[0]? | throw "niche first variant invariant"
      let first := firstIndex.val
      let some lastIndex := needsTag[needsTag.size-1]? | throw "niche last variant invariant"
      let last := lastIndex.val
      let some niche := original.largestNiche | return none
      let some (nicheStart,tag) ← ConcreteLayout.nicheReserve target niche (last-first+1) | return none
      let nicheSize ← niche.value.size target |>.mapError reprStr
      let size ← original.size.alignTo align |>.mapError toString
      let adjusted ← infos.mapIdxM fun i (source,alignment) => do
        if i == largest.val then return some source
        let mut layout := {source with largestNiche := none}
        if layout.size.bytes > niche.offset.bytes then
          let after ← niche.offset.add nicheSize |>.mapError toString
          let offset ← after.alignTo alignment |>.mapError toString
          let endOffset ← offset.add layout.size |>.mapError toString
          if endOffset.bytes > size.bytes then return none
          let offsets ← layout.fieldOffsets.mapM fun field => field.add offset |>.mapError toString
          layout := {layout with
            fieldOffsets := offsets
            size := endOffset
            backendRepr := if layout.uninhabited then layout.backendRepr else .Memory (sized := true)}
        return some layout
      if adjusted.any (·.isNone) then return none
      let layouts := adjusted.filterMap id
      let largestNiche ← ConcreteLayout.nicheFromScalar target niche.offset tag
      let othersZst := (Array.finRange layouts.size).all fun i => i.val == largest.val || layouts[i].size.bytes == 0
      let sameSize := size == original.size
      let sameAlign := align == originalAlign
      let backend := if sameSize && sameAlign && othersZst then
          match original.backendRepr with
          | .Scalar _ => .Scalar tag
          | .ScalarPair (a := a) (b := b) (bOffset := offset) =>
            if niche.offset.bytes == 0 then .ScalarPair (a := tag) (b := b.toUnion) (bOffset := offset)
            else .ScalarPair (a := a.toUnion) (b := tag) (bOffset := offset)
          | _ => .Memory (sized := true)
        else .Memory (sized := true)
      return some {
        variants := .Multiple tag (.Niche largest.val first last (BitVec.ofNat 128 nicheStart)) 0 layouts
        fields := .Arbitrary #[niche.offset] #[0]
        backendRepr := backend
        largestNiche
        uninhabited := layouts.all (·.uninhabited)
        size
        align := .new align
        maxReprAlign := maxRepr
        unadjustedAbiAlign := unadjusted
        reprC := repr.c
        randomizationSeed := seed }
    -- Failure of a speculative niche arrangement leaves the tagged arrangement.
    let nicheLayout := match nicheLayout with | .ok layout => layout | .error _ => none

    let necessary := (Array.finRange variants.size).filterMap fun i =>
      if repr.c || variants[i].all (!·.uninhabited) then some (discriminants[i.val]'(by omega)) else none
    let minNegative := necessary.foldl (fun a b => min a b) 0
    let maxPositive := necessary.foldl (fun a b => max a b) 0
    let unsignedFit := Integer.fitUnsigned (BitVec.ofInt 128 (max (if minNegative < 0 then minNegative + 2^128 else minNegative) maxPositive))
    let signedFit := maximumInteger (Integer.fitSigned minNegative) (Integer.fitSigned maxPositive)
    let (minimum,signed) ← match repr.integer with
      | some explicit => do
        let (integer,signed) ← reprInteger target explicit
        let fit := if signed then signedFit else unsignedFit
        unless integer.size.bytes >= fit.size.bytes do throw "enum representation cannot hold discriminants"
        pure (integer,signed)
      | none =>
        let least := if repr.c then target.cEnumMinSize else .I8
        if unsignedFit.size.bytes <= signedFit.size.bytes then pure (maximumInteger least unsignedFit,false)
        else pure (maximumInteger least signedFit,true)
    let mut align := target.aggregateAlign
    let mut maxRepr := ← repr.alignBytes.mapM fun bytes => Align.fromBytes (UInt64.ofNat bytes) |>.mapError toString
    let mut unadjusted := align
    let mut seed := UInt64.ofNat repr.fieldShuffleSeed
    let mut size := Size.ZERO
    let mut startAlign : Align := ⟨8⟩
    let mut prefixAlign := (← minimum.align target |>.mapError reprStr).abi
    if repr.c then
      for fields in variants do
        for field in fields do prefixAlign := prefixAlign.max field.align.abi
    let mut layouts : Array VariantLayout := #[]
    for fields in variants do
      let layout ← ConcreteLayout.univariant target repr fields (.prefixed minimum.size prefixAlign)
      let order ← layout.fields.indexByIncreasingOffset |>.mapError reprStr
      for index in order do
        let some field := fields[index]? | throw "enum field layout index out of bounds"
        if !field.is1zst then
          startAlign := startAlign.min field.align.abi
          break
      size := if layout.size.bytes > size.bytes then layout.size else size
      align := align.max layout.align.abi
      maxRepr := match maxRepr,layout.maxReprAlign with
        | some a,some b => some (a.max b) | a,none => a | none,b => b
      unadjusted := unadjusted.max layout.unadjustedAbiAlign
      seed := seed + layout.randomizationSeed
      layouts := layouts.push (← VariantLayout.fromLayout layout |>.mapError reprStr)
    size ← size.alignTo align |>.mapError toString
    if size.bytes >= target.base.objSizeBound then throw "enum layout size overflow"
    let typeck ← match repr.integer with
      | some explicit => do pure (← reprInteger target explicit).1
      | none => target.ptrSizedInteger.mapError reprStr
    if typeck.size.bytes < minimum.size.bytes then throw "enum layout tag exceeds discriminant type"
    let promoted ← if repr.c || repr.integer.isSome then pure minimum else do
      pure ((← Integer.forAlign target startAlign |>.mapError reprStr).getD minimum)
    let integer := maximumInteger promoted minimum
    if integer.size.bytes > minimum.size.bytes then
      layouts ← layouts.mapM fun layout => do
        let offsets ← layout.fieldOffsets.mapM fun offset => do
          if offset.bytes <= minimum.size.bytes then
            unless offset == minimum.size do throw "enum tag promotion offset invariant"
            pure integer.size
          else pure offset
        return {layout with
          fieldOffsets := offsets
          size := if layout.size.bytes <= minimum.size.bytes then integer.size else layout.size}
    let tags ← necessary.toList.mapM fun value => integer.size.truncate (BitVec.ofInt 128 value) |>.mapError toString
    let range := (← WrappingRange.smallestRangeContaining tags integer.size |>.mapError reprStr).getD ⟨0,0⟩
    let tag := Scalar.Initialized (value := .Int integer signed) (validRange := range)
    let mut backend := ABI.BackendRepr.Memory (sized := true)
    if integer.size == size then backend := .Scalar tag
    else
      let mut common : Option (Primitive × Size) := none
      let mut initialized := true
      let mut compatible := true
      for (fields,layout) in variants.zip layouts do
        let relevant := (fields.zip layout.fieldOffsets).filter fun (field,_) => !field.isZst
        match relevant.toList with
        | [] =>
          initialized := false
          continue
        | [(field,offset)] =>
          match field.backendRepr with
          | .Scalar scalar =>
            initialized := initialized && !scalar.isUninitValid
            let primitive := scalar.primitive
            if let some (old,previousOffset) := common then
              if offset != previousOffset then
                compatible := false
                break
              if old == primitive then continue
              match old,primitive with
              | .Int a _,.Int b _ =>
                if a != b then
                  compatible := false
                  break
              | .Pointer _,.Int .. | .Int ..,.Pointer _ =>
                let oldSize ← old.size target |>.mapError reprStr
                let newSize ← primitive.size target |>.mapError reprStr
                let oldAlign ← old.defaultAlign target |>.mapError reprStr
                let newAlign ← primitive.defaultAlign target |>.mapError reprStr
                if oldSize != newSize || oldAlign != newAlign then
                  compatible := false
                  break
                match primitive with
                | .Pointer _ => common := some (primitive,offset)
                | _ => pure ()
              | _,_ =>
                compatible := false
                break
            else common := some (primitive,offset)
          | _ =>
            compatible := false
            break
        | _ =>
          compatible := false
          break
      if compatible then
        if let some (primitive,offset) := common then
          let scalar ← if initialized then do
              let width ← primitive.size target |>.mapError reprStr
              let range ← WrappingRange.full width |>.mapError reprStr
              pure (Scalar.Initialized (value := primitive) (validRange := range))
            else pure (Scalar.Union (value := primitive))
          let pair ← ConcreteLayout.scalarPair target tag scalar
          match pair.fields with
          | .Arbitrary offsets _ =>
            if offsets[0]? == some Size.ZERO && offsets[1]? == some offset && pair.align.abi == align && pair.size == size then
              backend := pair.backendRepr
          | _ => throw "enum scalar-pair field invariant"
    if (match backend with | .Scalar _ | .ScalarPair .. => true | _ => false) then
      layouts := layouts.map fun layout =>
        match layout.backendRepr with
        | .Memory (sized := _) =>
          if layout.hasFields then {layout with
            backendRepr := backend
            size := if layout.size.bytes < size.bytes then size else layout.size}
          else layout
        | _ => layout
    let tagged : LayoutData := {
      variants := .Multiple tag .Direct 0 layouts
      fields := .Arbitrary #[Size.ZERO] #[0]
      backendRepr := backend
      largestNiche := ← ConcreteLayout.nicheFromScalar target Size.ZERO tag
      uninhabited := layouts.all (·.uninhabited)
      size
      align := .new align
      maxReprAlign := maxRepr
      unadjustedAbiAlign := unadjusted
      reprC := repr.c
      randomizationSeed := seed }
    if let some niche := nicheLayout then
      if tagged.size.bytes > niche.size.bytes then return niche
      if tagged.size == niche.size then
        let taggedAvailable ← match tagged.largestNiche with
          | some value => ConcreteLayout.nicheAvailable target value | none => pure 0
        let nicheAvailable ← match niche.largestNiche with
          | some value => ConcreteLayout.nicheAvailable target value | none => pure 0
        if taggedAvailable < nicheAvailable then return niche
    return tagged

  else throw "enum discriminant count mismatch"
end Miri.Input.ConcreteEnumLayout
