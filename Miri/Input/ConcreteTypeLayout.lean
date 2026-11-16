import Miri.Input.ConcreteEnumLayout
import Miri.Input.ConcreteCoroutineLayout
import Miri.Input.SourceDeclarationQueries

namespace Miri.Input.ConcreteTypeLayout
open Miri.ABI ConcreteLayout

private def defaultRepr : ReprOptions := ⟨none,none,none,0,none,0⟩

private def integer (target : RuntimeTargetDataLayout) : MIR.IntegerKind → Except String Integer
  | .i8 | .u8 => pure .I8 | .i16 | .u16 => pure .I16
  | .i32 | .u32 => pure .I32 | .i64 | .u64 => pure .I64
  | .i128 | .u128 => pure .I128
  | .isize | .usize => target.ptrSizedInteger.mapError reprStr

private def float : FloatTypeTag → ABI.Float
  | .f16 => .F16 | .f16b => .F16B | .f32 => .F32 | .f64 => .F64
  | .x87f80 => .X87F80 | .f128 => .F128 | .ppcf128 => .PpcF128

private def typeNode (document : ImportDocument) (id : TypeId) : Except String TypeNode := do
  let some node := document.types[id]? | throw s!"missing concrete type {id}"
  pure node

private def scalarConstant (document : ImportDocument) (id : Nat) : Except String Nat := do
  let some (.Value _ tree) := document.typeConstants[id]? | throw "nonconcrete type constant"
  let some (.Leaf bits _) := tree.nodes[tree.root]? | throw "nonscalar type constant"
  pure bits

private def fullScalar (target : RuntimeTargetDataLayout) (primitive : Primitive) : Except String Scalar := do
  let width ← primitive.size target |>.mapError reprStr
  return .Initialized (value := primitive) (validRange := ← WrappingRange.full width |>.mapError reprStr)

def pointerTail (document : ImportDocument) (fuel : Nat) (id : TypeId) : Except String TypeShape := do
  match fuel with
  | 0 => throw "cyclic unsized struct tail"
  | fuel+1 =>
    let node ← typeNode document id
    let normalized := node.sourceLayout.normalizedType
    if normalized != id then return ← pointerTail document fuel normalized
    match node.shape with
    | .adt data =>
      if data.kind != .structKind then pure node.shape else
        match data.variants[0]?.bind (·.fields.back?) with
        | some field => pointerTail document fuel field.typeId
        | none => pure node.shape
    | .tuple fields =>
      match fields.back? with
      | some field => pointerTail document fuel field
      | none => pure node.shape
    | .unsafeBinder inner _ => pointerTail document fuel inner
    | _ => pure node.shape

private def arrayLayout (target : RuntimeTargetDataLayout) (element : LayoutData)
    (count : Option Nat) : Except String LayoutData := do
  let n := count.getD 0
  let size ← checkedSize target (element.size.bytes.toNat*n)
  return {
    fields := .Array element.size (UInt64.ofNat n), variants := .Single 0
    backendRepr := .Memory (sized := count.isSome)
    largestNiche := if n == 0 then none else element.largestNiche
    uninhabited := element.uninhabited && n != 0, align := element.align, size
    maxReprAlign := none, unadjustedAbiAlign := element.align.abi, reprC := element.reprC
    randomizationSeed := element.randomizationSeed+UInt64.ofNat n }

private def vectorLayout (target : RuntimeTargetDataLayout) (element : LayoutData)
    (count : Nat) (packed : Bool) (vectors : Option Nat) : Except String LayoutData := do
  let .Scalar scalar := element.backendRepr | throw "SIMD element is not primitive"
  let lanes ← BackendLaneCount.new (UInt64.ofNat count) |>.mapError reprStr
  let rawSize ← checkedSize target (element.size.bytes.toNat*count)
  let (backend,size,align) ← match vectors with
    | some vectors => do
      let size ← checkedSize target (rawSize.bytes.toNat*vectors)
      let align ← target.rustVectorAlign rawSize |>.mapError reprStr
      pure (.SimdScalableVector (element := scalar) (count := lanes) (numberOfVectors := ⟨UInt8.ofNat vectors⟩),size,align)
    | none =>
      if packed && !lanes.isPowerOfTwo then pure (.Memory (sized := true),rawSize,Align.maxAlignedFactor rawSize)
      else do
        let align ← target.rustVectorAlign rawSize |>.mapError reprStr
        pure (.SimdVector (element := scalar) (count := lanes),rawSize,align)
  let size ← size.alignTo align |>.mapError reprStr
  return {
    fields := .Arbitrary #[Size.ZERO] #[0], variants := .Single 0, backendRepr := backend
    largestNiche := element.largestNiche, uninhabited := false, align := .new align
    size, maxReprAlign := none, unadjustedAbiAlign := element.align.abi, reprC := false
    randomizationSeed := element.randomizationSeed+UInt64.ofNat count }

def calculate (document : ImportDocument) (target : RuntimeTargetDataLayout)
    (id : TypeId) : Except String LayoutData := do
  (go (document.types.size+1) id).run' {}
where
  go : Nat → TypeId → StateT (Std.HashMap Nat LayoutData) (Except String) LayoutData
    | 0,_ => throw "cyclic concrete layout dependency"
    | fuel+1,id => do
      if let some layout := (← get)[id]? then return layout
      let node ← typeNode document id
      let scalar := fun value => do scalarLayout target (← fullScalar target value)
      let normalized := node.sourceLayout.normalizedType
      if normalized != id then
        let result ← go fuel normalized
        modify (·.insert id result)
        return result
      let result ← match node.shape with
        | .bool => scalarLayout target (.Initialized (value := .Int .I8 false) (validRange := ⟨0,1⟩))
        | .char => scalarLayout target (.Initialized (value := .Int .I32 false) (validRange := ⟨0,0x10ffff⟩))
        | .int (.known kind) => scalar (.Int (← integer target kind) true)
        | .uint (.known kind) => scalar (.Int (← integer target kind) false)
        | .float kind => scalar (.Float (float kind))
        | .functionPointer .. => do
          let pointer ← fullScalar target (.Pointer target.instructionAddressSpace)
          scalarLayout target (← pointer.setValidRange (← (pointer.validRange target).mapError reprStr >>= fun range => pure {range with start := 1}) |>.mapError reprStr)
        | .never => pure (neverLayout target)
        | .rawPointer pointee _ | .reference pointee .. => do
          let pointer ← fullScalar target (.Pointer AddressSpace.ZERO)
          let pointer ← if node.shapeKind == .reference then
              pointer.setValidRange { (← pointer.validRange target |>.mapError reprStr) with start := 1 } |>.mapError reprStr
            else pure pointer
          let tail ← pointerTail document (document.types.size+1) pointee
          match tail with
          | .slice _ | .str => scalarPair target pointer (← fullScalar target (.Int (← target.ptrSizedInteger.mapError reprStr) false))
          | .dynamicTraitObject .. =>
            let metadata ← fullScalar target (.Pointer AddressSpace.ZERO)
            let metadata ← metadata.setValidRange { (← metadata.validRange target |>.mapError reprStr) with start := 1 } |>.mapError reprStr
            scalarPair target pointer metadata
          | .alias .. => throw "unresolved pointer metadata type"
          | _ => scalarLayout target pointer
        | .functionDefinition .. => pure (unitLayout target)
        | .dynamicTraitObject .. | .foreign .. => pure (unitLayout target false)
        | .array element _ constructor => arrayLayout target (← go fuel element) (some constructor.count)
        | .slice element => do
          let layout ← arrayLayout target (← go fuel element) none
          pure {layout with randomizationSeed := 0x2dcba99c39784102}
        | .str => do
          let element ← scalar (.Int .I8 false)
          let layout ← arrayLayout target element none
          pure {layout with randomizationSeed := 0xc1325f37d127be22}
        | .tuple fields =>
          let fields ← fields.mapM (go fuel)
          univariant target defaultRepr fields (if fields.isEmpty then .alwaysSized else .maybeUnsized)
        | .closure .. | .coroutineClosure .. =>
          univariant target defaultRepr (← node.sourceLayout.closureUpvars.mapM (go fuel)) .alwaysSized
        | .unsafeBinder inner _ => go fuel inner
        | .adt data => do
          if let some simd := node.sourceLayout.simd then
            vectorLayout target (← go fuel simd.element) simd.count data.representation.packed node.sourceLayout.scalableVectors
          else
            let variants ← data.variants.mapM fun variant => variant.fields.mapM fun field => go fuel field.typeId
            if data.kind == .unionKind then
              let some fields := variants[0]? | throw "missing union fields"
              unionLayout target data.representation fields
            else if data.kind == .enumKind then
              ConcreteEnumLayout.calculate target data.representation variants node.sourceLayout.discriminants (node.sourceLayout.isUnsafeCell || node.sourceLayout.isUnsafePinned)
            else
              let some fields := variants[0]? | throw "missing struct fields"
              let maybeUnsized ← SourceDeclarationQueries.maybeUnsized document.sourceTraits data.definition
              let layout ← univariant target data.representation fields
                (if maybeUnsized && !fields.isEmpty then .maybeUnsized else .alwaysSized)
              if (node.sourceLayout.isUnsafeCell || node.sourceLayout.isUnsafePinned) then ConcreteEnumLayout.hideNiches target layout else pure layout
        | .patternType base pattern => do
          let layout ← go fuel base
          let (a,b,offset) ← match layout.backendRepr with
            | .Scalar scalar => pure (scalar,none,Size.ZERO)
            | .ScalarPair (a := a) (b := b) (bOffset := offset) => pure (a,some b,offset)
            | _ => throw "pattern base has no scalar layout"
          let current ← a.validRange target |>.mapError reprStr
          let range ← match pattern with
            | .notNull => pure {current with start := 1}
            | .range start finish => do
              unless b.isNone do throw "range pattern base is not scalar"
              let start ← scalarConstant document start
              let finish ← scalarConstant document finish
              let ordered : Bool ← if a.isSigned then do
                  let start ← layout.size.signExtend (BitVec.ofNat 128 start) |>.mapError reprStr
                  let finish ← layout.size.signExtend (BitVec.ofNat 128 finish) |>.mapError reprStr
                  pure (start ≤ finish)
                else pure (start ≤ finish)
              unless ordered do throw "wrapping range pattern"
              pure ⟨BitVec.ofNat 128 start,BitVec.ofNat 128 finish⟩
            | .or patterns =>
              let mut ranges := #[]
              for pattern in patterns do
                let .range start finish := pattern | throw "invalid mixed or-pattern"
                ranges := ranges.push (← scalarConstant document start,← scalarConstant document finish)
              ranges := ranges.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
              let some first := ranges[0]? | throw "empty or-pattern"
              let some second := ranges[1]? | throw "incomplete or-pattern"
              unless ranges.size == 2 && a.isSigned && b.isNone do throw "invalid or-pattern shape"
              let low ← layout.size.signedIntMin |>.mapError reprStr
              let low := (← layout.size.truncate (BitVec.ofInt 128 low) |>.mapError reprStr).toNat
              let (first,second) := if second.1 == low then (second,first) else (first,second)
              let firstEnd ← layout.size.signExtend (BitVec.ofNat 128 first.2) |>.mapError reprStr
              let secondStart ← layout.size.signExtend (BitVec.ofNat 128 second.1) |>.mapError reprStr
              unless firstEnd < secondStart do throw "overlapping or-pattern ranges"
              let upper ← layout.size.signedIntMax |>.mapError reprStr
              unless second.2 == upper.toNat do throw "or-pattern does not reach signed maximum"
              pure ⟨BitVec.ofNat 128 second.1,BitVec.ofNat 128 first.2⟩
          let a ← a.setValidRange range |>.mapError reprStr
          let backend := match b with | none => .Scalar a | some b => .ScalarPair (a := a) (b := b) (bOffset := offset)
          pure {layout with
            fields := .Arbitrary #[Size.ZERO] #[0], backendRepr := backend
            largestNiche := some ⟨Size.ZERO,a.primitive,range⟩}
        | .coroutine .. => do
          let some source := node.sourceLayout.coroutine | throw "coroutine source layout unavailable"
          let layout ← ConcreteCoroutineLayout.calculate target (← source.locals.mapM (go fuel))
            (← source.prefix.mapM (go fuel)) source.variants source.conflicts
          pure {layout with randomizationSeed := UInt64.ofNat source.seed}
        | .alias .. => throw "layout requested for an unnormalized concrete alias"
      let result ← match node.sourceLayout.specialFloat with
        | none => pure result
        | some .x87f80 => scalar (.Float .X87F80)
        | some kind => do
          let value ← fullScalar target (.Float (float kind))
          let align ← value.defaultAlign target |>.mapError reprStr
          pure {result with align, backendRepr := .Scalar value}
      let result ← if node.sourceLayout.isX87F80 then do
          unless result.size == ABI.Float.X87F80.size do throw "x87_f80 wrapper field size invariant"
          let some align := target.x87F80Align | throw "target x87_f80 alignment is absent"
          let size ← result.size.alignTo align |>.mapError reprStr
          pure {result with
            align := .new align
            unadjustedAbiAlign := align
            size := size
            backendRepr := .Memory (sized := true)
            largestNiche := none}
        else pure result
      modify (·.insert id result)
      pure result
end Miri.Input.ConcreteTypeLayout
