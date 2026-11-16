import Miri.ABI.FnAbi
import Miri.Input.Model.SourceAbi

namespace Miri.Input.SourceAbi
open Miri.ABI

inductive PointerKind where
  | shared (frozen : Bool)
  | mutable (unpin : Bool)
  | box (unpin global : Bool)

structure PointeeInfo where
  size : Size
  align : Align
  safe : Option PointerKind

structure Policy where
  target : RuntimeTargetDataLayout
  simdTypesIndirect : Bool
  softFloat : Bool
  maxReliableAlignment : Align
  boxNoAlias : Bool
  llvmWritable : Bool
  rustcNoWritable : Bool

structure Queries where
  typeCount : Nat
  lookup : TypeId → Except String (TyAndLayout TypeId)
  field : TyAndLayout TypeId → Nat → Except String (TyAndLayout TypeId)
  variant : TyAndLayout TypeId → Nat → Except String (TyAndLayout TypeId)
  pointeeInfo : TyAndLayout TypeId → Size → Except String (Option PointeeInfo)
  passIndirectlyInNonRusticAbis : TypeId → Except String Bool
  thinSelf : TyAndLayout TypeId → Except String (TyAndLayout TypeId)
  isX87F80 : TyAndLayout TypeId → Except String Bool

-- rustc_ty_utils::abi::arg_attrs_for_rust_scalar. Pointee classification is a
-- type query; scalar validity alone cannot establish reference permissions.
def scalarAttributes (policy : Policy) (queries : Queries) (layout : TyAndLayout TypeId)
    (scalar : Scalar) (offset : Size) (isReturn : Bool) : Except String ArgAttributes := do
  let mut attrs := ArgAttributes.new
  if !scalar.isUninitValid then attrs := { attrs with regular := attrs.regular ||| 128 }
  let .Initialized (value := .Pointer _) (validRange := range) := scalar | return attrs
  if !range.contains 0 then attrs := { attrs with regular := attrs.regular ||| 16 }
  let some pointee ← queries.pointeeInfo layout offset | return attrs
  if pointee.align.pow2 > 0 then
    attrs := { attrs with pointeeAlign := some ⟨min pointee.align.pow2 policy.maxReliableAlignment.pow2⟩ }
  attrs := { attrs with pointeeSize := pointee.size }
  let some kind := pointee.safe | return attrs
  let noAlias := match kind with
    | .shared frozen => frozen
    | .mutable unpin => unpin
    | .box unpin global => unpin && global && policy.boxNoAlias
  if noAlias && !isReturn then attrs := { attrs with regular := attrs.regular ||| 8 }
  if policy.llvmWritable && !policy.rustcNoWritable && !isReturn then
    if let .mutable true := kind then attrs := { attrs with regular := attrs.regular ||| 256 }
  let noFree := !isReturn && match kind with
    | .shared frozen => frozen
    | .mutable unpin => unpin
    | .box .. => false
  if noFree then attrs := { attrs with regular := attrs.regular ||| 512 }
  if !isReturn then
    if let .shared true := kind then attrs := { attrs with regular := attrs.regular ||| 36 }
  return attrs

def indirectMode (layout : LayoutData) : PassMode :=
  let attrs : ArgAttributes := {
    ArgAttributes.new with
    regular := 670
    pointeeSize := layout.size
    pointeeAlign := some layout.align.abi }
  if layout.isUnsized then .IndirectUnsized attrs ArgAttributes.new
  else .Indirect attrs none .Pointer

def argument (policy : Policy) (queries : Queries) (layout : TyAndLayout TypeId)
    (isReturn : Bool) : Except String (ArgAbi TypeId) := do
  let mode : PassMode ← if layout.layout.isZst then pure .Ignore else do
    match layout.layout.backendRepr with
    | .Scalar scalar =>
      let attrs ← scalarAttributes policy queries layout scalar Size.ZERO isReturn
      pure (.Direct attrs)
    | .ScalarPair (a := first) (b := second) (bOffset := offset) =>
      let firstAttrs ← scalarAttributes policy queries layout first Size.ZERO isReturn
      let secondAttrs ← scalarAttributes policy queries layout second offset isReturn
      pure (.Pair firstAttrs secondAttrs)
    | .SimdVector .. | .SimdScalableVector .. => pure (.Direct ArgAttributes.new)
    | .Memory .. => pure (indirectMode layout.layout)
  return ⟨layout, mode⟩

def isNoUndef (policy : Policy) (queries : Queries)
    (layout : TyAndLayout TypeId) : Except String Bool :=
  go (2 * queries.typeCount + 2) layout
where
  go (fuel : Nat) (layout : TyAndLayout TypeId) : Except String Bool := do
    let .succ fuel := fuel | throw "recursive source layout in noundef calculation"
    match layout.layout.backendRepr with
    | .Scalar scalar => return !scalar.isUninitValid
    | .ScalarPair (a := first) (b := second) =>
      let firstSize ← first.size policy.target |>.mapError reprStr
      let secondSize ← second.size policy.target |>.mapError reprStr
      return !first.isUninitValid && !second.isUninitValid &&
        firstSize.bytes + secondSize.bytes == layout.layout.size.bytes
    | .SimdVector .. | .SimdScalableVector .. => return false
    | .Memory .. =>
      match layout.layout.fields with
      | .Primitive | .Union _ => return false
      | .Array _ count =>
        if count == 0 then return true
        go fuel (← queries.field layout 0)
      | .Arbitrary _ _ =>
        let .Single _ := layout.layout.variants | return false
        let order ← layout.layout.fields.indexByIncreasingOffset |>.mapError reprStr
        let mut cursor := 0
        for index in order do
          let offset ← layout.layout.fields.offset index |>.mapError reprStr
          unless offset.bytes == cursor do return false
          let field ← queries.field layout index
          unless ← go fuel field do return false
          cursor := cursor + field.layout.size.bytes
        return cursor == layout.layout.size.bytes

def adjustRust (policy : Policy) (queries : Queries) (conv : CanonAbi)
    (arg : ArgAbi TypeId) (isReturn : Bool) : Except String (ArgAbi TypeId) := do
  match arg.mode with
  | .Ignore | .Cast .. => return arg
  | _ => pure ()
  let mut mode := arg.mode
  match mode, arg.layout.layout.backendRepr with
  | .Direct attrs, .Scalar scalar =>
    if scalar.isBool then mode := .Direct { attrs with argExt := .Zext }
  | .Pair first second, .ScalarPair (a := a) (b := b) =>
    mode := .Pair (if a.isBool then { first with argExt := .Zext } else first)
      (if b.isBool then { second with argExt := .Zext } else second)
  | _, _ => pure ()
  let layout := arg.layout.layout
  if isReturn && layout.size.bytes > 2 * policy.target.defaultAddressSpacePointerSpec.pointerSize.bytes then
    match layout.backendRepr with
    | .SimdVector .. | .SimdScalableVector .. => pure ()
    | _ => return { arg with mode := indirectMode layout }
  match layout.backendRepr with
  | .Memory .. =>
    if layout.isSized && layout.size.bytes <= policy.target.defaultAddressSpacePointerSpec.pointerSize.bytes then
      let register : Reg := ⟨.Integer, layout.size⟩
      let attrs : ArgAttributes := { ArgAttributes.new with
        regular := if ← isNoUndef policy queries arg.layout then 128 else 0 }
      mode := .Cast 0 ⟨#[], none, ⟨register, layout.size, false⟩, attrs⟩
    else if conv == .RustTail && !isReturn then
      unless layout.isSized do throw "RustTail argument is unsized"
      let .Indirect attrs space _ := indirectMode layout
        | throw "RustTail argument has no sized indirect mode"
      mode := .Indirect attrs space .OnStack
  | .SimdVector .. =>
    if policy.simdTypesIndirect && (policy.softFloat || layout.size.bytes > 16) then
      mode := indirectMode layout
  | _ => pure ()
  return { arg with mode }

inductive Eightbyte where
  | integer | sse | sseUp | x87 | x87Up
  deriving BEq, Repr

def Eightbyte.upperHalf : Eightbyte → Eightbyte
  | .integer => .integer
  | .sse | .sseUp => .sseUp
  | .x87 | .x87Up => .x87Up

def classifySysV (queries : Queries) (layout : TyAndLayout TypeId)
    (offset : Nat) (classes : Array (Option Eightbyte)) :
    Except String (Option (Array (Option Eightbyte))) :=
  go (2 * queries.typeCount + 2) layout offset classes
where
  go (fuel : Nat) (layout : TyAndLayout TypeId) (offset : Nat)
      (classes : Array (Option Eightbyte)) : Except String (Option (Array (Option Eightbyte))) := do
    let .succ fuel := fuel | throw "recursive source layout in SysV ABI classification"
    let alignment := 2 ^ layout.layout.align.abi.pow2
    if offset % alignment != 0 then
      return if layout.layout.isZst then some classes else none
    let component : Eightbyte ← match layout.layout.backendRepr with
      | .Scalar scalar => pure (match scalar.primitive with
          | .Int .. | .Pointer _ => Eightbyte.integer
          | .Float .X87F80 => .x87
          | .Float _ => .sse)
      | .SimdVector .. => pure .sse
      | .SimdScalableVector .. => throw "SysV ABI does not support scalable vectors"
      | .ScalarPair .. | .Memory .. =>
        let mut classes := classes
        for index in [:layout.layout.fields.count] do
          let fieldOffset ← layout.layout.fields.offset index |>.mapError reprStr
          let some next ← go fuel (← queries.field layout index)
            (offset + fieldOffset.bytes.toNat) classes | return none
          classes := next
        if let .Multiple _ _ _ variants := layout.layout.variants then
          for index in [:variants.size] do
            let some next ← go fuel (← queries.variant layout index) offset classes
              | return none
            classes := next
        return some classes
    if layout.layout.size.bytes == 0 then return some classes
    let first := offset / 8
    let last := (offset + layout.layout.size.bytes.toNat - 1) / 8
    if last >= classes.size then return none
    let mut result := classes
    let mut current := component
    for index in [first:last + 1] do
      if h : index < result.size then
        let old := result[index]
        match old, current with
          | some .x87, .sse | some .x87, .sseUp
          | some .x87Up, .sse | some .x87Up, .sseUp
          | some .sse, .x87 | some .sse, .x87Up
          | some .sseUp, .x87 | some .sseUp, .x87Up => return none
          | _, _ => pure ()
        let merged := match old, current with
          | some .integer, _ | _, .integer => Eightbyte.integer
          | some .sse, _ | _, .sse => Eightbyte.sse
          | some .sseUp, _ | _, .sseUp => Eightbyte.sseUp
          | some .x87, _ | _, .x87 => Eightbyte.x87
          | _, _ => current
        result := result.set index (some merged) h
        current := current.upperHalf
      else throw "SysV component index exceeds its classification buffer"
    return some result

def sysVClasses (queries : Queries) (arg : ArgAbi TypeId) :
    Except String (Option (Array (Option Eightbyte))) := do
  let count := (arg.layout.layout.size.bytes.toNat + 7) / 8
  if count > 8 then return none
  let some classes ← classifySysV queries arg.layout 0 (Array.replicate 8 none) | return none
  if count > 2 then
    let some first := classes[0]? | throw "SysV classification buffer is empty"
    unless first == some .sse do return none
    for index in [1:count] do
      let some component := classes[index]? | throw "SysV component index exceeds its classification buffer"
      unless component == some .sseUp do return none
    return some classes
  let mut classes := classes
  let mut index := 0
  while index < count do
    if h : index < classes.size then
      if classes[index] == some .sseUp then
        classes := classes.set index (some .sse) h
      else if classes[index] == some .sse then
        index := index + 1
        while index < count do
          let some component := classes[index]? | throw "SysV component index exceeds its classification buffer"
          if component != some .sseUp then break
          index := index + 1
      else index := index + 1
    else throw "SysV component index exceeds its classification buffer"
  if classes[0]? == some (some .x87Up) then return none
  for slot in [1:count] do
    let some previous := classes[slot - 1]? | throw "SysV component index exceeds its classification buffer"
    let some current := classes[slot]? | throw "SysV component index exceeds its classification buffer"
    if current == some .x87Up && previous != some .x87 then return none
  return some classes

def sysVRegister (classes : Array (Option Eightbyte)) (index remaining : Nat) :
    Except String (Option (Reg × Nat)) := do
  match classes[index]?.getD none with
  | none => return none
  | some .integer => return some (⟨.Integer, Size.ofBytes (UInt64.ofNat (min remaining 8))⟩, index + 1)
  | some .sse =>
    let mut finish := index + 1
    while h : finish < classes.size do
      unless classes[finish] == some .sseUp do break
      finish := finish + 1
    let register := if finish == index + 1 then
      if remaining == 4 then Reg.f32 else Reg.f64
      else Reg.opaqueVector (Size.ofBytes (UInt64.ofNat (8 * (finish - index))))
    return some (register, finish)
  | some .x87 =>
    let mut finish := index + 1
    while h : finish < classes.size do
      unless classes[finish] == some .x87Up do break
      finish := finish + 1
    unless finish == index + 2 do throw "SysV x87 register must occupy two eightbytes"
    return some (⟨.Float, Size.ofBytes 10⟩, finish)
  | some .sseUp | some .x87Up => throw "SysV register starts at an upper component"

def sysVCast (classes : Array (Option Eightbyte)) (size : Size) : Except String CastTarget := do
  let some (low, index) ← sysVRegister classes 0 size.bytes.toNat
    | throw "SysV aggregate has no register component"
  let mut result : CastTarget := ⟨#[], none, ⟨low, low.size, false⟩, ArgAttributes.new⟩
  let offset := 8 * index
  let mut finish := index
  if size.bytes.toNat > offset then
    if let some (high, next) ← sysVRegister classes index (size.bytes.toNat - offset) then
      result := ⟨#[low], none, ⟨high, high.size, false⟩, ArgAttributes.new⟩
      finish := next
  if (← sysVRegister classes finish 0).isSome then
    throw "SysV aggregate has more than two register components"
  return result

def extendInteger (arg : ArgAbi TypeId) (bits : Nat) : ArgAbi TypeId :=
  match arg.mode, arg.layout.layout.backendRepr with
  | .Direct attrs, .Scalar scalar =>
    match scalar.primitive with
    | .Int integer signed =>
      if integer.size.bytes.toNat * 8 < bits || arg.layout.layout.backendRepr.isBool then
        { arg with mode := .Direct { attrs with argExt := if signed then .Sext else .Zext } }
      else arg
    | _ => arg
  | _, _ => arg

def adjustSysV (queries : Queries) (abi : FnAbi TypeId) (darwin : Bool) :
    Except String (FnAbi TypeId) := do
  let mut integerRegisters := 6
  let mut sseRegisters := 8
  let mut ret := abi.ret
  let mut args := abi.args
  for (initial, index) in (#[ret] ++ args).toList.zipIdx do
    let isArgument := index != 0
    let mut arg := initial
    if arg.mode.isIgnore || !arg.layout.layout.isSized then continue
    if isArgument && (← queries.passIndirectlyInNonRusticAbis arg.layout.ty) then
      integerRegisters := integerRegisters - 1
      arg := { arg with mode := indirectMode arg.layout.layout }
    else if isArgument && (← queries.isX87F80 arg.layout) then
      let reg : Reg := ⟨.Float, Size.ofBytes 10⟩
      arg := {arg with mode := .Cast 0 ⟨#[], none, ⟨reg, reg.size, false⟩, ArgAttributes.new⟩}
    else
      let mut classes ← sysVClasses queries arg
      if isArgument then
        if let some classified := classes then
          if classified.contains (some .x87) then classes := none
          else
            let neededInteger := classified.foldl (fun count item =>
              if item == some .integer then count + 1 else count) 0
            let neededSse := classified.foldl (fun count item =>
              if item == some .sse then count + 1 else count) 0
            if neededInteger <= integerRegisters && neededSse <= sseRegisters then
              integerRegisters := integerRegisters - neededInteger
              sseRegisters := sseRegisters - neededSse
            else if arg.layout.layout.isAggregate then classes := none
      match classes with
      | none =>
        let mode := indirectMode arg.layout.layout
        if isArgument then
          let .Indirect attrs space _ := mode | throw "SysV stack argument is unsized"
          arg := { arg with mode := .Indirect attrs space .OnStack }
        else
          arg := { arg with mode }
          integerRegisters := integerRegisters - 1
      | some classified =>
        if arg.layout.layout.isAggregate then
          arg := { arg with mode := .Cast 0 (← sysVCast classified arg.layout.layout.size) }
        else if isArgument || darwin then arg := extendInteger arg 32
        if !isArgument && arg.layout.layout.backendRepr.isBool then arg := extendInteger arg 8
    if isArgument then
      if h : index - 1 < args.size then args := args.set (index - 1) arg h
      else throw "SysV argument index exceeds its argument buffer"
    else ret := arg
  return { abi with args, ret }

def canonicalConvention (policy : SourceAbiPolicy) (abi : ExternAbi) (variadic : Bool) :
    Except String CanonAbi := do
  match abi with
  | .C _ | .Cdecl _ => return .C
  | .Rust | .RustCall => return .Rust
  | .RustCold => return if policy.windows then .Rust else .RustCold
  | .RustPreserveNone => return .RustPreserveNone
  | .RustTail => return .RustTail
  | .System _ =>
    if policy.architecture == "x86" && policy.windows && !variadic then return .X86 .Stdcall
    return .C
  | .SysV64 _ =>
    unless policy.architecture == "x86_64" do throw "SysV64 requires x86_64"
    return .X86 .SysV64
  | .Win64 _ | .EfiApi =>
    unless policy.architecture == "x86_64" do throw "Win64 source ABI requires x86_64"
    return .X86 .Win64
  | .Vectorcall _ =>
    unless policy.architecture == "x86_64" || policy.architecture == "x86" do
      throw "vectorcall requires x86"
    return .X86 .Vectorcall
  | .Fastcall _ | .Stdcall _ =>
    if policy.architecture == "x86" then
      return .X86 (if let .Fastcall _ := abi then .Fastcall else .Stdcall)
    if policy.windows then return .C
    throw "fastcall/stdcall unavailable on target"
  | .X86Interrupt => return .Interrupt .X86
  | .Custom => return .Custom
  | .Swift =>
    unless policy.darwin do throw "Swift ABI requires Apple target"
    return .Swift
  | _ => throw s!"unsupported target ABI mapping: {reprStr abi}"

def canUnwind (policy : SourceAbiPolicy) (definition : Option SourceAbiDefinition)
    (abi : ExternAbi) : Bool := Id.run do
  if let some definition := definition then
    if definition.hasDefinition then
      if definition.neverUnwind || (!policy.panicUnwinds && !definition.foreign) ||
          (!policy.panicInDropUnwinds && definition.dropGlue) then return false
  match abi with
  | .C unwind | .System unwind | .Cdecl unwind | .Stdcall unwind | .Fastcall unwind
  | .Vectorcall unwind | .Thiscall unwind | .Aapcs unwind | .Win64 unwind | .SysV64 unwind => return unwind
  | .Rust | .RustCall | .RustCold | .RustPreserveNone | .RustTail => return policy.panicUnwinds
  | _ => return false

def adjustWin64 (policy : Policy) (queries : Queries) (abi : FnAbi TypeId) :
    Except String (FnAbi TypeId) := do
  let mut ret := abi.ret
  let mut args := abi.args
  for (initial, index) in (#[ret] ++ args).toList.zipIdx do
    let isReturn := index == 0
    let mut arg := initial
    if arg.mode.isIgnore then
      if arg.layout.layout.reprC then arg := {arg with mode := indirectMode arg.layout.layout}
    else if !isReturn && (← queries.passIndirectlyInNonRusticAbis arg.layout.ty) then
      arg := {arg with mode := indirectMode arg.layout.layout}
    else
      match arg.layout.layout.backendRepr with
      | .Memory (sized := false) => pure ()
      | .ScalarPair .. | .Memory (sized := true) =>
        let size := arg.layout.layout.size
        if [1, 2, 4, 8].contains size.bytes.toNat then
          let reg : Reg := ⟨.Integer, size⟩
          arg := {arg with mode := .Cast 0 ⟨#[], none, ⟨reg, size, false⟩, ArgAttributes.new⟩}
        else arg := {arg with mode := indirectMode arg.layout.layout}
      | .SimdVector .. => pure ()
      | .SimdScalableVector .. => throw "Win64 ABI does not support scalable vectors"
      | .Scalar scalar =>
        if isReturn && (match scalar.primitive with | .Int .I128 _ => true | _ => false) then
          unless policy.softFloat do
            let reg := Reg.opaqueVector (Size.ofBytes 16)
            arg := {arg with mode := .Cast 0 ⟨#[], none, ⟨reg, reg.size, false⟩, ArgAttributes.new⟩}
        else if arg.layout.layout.size.bytes > 8 then
          arg := {arg with mode := indirectMode arg.layout.layout}
        else arg := extendInteger arg 32
    if isReturn then ret := arg
    else if h : index - 1 < args.size then args := args.set (index - 1) arg h
    else throw "Win64 argument index exceeds its argument buffer"
  return {abi with ret, args}

def compute (source : SourceAbiPolicy) (target : RuntimeTargetDataLayout) (queries : Queries)
    (signature : FunctionSignature) (extra : Array TypeId)
    (definition : Option SourceAbiDefinition := none) (item : Bool := false) : Except String (FnAbi TypeId) := do
  unless source.architecture == "x86_64" do throw "source ABI target is not implemented"
  let policy : Policy := {
    target, simdTypesIndirect := source.simdTypesIndirect, softFloat := source.softFloat
    maxReliableAlignment := ⟨Nat.log2 source.maxReliableAlignment⟩
    boxNoAlias := source.boxNoAlias, llvmWritable := source.llvmWritable
    rustcNoWritable := !item || definition.any (·.noWritable) }
  let conv ← canonicalConvention source signature.abi signature.cVariadic
  let mut inputs := signature.inputs
  let mut extra := extra
  if signature.abi == .RustCall then
    unless !signature.cVariadic && extra.isEmpty do throw "invalid RustCall variadic arguments"
    let some last := inputs.back? | throw "RustCall is missing tuple argument"
    let last ← queries.lookup last
    let mut tupled := #[]
    for index in [:last.layout.fields.count] do
      tupled := tupled.push (← queries.field last index).ty
    inputs := inputs.pop
    extra := tupled
  else unless signature.cVariadic || extra.isEmpty do throw "nonvariadic source ABI has extra arguments"
  let fixedCount := inputs.size
  let mut builtArgs := #[]
  let actual := inputs ++ extra ++ (definition.bind (·.callerLocation)).toArray
  for h : index in [:actual.size] do
    let mut layout ← queries.lookup actual[index]
    if index == 0 && definition.any (·.virtualCall) then layout ← queries.thinSelf layout
    builtArgs := builtArgs.push (← argument policy queries layout false)
  let ret ← argument policy queries (← queries.lookup signature.output) true
  let mut abi : FnAbi TypeId := ⟨builtArgs, ret, signature.cVariadic, UInt32.ofNat fixedCount,
    conv, canUnwind source definition signature.abi⟩
  if conv.isRusticAbi then
    let rustArgs ← abi.args.mapM (fun arg => adjustRust policy queries conv arg false)
    let rustRet ← adjustRust policy queries conv abi.ret true
    abi := {abi with args := rustArgs, ret := rustRet}
  else if signature.abi == .X86Interrupt then
    if h : 0 < abi.args.size then
      let first := abi.args[0]
      let .Indirect attrs space _ := indirectMode first.layout.layout
        | throw "x86 interrupt first argument unsized"
      abi := {abi with args := abi.args.set 0 {first with mode := .Indirect attrs space .OnStack} h}
  else if signature.abi == .Win64 false || signature.abi == .Win64 true ||
      (match signature.abi with | .Vectorcall _ => true | _ => false) ||
      (source.windows && !(match signature.abi with | .SysV64 _ => true | _ => false)) then
    abi ← adjustWin64 policy queries abi
  else abi ← adjustSysV queries abi source.darwin
  return abi

end Miri.Input.SourceAbi
