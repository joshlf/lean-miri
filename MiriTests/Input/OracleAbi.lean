import Miri.Input.RuntimeMetadata
import Miri.Input.TableTail
import Miri.ABI.FnAbi

namespace Miri.Input.OracleAbi
open JsonReader DecoderValues Miri.ABI
abbrev LayoutId := Nat

inductive PassModeKind where
  | ignore | direct | pair | cast | indirect | indirectUnsized
  deriving Repr, DecidableEq

inductive ArmCallKind where
  | aapcs | cmseNonSecureCall | cmseNonSecureEntry
  deriving Repr, DecidableEq

inductive InterruptCallKind where
  | avr | avrNonBlocking | msp430 | riscvMachine | riscvSupervisor | x86
  deriving Repr, DecidableEq

inductive X86CallKind where
  | fastcall | stdcall | sysv64 | thiscall | vectorcall | win64
  deriving Repr, DecidableEq

inductive CanonicalAbiKind where
  | c | rust | rustCold | rustPreserveNone | rustTail | custom | swift
  | arm | gpuKernel | interrupt | x86
  deriving Repr, DecidableEq

structure CanonicalAbi where
  kind : CanonicalAbiKind
  armCall : Option ArmCallKind
  interruptKind : Option InterruptCallKind
  x86Call : Option X86CallKind
  deriving BEq

inductive ArgumentExtensionKind where
  | none | zeroExtend | signExtend
  deriving Repr, DecidableEq

inductive ArgumentCaptureKind where
  | none | address | readOnly | unrestricted
  deriving Repr, DecidableEq

inductive IndirectModeKind where
  | pointer | onStack | amdgpuKernelArgument
  deriving Repr, DecidableEq

structure AbiAttributes where
  regularBits : Nat
  pointeeSizeBytes : Nat
  pointeeAlignBytes : Option Nat
  argExtension : ArgumentExtensionKind
  deriving BEq

inductive AbiRegisterKind where
  | integer | float | ppcF128 | vector
  deriving Repr, DecidableEq

inductive AbiRegisterHint where
  | integer (kind : IntegerTypeTag) (signed : Bool)
  | float (kind : FloatTypeTag)
  | pointer (addressSpace : Nat)
  deriving Repr, DecidableEq

structure AbiRegister where
  kind : AbiRegisterKind
  sizeBits : Nat
  hintElement : Option AbiRegisterHint
  deriving BEq

structure AbiCastTarget where
  prefixRegisters : Array AbiRegister
  restOffsetBytes : Option Nat
  restRegister : AbiRegister
  restTotalBytes : Nat
  restIsConsecutive : Bool
  attributes : AbiAttributes
  deriving BEq

structure AbiPassMode where
  kind : PassModeKind
  attributes : Array AbiAttributes
  castTarget : Option AbiCastTarget
  padI32Count : Option Nat
  addressSpace : Option Nat
  indirectMode : Option IndirectModeKind
  deriving BEq

structure AbiArgument where
  typeId : TypeId
  /-- Physical compiler TyAndLayout for this FnAbi argument. The logical type
  remains `typeId`; Rust can adjust the ABI layout independently (notably the
  forced-thin virtual-call receiver). The input schema validates its presence. -/
  layoutId : LayoutId
  mode : AbiPassMode
  deriving BEq

structure FunctionAbi where
  arguments : Array AbiArgument
  returnValue : AbiArgument
  callingConvention : CanonicalAbi
  canUnwind : Bool
  cVariadic : Bool
  fixedCount : Nat
  deriving BEq

def validateCanonicalAbi (abi : CanonicalAbi) (path : String) : Except String Unit := do
  match abi.kind with
  | .arm =>
    match abi.armCall with
    | none => throw (DecoderValues.joinPath path "arm_call" ++ ": " ++ "ARM calling convention is missing its call kind")
    | _ => pure ()
  | .interrupt =>
    match abi.interruptKind with
    | none => throw (DecoderValues.joinPath path "interrupt_kind" ++ ": " ++ "interrupt calling convention is missing its interrupt kind")
    | _ => pure ()
  | .x86 =>
    match abi.x86Call with
    | none => throw (DecoderValues.joinPath path "x86_call" ++ ": " ++ "x86 calling convention is missing its call kind")
    | _ => pure ()
  | _ => pure ()
  return ()

def validateAbiRegister (reg : AbiRegister) (path : String) : Except String Unit := do
  match reg.kind with
  | .vector =>
    match reg.hintElement with
    | none => throw (DecoderValues.joinPath path "kind.hint_element" ++ ": " ++ "vector ABI register is missing its element hint")
    | some _ => pure ()
  | _ => pure ()
  return ()

def validateAbiPassMode (mode : AbiPassMode) (path : String) : Except String Unit := do
  match mode.castTarget with
  | some target =>
    for (register, index) in target.prefixRegisters.toList.zipIdx do
      validateAbiRegister register s!"{path}.target.prefix_registers[{index}]"
    validateAbiRegister target.restRegister (DecoderValues.joinPath path "target.rest_register")
  | none => pure ()
  return ()

def validateFunctionAbi (abi : FunctionAbi) (path : String) : Except String Unit := do
  validateCanonicalAbi abi.callingConvention (path ++ ".calling_convention")
  for (arg, index) in (abi.arguments.push abi.returnValue).toList.zipIdx do
    validateAbiPassMode arg.mode s!"{path}.arguments[{index}].mode"

def passModeKind (tag : String) : Except String PassModeKind :=
  match tag with
  | "Ignore" => pure (.ignore)
  | "Direct" => pure (.direct)
  | "Pair" => pure (.pair)
  | "Cast" => pure (.cast)
  | "Indirect" => pure (.indirect)
  | "IndirectUnsized" => pure (.indirectUnsized)
  | other => throw s!"unrecognized passModeKind tag `{other}`"

def abiRegisterKind (tag : String) : Except String AbiRegisterKind :=
  match tag with
  | "integer" => pure (.integer)
  | "float" => pure (.float)
  | "ppc_f128" => pure (.ppcF128)
  | "vector" => pure (.vector)
  | other => throw s!"unrecognized abiRegisterKind tag `{other}`"

def canonicalAbiKind (tag : String) : Except String CanonicalAbiKind :=
  match tag with
  | "c" => pure (.c)
  | "rust" => pure (.rust)
  | "rust_cold" => pure (.rustCold)
  | "rust_preserve_none" => pure (.rustPreserveNone)
  | "rust_tail" => pure (.rustTail)
  | "custom" => pure (.custom)
  | "swift" => pure (.swift)
  | "arm" => pure (.arm)
  | "gpu_kernel" => pure (.gpuKernel)
  | "interrupt" => pure (.interrupt)
  | "x86" => pure (.x86)
  | other => throw s!"unrecognized canonicalAbiKind tag `{other}`"

def armCallKind (tag : String) : Except String ArmCallKind :=
  match tag with
  | "aapcs" => pure (.aapcs)
  | "cmse_nonsecure_call" => pure (.cmseNonSecureCall)
  | "cmse_nonsecure_entry" => pure (.cmseNonSecureEntry)
  | other => throw s!"unrecognized armCallKind tag `{other}`"

def interruptCallKind (tag : String) : Except String InterruptCallKind :=
  match tag with
  | "avr" => pure (.avr)
  | "avr_non_blocking" => pure (.avrNonBlocking)
  | "msp430" => pure (.msp430)
  | "riscv_machine" => pure (.riscvMachine)
  | "riscv_supervisor" => pure (.riscvSupervisor)
  | "x86" => pure (.x86)
  | other => throw s!"unrecognized interruptCallKind tag `{other}`"

def x86CallKind (tag : String) : Except String X86CallKind :=
  match tag with
  | "fastcall" => pure (.fastcall)
  | "stdcall" => pure (.stdcall)
  | "sysv64" => pure (.sysv64)
  | "thiscall" => pure (.thiscall)
  | "vectorcall" => pure (.vectorcall)
  | "win64" => pure (.win64)
  | other => throw s!"unrecognized x86CallKind tag `{other}`"

private structure ParseArgumentExtensionFields where
  kind : Option (String) := none

def parseArgumentExtension (path : String) : Parser (ArgumentExtensionKind) := do
  let s ← object (ParseArgumentExtensionFields.mk none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  match kind with
  | "none" => pure .none
  | "zero_extend" => pure .zeroExtend
  | "sign_extend" => pure .signExtend
  | _ => fail s!"{path}: unknown ArgumentExtensionKind"

private structure ParseIndirectModeFields where
  kind : Option (String) := none

def parseIndirectMode (path : String) : Parser (IndirectModeKind) := do
  let s ← object (ParseIndirectModeFields.mk none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  match kind with
  | "pointer" => pure .pointer
  | "on_stack" => pure .onStack
  | "amdgpu_kernel_argument" => pure .amdgpuKernelArgument
  | _ => fail s!"{path}: unknown IndirectModeKind"

private structure ParseAbiAttributesFields where
  regular_bits : Option (Nat) := none
  pointee_size_bytes : Option (Nat) := none
  pointee_align_bytes : Option (Option Nat) := none
  arg_extension : Option (ArgumentExtensionKind) := none

def parseAbiAttributes (path : String) : Parser (AbiAttributes) := do
  let s ← object (ParseAbiAttributesFields.mk none none none none) fun s key => do
    match key with
    | "regular_bits" => return { s with regular_bits := some (← natural) }
    | "pointee_size_bytes" => return { s with pointee_size_bytes := some (← natural) }
    | "pointee_align_bytes" => return { s with pointee_align_bytes := some (← nullable natural) }
    | "arg_extension" => return { s with arg_extension := some (← parseArgumentExtension (path ++ ".arg_extension")) }
    | _ => skipValue; pure s
  let regular_bits ← required s.regular_bits (path ++ ".regular_bits")
  let pointee_size_bytes ← required s.pointee_size_bytes (path ++ ".pointee_size_bytes")
  let pointee_align_bytes ← pure (s.pointee_align_bytes.getD none)
  let arg_extension ← required s.arg_extension (path ++ ".arg_extension")
  return ⟨regular_bits, pointee_size_bytes, pointee_align_bytes, arg_extension⟩

private structure ParseCanonicalAbiFields where
  kind : Option (String) := none
  arm_call : Option (Option String) := none
  interrupt_kind : Option (Option String) := none
  x86_call : Option (Option String) := none

def parseCanonicalAbi (path : String) : Parser (CanonicalAbi) := do
  let s ← object (ParseCanonicalAbiFields.mk none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "arm_call" => return { s with arm_call := some (← nullable string) }
    | "interrupt_kind" => return { s with interrupt_kind := some (← nullable string) }
    | "x86_call" => return { s with x86_call := some (← nullable string) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let arm_call ← pure (s.arm_call.getD none)
  let interrupt_kind ← pure (s.interrupt_kind.getD none)
  let x86_call ← pure (s.x86_call.getD none)
  let allowed : List String := match kind with
    | "arm" => ["arm_call"]
    | "interrupt" => ["interrupt_kind"]
    | "x86" => ["x86_call"]
    | _ => []
  if s.arm_call.isSome && !(allowed.contains "arm_call") then fail s!"{path}: field `arm_call` is incompatible with the selected variant"
  if s.interrupt_kind.isSome && !(allowed.contains "interrupt_kind") then fail s!"{path}: field `interrupt_kind` is incompatible with the selected variant"
  if s.x86_call.isSome && !(allowed.contains "x86_call") then fail s!"{path}: field `x86_call` is incompatible with the selected variant"
  if kind == "arm" then let _ ← required arm_call "arm_call"; pure ()
  if kind == "interrupt" then let _ ← required interrupt_kind "interrupt_kind"; pure ()
  if kind == "x86" then let _ ← required x86_call "x86_call"; pure ()
  return ⟨← liftExcept (canonicalAbiKind kind), ← liftExcept (arm_call.mapM armCallKind),
    ← liftExcept (interrupt_kind.mapM interruptCallKind), ← liftExcept (x86_call.mapM x86CallKind)⟩

private structure ParseAbiRegisterHintFields where
  kind : Option (String) := none
  integer_kind : Option (Option String) := none
  signed : Option (Option Bool) := none
  float_kind : Option (Option String) := none
  address_space : Option (Option Nat) := none

def parseAbiRegisterHint (path : String) : Parser (AbiRegisterHint) := do
  let s ← object (ParseAbiRegisterHintFields.mk none none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "integer_kind" => return { s with integer_kind := some (← nullable string) }
    | "signed" => return { s with signed := some (← nullable boolean) }
    | "float_kind" => return { s with float_kind := some (← nullable string) }
    | "address_space" => return { s with address_space := some (← nullable natural) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let integer_kind ← pure (s.integer_kind.getD none)
  let signed ← pure (s.signed.getD none)
  let float_kind ← pure (s.float_kind.getD none)
  let address_space ← pure (s.address_space.getD none)
  let allowed : List String := match kind with
    | "integer" => ["integer_kind", "signed"]
    | "float" => ["float_kind"]
    | "pointer" => ["address_space"]
    | _ => []
  if s.integer_kind.isSome && !(allowed.contains "integer_kind") then fail s!"{path}: field `integer_kind` is incompatible with the selected variant"
  if s.signed.isSome && !(allowed.contains "signed") then fail s!"{path}: field `signed` is incompatible with the selected variant"
  if s.float_kind.isSome && !(allowed.contains "float_kind") then fail s!"{path}: field `float_kind` is incompatible with the selected variant"
  if s.address_space.isSome && !(allowed.contains "address_space") then fail s!"{path}: field `address_space` is incompatible with the selected variant"
  match kind with
  | "integer" => return .integer (← liftExcept (integerTypeTag (← required integer_kind "integer_kind"))) (← required signed "signed")
  | "float" => return .float (← liftExcept (floatTypeTag (← required float_kind "float_kind")))
  | "pointer" => return .pointer (← required address_space "address_space")
  | _ => fail s!"{path}: unrecognized register primitive hint"

private structure ParseAbiRegisterKindFields where
  kind : Option (String) := none
  hint_element : Option (Option AbiRegisterHint) := none

private def parseAbiRegisterKind (path : String) : Parser (AbiRegisterKind × Option AbiRegisterHint) := do
  let s ← object (ParseAbiRegisterKindFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "hint_element" => return { s with hint_element := some (← nullable (parseAbiRegisterHint (path ++ ".hint_element"))) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let hint_element ← pure (s.hint_element.getD none)
  if kind == "vector" then
    let _ ← required hint_element "hint_element"
    pure ()
  else if s.hint_element.isSome then
    fail s!"{path}: hint_element belongs only to vector registers"
  return (← liftExcept (abiRegisterKind kind), hint_element)

private structure ParseAbiRegisterFields where
  kind : Option (AbiRegisterKind × Option AbiRegisterHint) := none
  size_bits : Option (Nat) := none

def parseAbiRegister (path : String) : Parser (AbiRegister) := do
  let s ← object (ParseAbiRegisterFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← parseAbiRegisterKind (path ++ ".kind")) }
    | "size_bits" => return { s with size_bits := some (← natural) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let size_bits ← required s.size_bits (path ++ ".size_bits")
  return ⟨kind.1, size_bits, kind.2⟩

private structure ParseAbiCastTargetFields where
  prefix_registers : Option (Array AbiRegister) := none
  rest_offset_bytes : Option (Option Nat) := none
  rest_register : Option (AbiRegister) := none
  rest_total_bytes : Option (Nat) := none
  rest_is_consecutive : Option (Bool) := none
  attributes : Option (AbiAttributes) := none

def parseAbiCastTarget (path : String) : Parser (AbiCastTarget) := do
  let s ← object (ParseAbiCastTargetFields.mk none none none none none none) fun s key => do
    match key with
    | "prefix_registers" => return { s with prefix_registers := some (← array (parseAbiRegister (path ++ ".prefix_registers"))) }
    | "rest_offset_bytes" => return { s with rest_offset_bytes := some (← nullable natural) }
    | "rest_register" => return { s with rest_register := some (← parseAbiRegister (path ++ ".rest_register")) }
    | "rest_total_bytes" => return { s with rest_total_bytes := some (← natural) }
    | "rest_is_consecutive" => return { s with rest_is_consecutive := some (← boolean) }
    | "attributes" => return { s with attributes := some (← parseAbiAttributes (path ++ ".attributes")) }
    | _ => skipValue; pure s
  let prefix_registers ← required s.prefix_registers (path ++ ".prefix_registers")
  let rest_offset_bytes ← pure (s.rest_offset_bytes.getD none)
  let rest_register ← required s.rest_register (path ++ ".rest_register")
  let rest_total_bytes ← required s.rest_total_bytes (path ++ ".rest_total_bytes")
  let rest_is_consecutive ← required s.rest_is_consecutive (path ++ ".rest_is_consecutive")
  let attributes ← required s.attributes (path ++ ".attributes")
  return ⟨prefix_registers, rest_offset_bytes, rest_register, rest_total_bytes, rest_is_consecutive, attributes⟩

private structure ParseAbiPassModeFields where
  kind : Option (String) := none
  attributes : Option (Option AbiAttributes) := none
  first : Option (Option AbiAttributes) := none
  second : Option (Option AbiAttributes) := none
  metadata_attributes : Option (Option AbiAttributes) := none
  target : Option (Option AbiCastTarget) := none
  mode : Option (Option IndirectModeKind) := none
  pad_i32_count : Option (Option Nat) := none
  address_space : Option (Option Nat) := none

def parseAbiPassMode (path : String) : Parser (AbiPassMode) := do
  let s ← object (ParseAbiPassModeFields.mk none none none none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with kind := some (← string) }
    | "attributes" => return { s with attributes := some (← nullable (parseAbiAttributes (path ++ ".attributes"))) }
    | "first" => return { s with first := some (← nullable (parseAbiAttributes (path ++ ".first"))) }
    | "second" => return { s with second := some (← nullable (parseAbiAttributes (path ++ ".second"))) }
    | "metadata_attributes" => return { s with metadata_attributes := some (← nullable (parseAbiAttributes (path ++ ".metadata_attributes"))) }
    | "target" => return { s with target := some (← nullable (parseAbiCastTarget (path ++ ".target"))) }
    | "mode" => return { s with mode := some (← nullable (parseIndirectMode (path ++ ".mode"))) }
    | "pad_i32_count" => return { s with pad_i32_count := some (← nullable natural) }
    | "address_space" => return { s with address_space := some (← nullable natural) }
    | _ => skipValue; pure s
  let kind ← required s.kind (path ++ ".kind")
  let attributes ← pure (s.attributes.getD none)
  let first ← pure (s.first.getD none)
  let second ← pure (s.second.getD none)
  let metadata_attributes ← pure (s.metadata_attributes.getD none)
  let target ← pure (s.target.getD none)
  let mode ← pure (s.mode.getD none)
  let pad_i32_count ← pure (s.pad_i32_count.getD none)
  let address_space ← pure (s.address_space.getD none)
  let kind ← liftExcept (passModeKind kind)
  let allowed : List String := match kind with
    | .ignore => []
    | .direct => ["attributes"]
    | .pair => ["first", "second"]
    | .cast => ["target", "pad_i32_count"]
    | .indirect => ["attributes", "address_space", "mode"]
    | .indirectUnsized => ["attributes", "metadata_attributes"]
  if s.attributes.isSome && !(allowed.contains "attributes") then fail s!"{path}: field `attributes` is incompatible with the selected variant"
  if s.first.isSome && !(allowed.contains "first") then fail s!"{path}: field `first` is incompatible with the selected variant"
  if s.second.isSome && !(allowed.contains "second") then fail s!"{path}: field `second` is incompatible with the selected variant"
  if s.metadata_attributes.isSome && !(allowed.contains "metadata_attributes") then fail s!"{path}: field `metadata_attributes` is incompatible with the selected variant"
  if s.target.isSome && !(allowed.contains "target") then fail s!"{path}: field `target` is incompatible with the selected variant"
  if s.mode.isSome && !(allowed.contains "mode") then fail s!"{path}: field `mode` is incompatible with the selected variant"
  if s.pad_i32_count.isSome && !(allowed.contains "pad_i32_count") then fail s!"{path}: field `pad_i32_count` is incompatible with the selected variant"
  if s.address_space.isSome && !(allowed.contains "address_space") then fail s!"{path}: field `address_space` is incompatible with the selected variant"
  match kind with
  | .direct | .indirect => let _ ← required attributes "attributes"; pure ()
  | .pair => let _ ← required first "first"; let _ ← required second "second"; pure ()
  | .indirectUnsized => let _ ← required attributes "attributes"; let _ ← required metadata_attributes "metadata_attributes"; pure ()
  | _ => pure ()
  match kind with
  | .cast => unless target.isSome && pad_i32_count.isSome do fail s!"{path}: Cast pass mode is missing target/padding data"
  | .indirect => unless mode.isSome do fail s!"{path}: Indirect pass mode is missing its mode tag"
  | _ => pure ()
  return ⟨kind, #[attributes, first, second, metadata_attributes].filterMap id, target, pad_i32_count, address_space, mode⟩

private structure ParseAbiArgumentFields where
  type : Option (Nat) := none
  layout : Option (Nat) := none
  mode : Option (AbiPassMode) := none

def parseAbiArgument (path : String) : Parser (AbiArgument) := do
  let s ← object (ParseAbiArgumentFields.mk none none none) fun s key => do
    match key with
    | "type" => return { s with type := some (← natural) }
    | "layout" => return { s with layout := some (← natural) }
    | "mode" => return { s with mode := some (← parseAbiPassMode (path ++ ".mode")) }
    | _ => skipValue; pure s
  let type ← required s.type (path ++ ".type")
  let layout ← required s.layout (path ++ ".layout")
  let mode ← required s.mode (path ++ ".mode")
  return ⟨type, layout, mode⟩

private structure ParseFunctionAbiFields where
  arguments : Option (Array AbiArgument) := none
  returnValue : Option (AbiArgument) := none
  calling_convention : Option (CanonicalAbi) := none
  can_unwind : Option (Bool) := none
  c_variadic : Option (Bool) := none
  fixed_count : Option (Nat) := none

def parseFunctionAbi (path : String) : Parser FunctionAbi := do
  let argument := parseAbiArgument
  let s ← object (ParseFunctionAbiFields.mk none none none none none none) fun s key => do
    match key with
    | "arguments" => return { s with arguments := some (← arrayIndexed (fun i => argument s!"{path}.arguments[{i}]")) }
    | "return" => return { s with returnValue := some (← argument (path ++ ".return")) }
    | "calling_convention" => return { s with calling_convention := some (← parseCanonicalAbi (path ++ ".calling_convention")) }
    | "can_unwind" => return { s with can_unwind := some (← boolean) }
    | "c_variadic" => return { s with c_variadic := some (← boolean) }
    | "fixed_count" => return { s with fixed_count := some (← natural) }
    | _ => skipValue; pure s
  let arguments ← required s.arguments (path ++ ".arguments")
  let returnValue ← required s.returnValue (path ++ ".returnValue")
  let calling_convention ← required s.calling_convention (path ++ ".calling_convention")
  let can_unwind ← required s.can_unwind (path ++ ".can_unwind")
  let c_variadic ← required s.c_variadic (path ++ ".c_variadic")
  let fixed_count ← required s.fixed_count (path ++ ".fixed_count")
  return ⟨arguments, returnValue, calling_convention, can_unwind, c_variadic, fixed_count⟩

def decodeCompilerFunctionAbi : Parser FunctionAbi := parseFunctionAbi "$.compiler_fn_abi"
abbrev RuntimeResult := Except RuntimeMetadataError
private def require (value : Option A) (path : String) : RuntimeResult A := RuntimeMetadata.require value path
private def invalid (path message : String) : RuntimeMetadataError := .invalid path message
private def requireAbi (value : Option A) (message : String) : Except String A :=
  match value with | some value => pure value | none => throw message

def attributes (source : AbiAttributes) : RuntimeResult ArgAttributes := do
  if source.regularBits >= 2^16 then throw (invalid "regular attributes" "u16 overflow")
  let regular := UInt16.ofNat source.regularBits
  let extension := match source.argExtension with
    | .none => ArgExtension.None
    | .zeroExtend => .Zext
    | .signExtend => .Sext
  let align ← source.pointeeAlignBytes.mapM RuntimeMetadata.alignment
  return ⟨regular,extension,← RuntimeMetadata.size source.pointeeSizeBytes,align⟩

private def hintPrimitive (source : AbiRegisterHint) : RuntimeResult Primitive := do
  match source with
  | .integer (.known kind) signed => return .Int (← RuntimeMetadata.integer kind) signed
  | .float kind => return .Float (← RuntimeMetadata.float kind)
  | .pointer addressSpace => return .Pointer ⟨← RuntimeMetadata.u32 addressSpace "hint address space"⟩

def register (source : AbiRegister) : RuntimeResult Reg := do
  let kind ← match source.kind with
    | .integer => pure RegKind.Integer | .float => pure .Float | .ppcF128 => pure .PpcF128
    | .vector => pure (RegKind.Vector (hintVectorElem := ← hintPrimitive (← require source.hintElement "register hint")))
  return ⟨kind,Size.fromBits (← RuntimeMetadata.u64 source.sizeBits "register bits")⟩

def castTarget (source : AbiCastTarget) : RuntimeResult CastTarget := do
  if source.prefixRegisters.size > 8 then throw (invalid "cast prefix" "exceeds source ArrayVec capacity")
  return {
    «prefix» := ← source.prefixRegisters.mapM register
    restOffset := ← source.restOffsetBytes.mapM RuntimeMetadata.size
    rest := ⟨← register source.restRegister,← RuntimeMetadata.size source.restTotalBytes,source.restIsConsecutive⟩
    attrs := ← attributes source.attributes }

def passMode (source : AbiPassMode) : RuntimeResult PassMode := do
  let expected ← match source.kind with
    | .ignore | .cast => pure 0
    | .direct | .indirect => pure 1
    | .pair | .indirectUnsized => pure 2
  if source.attributes.size != expected then throw (invalid "pass attributes" "arity mismatch")
  let attrsAt (index : Nat) := do attributes (← require source.attributes[index]? s!"pass attributes {index}")
  match source.kind with
  | .ignore => pure .Ignore
  | .direct => return .Direct (← attrsAt 0)
  | .pair => return .Pair (← attrsAt 0) (← attrsAt 1)
  | .cast =>
    let pad ← require source.padI32Count "cast.pad_i32_count"
    if pad >= 256 then throw (invalid "cast padding" "u8 overflow")
    return .Cast (UInt8.ofNat pad) (← castTarget (← require source.castTarget "cast.target"))
  | .indirect =>
    let mode ← require source.indirectMode "indirect mode"
    let mode := match mode with
      | .pointer => IndirectMode.Pointer | .onStack => .OnStack
      | .amdgpuKernelArgument => .AmdgpuKernelArg
    let space ← source.addressSpace.mapM (fun n => AddressSpace.mk <$> RuntimeMetadata.u32 n "indirect address space")
    return .Indirect (← attrsAt 0) space mode
  | .indirectUnsized => return .IndirectUnsized (← attrsAt 0) (← attrsAt 1)

def argument (runtime : RuntimeMetadata) (layouts : Array Layout) (source : AbiArgument) : RuntimeResult (ArgAbi TypeId) := do
  let _ ← runtime.node source.typeId
  let sourceLayout ← RuntimeMetadata.require layouts[source.layoutId]? "oracle physical layout"
  let layout ← RuntimeMetadata.layout runtime.target sourceLayout
  return ⟨⟨source.typeId,layout⟩,← passMode source.mode⟩

def convention (source : CanonicalAbi) : Except String CanonAbi := do
  match source.kind with
  | .c => pure .C | .rust => pure .Rust | .rustCold => pure .RustCold
  | .rustPreserveNone => pure .RustPreserveNone | .rustTail => pure .RustTail
  | .custom => pure .Custom | .swift => pure .Swift | .gpuKernel => pure .GpuKernel
  | .arm =>
    let call ← requireAbi source.armCall "missing Arm calling convention"
    return .Arm (← match call with
      | .aapcs => pure ArmCall.Aapcs | .cmseNonSecureCall => pure .CCmseNonSecureCall
      | .cmseNonSecureEntry => pure .CCmseNonSecureEntry)
  | .interrupt =>
    let kind ← requireAbi source.interruptKind "missing interrupt calling convention"
    return .Interrupt (← match kind with
      | .avr => pure InterruptKind.Avr | .avrNonBlocking => pure .AvrNonBlocking
      | .msp430 => pure .Msp430 | .riscvMachine => pure .RiscvMachine
      | .riscvSupervisor => pure .RiscvSupervisor | .x86 => pure .X86)
  | .x86 =>
    let call ← requireAbi source.x86Call "missing x86 calling convention"
    return .X86 (← match call with
      | .fastcall => pure X86Call.Fastcall | .stdcall => pure .Stdcall | .sysv64 => pure .SysV64
      | .thiscall => pure .Thiscall | .vectorcall => pure .Vectorcall | .win64 => pure .Win64)

def functionAbi (runtime : RuntimeMetadata) (layouts : Array Layout) (source : FunctionAbi) : Except String (FnAbi TypeId) := do
  let args ← source.arguments.mapM fun sourceArg => (argument runtime layouts sourceArg).mapError toString
  let ret ← (argument runtime layouts source.returnValue).mapError toString
  if source.fixedCount >= 2^32 then throw "FnAbi.fixed_count exceeds u32"
  if source.fixedCount > args.size then throw "FnAbi.fixed_count exceeds actual arguments"
  -- rustc's physical `FnAbi.args` can include the compiler-injected caller
  -- location while `fixed_count` counts only explicit source arguments.
  -- Preserve both exact facts here; demanded call initialization validates
  -- their relationship against the exact `requires_caller_location` query.
  return ⟨args,ret,source.cVariadic,UInt32.ofNat source.fixedCount,← convention source.callingConvention,source.canUnwind⟩

end Miri.Input.OracleAbi
