import Miri.Input.Model.SourceTypes

/-! Typed generic MIR source. Type/definition/span references belong to immutable
source tables, never executable runtime pools. Unsupported syntax is retained as
a typed tag; consumers must fail at demand, never replace it with a no-op. -/
namespace Miri.Input.SourceMir
abbrev TypeRef := SourceTypes.TypeRef
abbrev DefinitionRef := SourceTypes.DefinitionRef

structure SpanKey where
  lo : Nat
  hi : Nat
  context : String
  parentLocalDefinition : Option Nat
  deriving Repr, DecidableEq
structure Span where
  identity : Nat
  key : SpanKey
  isDummy : Bool
  file : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, DecidableEq
structure SourceInfo where
  span : Nat
  scope : Nat
  deriving Repr, DecidableEq
structure Backtrace where
  span : Nat
  bytePosition : Nat
  line : Nat
  column : Nat
  filename : String
  deriving Repr, DecidableEq
structure Scope where
  span : Nat
  parent : Option Nat
  inlinedParent : Option Nat
  deriving Repr, DecidableEq
inductive Phase where
  | known (value : MIR.MirPhase)
  | unsupported (kind : String)
  deriving Repr, DecidableEq

inductive Projection where
  | deref
  | field (index : Nat) (type : TypeRef)
  | index (localId : Nat)
  | unsupported (kind : String)
  deriving Repr, DecidableEq
structure Place where
  localId : Nat
  projection : Array Projection
  deriving Repr, DecidableEq
inductive ConstantValue where
  | zeroSized
  | scalar (bits sizeBytes : Nat)
  | typeConstant (expression : SourceTypes.ConstExpr)
  | unevaluated (definition : DefinitionRef) (arguments : Array SourceTypes.Argument) (promoted : Option Nat)
  | unsupported (kind : String)
  deriving Repr, DecidableEq
structure Constant where
  type : TypeRef
  value : ConstantValue
  span : SpanKey
  userType : Option Nat
  deriving Repr, DecidableEq
inductive Operand where
  | copy (place : Place)
  | move (place : Place)
  | constant (value : Constant)
  | unsupported (kind : String)
  deriving Repr, DecidableEq
inductive Operator (α : Type) where
  | known (value : α)
  | unsupported (kind : String)
  deriving Repr, DecidableEq
inductive Rvalue where
  | use (operand : Operand) (retag : Bool)
  | reference (region : SourceTypes.Region) (borrow : Operator MIR.BorrowKind) (place : Place)
  | binary (operator : Operator MIR.BinOp) (left right : Operand)
  | unary (operator : Operator MIR.UnOp) (operand : Operand)
  | repeat (operand : Operand) (count : SourceTypes.ConstExpr)
  | discriminant (place : Place)
  | aggregateTuple (operands : Array Operand)
  | aggregateClosure (definition : DefinitionRef) (arguments : Array SourceTypes.Argument) (operands : Array Operand)
  | unsize (operand : Operand) (target : TypeRef) (source : Operator MIR.CoercionSource)
  | unsupported (kind : String)
  deriving Repr, DecidableEq
inductive StatementKind where
  | assign (destination : Place) (value : Rvalue)
  | storageLive (localId : Nat)
  | storageDead (localId : Nat)
  | nop
  | unsupported (kind : String)
  deriving Repr, DecidableEq
structure Statement where
  source : SourceInfo
  kind : StatementKind
  deriving Repr, DecidableEq
inductive Unwind where
  | continueUnwind | unreachable | cleanup (target : Nat)
  | terminate (reason : Operator MIR.UnwindTerminateReason)
  | unsupported (kind : String)
  deriving Repr, DecidableEq
structure SpannedOperand where
  operand : Operand
  span : Nat
  deriving Repr, DecidableEq
inductive TerminatorKind where
  | returnValue
  | terminateUnwind (reason : Operator MIR.UnwindTerminateReason)
  | goto (target : Nat)
  | resumeUnwind
  | unreachable
  | call (function : Operand) (arguments : Array SpannedOperand) (destination : Place)
      (target : Option Nat) (unwind : Unwind) (source : Operator MIR.CallSource) (functionSpan : Nat)
  | drop (place : Place) (target : Nat) (unwind : Unwind) (replace : Bool) (asyncDrop : Option Nat)
  | switchInt (discriminant : Operand) (values : Array (Nat × Nat)) (otherwise : Nat)
  | unsupported (kind : String)
  deriving Repr, DecidableEq
structure Terminator where
  source : SourceInfo
  kind : TerminatorKind
  deriving Repr, DecidableEq
structure Block where
  cleanup : Bool
  statements : Array Statement
  terminator : Terminator
  deriving Repr, DecidableEq
structure Local where
  type : TypeRef
  mutable : Bool
  source : SourceInfo
  deriving Repr, DecidableEq
structure Body where
  definition : DefinitionId
  promoted : Option Nat
  promotedCount : Nat
  phase : Phase
  injectionPhase : Option Phase
  argumentCount : Nat
  spreadArgument : Option Nat
  bodySpan : Nat
  definitionSpan : Nat
  spans : Array Span
  scopes : Array Scope
  backtraces : Array Backtrace
  locals : Array Local
  blocks : Array Block
  requiredConstants : Array Constant
  deriving Repr, DecidableEq

structure Material where
  rootSpan : Span
  bodies : Array Body
  deriving Repr, DecidableEq
end Miri.Input.SourceMir
