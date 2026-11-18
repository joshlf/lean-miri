import Miri.Verification.EffectSpecs
import MiriTests.ControlFlow.Transitions

/-! Default vcgen routing for the additional operations used by duplicate_prefix
and its retained callees. -/
namespace MiriTests.Verification.DuplicatePrefixOps

open Miri.MIR Miri.Interpreter
open Miri.Verification.StepWP Miri.Verification.EffectSpecs Std.WP
set_option experimental.vcgen true

variable {P L E M C V : Type}
local notation "S" => StepState P L E M
local notation "H" => StepHooks P L E M C V

example (hooks : H) (allowed : S → C → Prop) (id : LocalId)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S)
    (matched : (Instruction.statement (.StorageLive id)).matches before)
    (next : transitionPre allowed true
      (fun c => Step.finishStatement (before.stack.frames.size - 1) (hooks.storageLive c id before))
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.StorageLive id)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨matched, next⟩

example (hooks : H) (allowed : S → C → Prop) (id : LocalId)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S)
    (matched : (Instruction.statement (.StorageDead id)).matches before)
    (next : transitionPre allowed true
      (fun c => Step.finishStatement (before.stack.frames.size - 1) (hooks.storageDead c id before))
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.StorageDead id)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨matched, next⟩

example (hooks : H) (allowed : S → C → Prop) (place : Place)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S)
    (matched : (Instruction.statement (.PlaceMention place)).matches before)
    (next : transitionPre allowed true
      (fun c => Step.finishStatement (before.stack.frames.size - 1) ((let result := hooks.evalPlace c place false before
        (result.1, result.2.map fun _ => ()))))
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.PlaceMention place)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨matched, next⟩

example (hooks : H) (allowed : S → C → Prop) (args : CopyNonOverlapping)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S)
    (matched : (Instruction.statement (.Intrinsic (.CopyNonOverlapping args))).matches before)
    (next : transitionPre allowed true
      (fun c => Step.finishStatement (before.stack.frames.size - 1) (hooks.intrinsic c (.CopyNonOverlapping args) before))
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.Intrinsic (.CopyNonOverlapping args))))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨matched, next⟩

example (hooks : H) (allowed : S → C → Prop) (operand : Operand) (targets : SwitchTargets)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S) (term : Terminator)
    (selected : currentTerminator before = some term) (kind : term.kind = .SwitchInt operand targets)
    (next : transitionPre allowed true (fun c => Step.runTerminator hooks c term before)
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.terminator (.SwitchInt operand targets)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨term, selected, kind, next⟩

example (hooks : H) (allowed : S → C → Prop) (cond : Operand) (expected : Bool) (message : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S) (term : Terminator)
    (selected : currentTerminator before = some term) (kind : term.kind = .Assert cond expected message target unwind)
    (next : transitionPre allowed true (fun c => Step.runTerminator hooks c term before)
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.terminator (.Assert cond expected message target unwind)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨term, selected, kind, next⟩

example (hooks : H) (allowed : S → C → Prop) (callee : Operand) (args : Array SpannedOperand) (dest : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) (source : CallSource) (span : SpanRef)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S) (term : Terminator)
    (selected : currentTerminator before = some term) (kind : term.kind = .Call callee args dest target unwind source span)
    (next : transitionPre allowed true (fun c => Step.runTerminator hooks c term before)
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.terminator (.Call callee args dest target unwind source span)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨term, selected, kind, next⟩

example (hooks : H) (allowed : S → C → Prop) (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
    (replace : Bool) (asyncDrop : Option BasicBlockId)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S) (term : Terminator)
    (selected : currentTerminator before = some term) (kind : term.kind = .Drop place target unwind replace asyncDrop)
    (next : transitionPre allowed true (fun c => Step.runTerminator hooks c term before)
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.terminator (.Drop place target unwind replace asyncDrop)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨term, selected, kind, next⟩

example (hooks : ControlTests.H) (before : ControlTests.S)
    (place : Place) (target resume : BasicBlockId) (unwind : UnwindAction) :
    Triple (toEffect (ControlFlow.evalDrop hooks () place target unwind (some resume)))
      (· = before) (fun _ _ => False)
      (fun error after =>
        error = .invalidProgram "Async Drop must be expanded or reset to sync" ∧ after = before) := by
  vcgen with finish

open Miri.Memory Miri.ABI

/-- A symbolic Use goes through place evaluation, operand evaluation and the
registered copy effect without opening the rvalue dispatcher by hand. -/
private def copyFixture (base : RvalueHooks Unit Nat Unit Unit)
    (layout : TyAndLayout TyId) (op : OpTy Unit) : RvalueHooks Unit Nat Unit Unit :=
  { base with
    placeLayout := fun _ => layout
    evalPlace := fun _ _ _ => pure ()
    evalOperand := fun _ _ _ => pure op
    withRetagMode := fun _ _ action => action
    copyOp := fun _ _ _ => set 7 }
example (base : RvalueHooks Unit Nat Unit Unit) (layout : TyAndLayout TyId) (op : OpTy Unit)
    (operand : Operand) (destination : Place) :
    Triple (evalRvalueIntoPlace (copyFixture base layout op) () (.Use operand .Yes) destination)
      (fun _ => True) (fun _ after => after = 7) (fun _ _ => False) := by
  vcgen (errorOnMissingSpec := false)
  all_goals
    simp [wp, WP.wpTrans, copyFixture, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      set, MonadStateOf.set, EStateM.set]

end MiriTests.Verification.DuplicatePrefixOps
