import Miri.Verification.StepWP
import MiriTests.ControlFlow.Transitions

/-! The control-flow fixture runs the original Step driver and ControlFlow
implementation with fixture callbacks. -/
namespace MiriTests.Verification.StepWP

open Miri.Interpreter Miri.Verification.StepWP Std.WP
open Lean.Order

set_option experimental.vcgen true

private abbrev DriverProgram := Program ControlTests.stepHooks (fun _ _ => True)

private def advance : DriverProgram :=
  .step true

private def stopCheck : DriverProgram :=
  checkEmptyStack ControlTests.stepHooks (fun _ _ => True)

private def noError : StepError → ControlTests.S → Prop := fun _ _ => False

private def entry : ControlTests.S := ControlTests.program ControlTests.fixture

private def afterGoto : ControlTests.S :=
  (Step.step ControlTests.stepHooks () entry).1

private def afterNop : ControlTests.S :=
  (Step.step ControlTests.stepHooks () afterGoto).1

private def afterReturn : ControlTests.S :=
  (Step.step ControlTests.stepHooks () afterNop).1

private def finalPost (_ : Unit) (state : ControlTests.S) : Prop :=
  state.stack.frames.isEmpty = true ∧ state.machine = [9, 9, 1, 2, 3, 4]

/-- The three successful driver iterations are Goto, Nop and Return.
The final iteration checks that the return emptied the stack. -/
theorem gotoNopReturn :
    Triple (Program.seq advance (Program.seq advance (Program.seq advance stopCheck)))
      (fun state => state = entry)
      finalPost noError := by
  vcgen [advance, stopCheck]
  subst_vars
  change stepPre ControlTests.stepHooks (fun _ _ => True) true
    (wp (Program.seq advance (Program.seq advance stopCheck)) finalPost noError) noError entry
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  change true = true ∧
    wp (Program.seq advance (Program.seq advance stopCheck)) finalPost noError afterGoto
  refine ⟨rfl, ⟨⟨(), trivial⟩, ?_⟩⟩
  rintro ⟨⟩ _
  change true = true ∧ wp (Program.seq advance stopCheck) finalPost noError afterNop
  refine ⟨rfl, ⟨⟨(), trivial⟩, ?_⟩⟩
  rintro ⟨⟩ _
  change true = true ∧ wp stopCheck finalPost noError afterReturn
  refine ⟨rfl, ⟨⟨(), trivial⟩, ?_⟩⟩
  rintro ⟨⟩ _
  exact ⟨rfl, rfl, rfl⟩

/-- A symbolic proof can use a registered rule without unfolding the driver. -/
example (state : ControlTests.S) :
    Triple (checkEmptyStack ControlTests.stepHooks (fun _ _ => True))
      (fun before => before = state ∧ before.stack.currentFrame? = none)
      (fun _ after => after = state) noError := by
  vcgen
  rename_i before h
  exact ⟨h.2, ⟨(), trivial⟩, h.1⟩

/-- An empty set of permitted choices fails even with trivial postconditions. -/
example : ¬ stepPre ControlTests.stepHooks (fun _ _ => False) true
    (fun _ => True) (fun _ _ => True) entry := by
  rintro ⟨⟨_, permitted⟩, _⟩
  exact permitted

private def unsupportedHooks := { ControlTests.stepHooks with
  beforeTerminator := fun _ state => (ControlTests.log 99 state, .error (.unsupported "fixture")) }

/-- Errors preserve the state produced by the failing callback. -/
example : stepPre unsupportedHooks (fun _ _ => True) true (fun _ => False)
    (fun error state => error = .unsupported "fixture" ∧ state.machine = [99]) entry := by
  exact ⟨⟨(), trivial⟩, fun _ _ => ⟨rfl, rfl⟩⟩

example : ¬ stepPre unsupportedHooks (fun _ _ => True) true (fun _ => True) noError entry := by
  intro safe
  exact safe.2 () trivial

end MiriTests.Verification.StepWP
