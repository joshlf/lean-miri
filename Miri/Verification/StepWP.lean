import Miri.Interpreter.Step
import Std.Tactic.Do
import Std.WP

/-! Verification conditions for finite sequences of interpreter steps. Each
step uses the existing driver and quantifies over its permitted choices. -/
namespace Miri.Verification.StepWP

open Miri.Interpreter
open Std.WP

variable {P L E M C V : Type}
local notation "State" => StepState P L E M
local notation "Hooks" => StepHooks P L E M C V

/-- Each step states the expected driver result: `true` for a step that
continues, `false` for a step that finds an empty stack. -/
inductive Program (hooks : Hooks) (allowed : State → C → Prop) where
  | step (more : Bool)
  | seq (first next : Program hooks allowed)

variable {hooks : StepHooks P L E M C V} {allowed : StepState P L E M → C → Prop}

/-- Demand a permitted choice and check every permitted result. The driver
state on error is the one supplied to the error postcondition. -/
def stepPre (hooks : Hooks) (allowed : State → C → Prop) (more : Bool)
    (post : State → Prop) (onError : StepError → State → Prop) (state : State) : Prop :=
  (∃ choice, allowed state choice) ∧
    ∀ choice, allowed state choice →
      match Step.step hooks choice state with
      | (after, .ok actual) => actual = more ∧ post after
      | (after, .error error) => onError error after

theorem stepPre_outcome {hooks : Hooks} {allowed : State → C → Prop} {more : Bool}
    {post : State → Prop} {onError : StepError → State → Prop} {before after : State}
    {result : Except StepError Bool} (h : stepPre hooks allowed more post onError before)
    (hstep : Step.AllowedStep hooks allowed before after result) :
    match result with
    | .ok actual => actual = more ∧ post after
    | .error error => onError error after := by
  obtain ⟨choice, permitted, outcome⟩ := hstep
  cases result <;> simpa only [outcome] using h.2 choice permitted

/-- After each expected successful result, the next command sees the updated state.
Errors go directly to the enclosing error postcondition. -/
def pre : Program hooks allowed → (State → Prop) → (StepError → State → Prop) → State → Prop
  | .step more, post, onError => stepPre hooks allowed more post onError
  | .seq first next, post, onError => pre first (pre next post onError) onError

private theorem pre_mono (program : Program hooks allowed)
    {post post' : State → Prop} {onError onError' : StepError → State → Prop}
    (hpost : ∀ state, post state → post' state)
    (herror : ∀ error state, onError error state → onError' error state) :
    ∀ state, pre program post onError state → pre program post' onError' state := by
  induction program generalizing post post' with
  | step more =>
    intro state h
    refine ⟨h.1, fun choice permitted => ?_⟩
    have hresult := h.2 choice permitted
    cases outcome : Step.step hooks choice state with
    | mk after result =>
      cases result with
      | ok actual =>
        simp only [outcome] at hresult ⊢
        exact ⟨hresult.1, hpost after hresult.2⟩
      | error error =>
        simp only [outcome] at hresult ⊢
        exact herror error after hresult
  | seq first next firstIH nextIH =>
    exact firstIH (nextIH hpost)

instance : WP (Program hooks allowed) Unit (StepState P L E M → Prop)
    (StepError → StepState P L E M → Prop) where
  wpTrans program := ⟨fun post onError => pre program (post ()) onError⟩
  wp_trans_monotone program := by
    intro post post' onError onError' herror hpost
    exact pre_mono program (hpost ()) herror

@[spec] theorem spec_step (hooks : Hooks) (allowed : State → C → Prop) (more : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.step (hooks := hooks) (allowed := allowed) more)
      (stepPre hooks allowed more (post ()) onError) post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

@[spec] theorem spec_seq (first next : Program hooks allowed)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.seq first next) (wp first (fun _ => wp next post onError) onError)
      post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

/-- Observe that the driver has no current frame. -/
def checkEmptyStack (hooks : Hooks) (allowed : State → C → Prop) : Program hooks allowed :=
  .step false

@[spec] theorem spec_checkEmptyStack (hooks : Hooks) (allowed : State → C → Prop)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (checkEmptyStack hooks allowed)
      (fun state => state.stack.currentFrame? = none ∧
        (∃ choice, allowed state choice) ∧ post () state) post onError := by
  apply Triple.iff.mpr
  rintro state ⟨empty, enabled, hpost⟩
  change stepPre hooks allowed false (post ()) onError state
  refine ⟨enabled, ?_⟩
  intro choice _
  change (match Step.step hooks choice state with
    | (after, .ok actual) => actual = false ∧ post () after
    | (after, .error error) => onError error after)
  simpa [Step.step, empty] using hpost

end Miri.Verification.StepWP
