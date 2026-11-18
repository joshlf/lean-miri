import Miri.Verification.FunctionBody
import Std.Tactic.Do
import Std.WP

/-! Verification conditions for finite sequences of interpreter steps. Each
step uses the existing driver and quantifies over its permitted choices. -/
namespace Miri.Verification.StepWP

open Miri.Interpreter Miri.MIR
open Std.WP

variable {P L E M C V : Type}
local notation "State" => StepState P L E M
local notation "Hooks" => StepHooks P L E M C V

inductive Instruction where
  | statement (kind : StatementKind)
  | ret

/-- Check the same frame, block and statement slot that the driver dispatches. -/
def Instruction.matches (instruction : Instruction) (state : State) : Prop :=
  match state.stack.currentFrame? with
  | some frame =>
    match frame.location with
    | .mir loc =>
      match frame.body.basicBlocks[loc.block]? with
      | some block =>
        match instruction, block.statements[loc.statementIndex]? with
        | .statement kind, some stmt => stmt.kind = kind
        | .ret, none => block.terminator.kind = .Return
        | _, _ => False
      | none => False
    | .unwinding _ => False
  | none => False

/-- Each step states the expected driver result: `true` for a step that
continues, `false` for a step that finds an empty stack. -/
inductive Program (hooks : Hooks) (allowed : State → C → Prop) where
  | step (more : Bool)
  | instruction (operation : Instruction)
  | call (prepare : C → State → EStateM.Result StepError State Unit)
  | seq (first next : Program hooks allowed)

variable {hooks : StepHooks P L E M C V} {allowed : StepState P L E M → C → Prop}

/-- Lower a one-block body with a Return terminator. Instruction guards bind
the resulting verification program to the MIR actually stepped. -/
def lowerStraightLine (body : Body) : Option (Program hooks allowed) := do
  let #[block] := body.basicBlocks | none
  let .Return := block.terminator.kind | none
  return block.statements.foldr
    (fun statement next => .seq (.instruction (.statement statement.kind)) next)
    (.instruction .ret)

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

/-- A direct call uses the supplied preparation action, then follows real
driver steps until the callee leaves scope. Every successful scope exit must
satisfy `post`, which can require the normal caller continuation. -/
def callPre (hooks : Hooks) (allowed : State → C → Prop)
    (prepare : C → State → EStateM.Result StepError State Unit)
    (post : State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  (∃ choice, allowed before choice) ∧
    ∀ choice, allowed before choice →
      match prepare choice before with
      | .error error failed => onError error failed
      | .ok () entry =>
        let depth := before.stack.frames.size + 1
        let stackDepth := fun state : State => state.stack.frames.size
        stackDepth entry = depth ∧
          FunctionBody.OnError (Step.step hooks) stackDepth allowed depth entry onError ∧
          FunctionBody.NormalPost (Step.step hooks) stackDepth allowed depth entry post

/-- After each expected successful result, the next command sees the updated state.
Errors go directly to the enclosing error postcondition. -/
def pre : Program hooks allowed → (State → Prop) → (StepError → State → Prop) → State → Prop
  | .step more, post, onError => stepPre hooks allowed more post onError
  | .instruction operation, post, onError =>
    fun state => operation.matches state ∧ stepPre hooks allowed true post onError state
  | .call prepare, post, onError => callPre hooks allowed prepare post onError
  | .seq first next, post, onError => pre first (pre next post onError) onError

theorem stepPre_mono {more : Bool}
    {post post' : State → Prop} {onError onError' : StepError → State → Prop}
    (hpost : ∀ state, post state → post' state)
    (herror : ∀ error state, onError error state → onError' error state)
    (state : State) (h : stepPre hooks allowed more post onError state) :
    stepPre hooks allowed more post' onError' state := by
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

private theorem pre_mono (program : Program hooks allowed)
    {post post' : State → Prop} {onError onError' : StepError → State → Prop}
    (hpost : ∀ state, post state → post' state)
    (herror : ∀ error state, onError error state → onError' error state) :
    ∀ state, pre program post onError state → pre program post' onError' state := by
  induction program generalizing post post' with
  | step more => exact stepPre_mono hpost herror
  | instruction operation =>
    intro state h
    exact ⟨h.1, stepPre_mono hpost herror state h.2⟩
  | call prepare =>
    intro state h
    refine ⟨h.1, fun choice permitted => ?_⟩
    have actual := h.2 choice permitted
    cases outcome : prepare choice state with
    | error error failed =>
      simp only [outcome] at actual ⊢
      exact herror error failed actual
    | ok value entry =>
      cases value
      simp only [outcome] at actual ⊢
      refine ⟨actual.1, ?_, ?_⟩
      · intro before reached inside c enabled after error failed
        exact herror error after (actual.2.1 before reached inside c enabled after error failed)
      · intro after reached outside
        exact hpost after (actual.2.2 after reached outside)
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

@[spec] theorem spec_instruction (hooks : Hooks) (allowed : State → C → Prop)
    (operation : Instruction) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) operation)
      (fun state => operation.matches state ∧ stepPre hooks allowed true (post ()) onError state)
      post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

@[spec] theorem spec_call (hooks : Hooks) (allowed : State → C → Prop)
    (prepare : C → State → EStateM.Result StepError State Unit)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.call (hooks := hooks) (allowed := allowed) prepare)
      (callPre hooks allowed prepare (post ()) onError) post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

/-- A checked two-instruction body ends below its entry stack depth whenever
both instructions succeed. Either can instead leave a classified non-UB error. -/
theorem twoInstructions_body {first second : Instruction} {start : State} {depth : Nat}
    {post : State → Prop} (inside : depth ≤ start.stack.frames.size)
    (firstInScope : ∀ after choice, allowed start choice →
      Step.step hooks choice start = (after, .ok true) → depth ≤ after.stack.frames.size)
    (verified : pre (Program.seq (Program.instruction (hooks := hooks) (allowed := allowed) first)
        (Program.instruction second))
      (fun state => state.stack.frames.size < depth ∧ post state)
      (fun error _ => RunLoop.reportsUB error = false) start) :
    FunctionBody.UBFree (Step.step hooks) (fun state => state.stack.frames.size) allowed depth start ∧
    FunctionBody.NormalPost (Step.step hooks) (fun state => state.stack.frames.size) allowed depth start
      post := by
  let final := fun state : State => state.stack.frames.size < depth ∧ post state
  let onError := fun (error : StepError) (_ : State) => RunLoop.reportsUB error = false
  let pending := fun state => second.matches state ∧ stepPre hooks allowed true final onError state
  let invariant := fun state => state = start ∨
    (depth ≤ state.stack.frames.size ∧ pending state) ∨ final state
  have initially : stepPre hooks allowed true pending onError start := verified.2
  apply FunctionBody.ofInvariant invariant (Or.inl rfl)
  · intro before after choice inv hdepth permitted outcome
    rcases inv with rfl | ⟨_, next⟩ | done
    · have next := (stepPre_outcome initially ⟨choice, permitted, outcome⟩).2
      exact Or.inr (Or.inl ⟨firstInScope after choice permitted outcome, next⟩)
    · exact Or.inr (Or.inr (stepPre_outcome next.2 ⟨choice, permitted, outcome⟩).2)
    · exact False.elim (Nat.not_lt_of_ge hdepth done.1)
  · intro before after choice error inv hdepth permitted outcome
    rcases inv with rfl | ⟨_, next⟩ | done
    · exact stepPre_outcome initially ⟨choice, permitted, outcome⟩
    · exact stepPre_outcome next.2 ⟨choice, permitted, outcome⟩
    · exact False.elim (Nat.not_lt_of_ge hdepth done.1)
  · intro state inv outside
    rcases inv with rfl | ⟨hdepth, _⟩ | done
    · exact False.elim (Nat.not_lt_of_ge inside outside)
    · exact False.elim (Nat.not_lt_of_ge hdepth outside)
    · exact done.2

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
