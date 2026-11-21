import Jihoo.NativeCoreCodeApplication
import Jihoo.NativeCoreCodePartialApplication

/-! Runtime application inference keeps the original instantiated
codomain. A function-valued top result performs the authenticated
partial-application scan, while an inner spine segment returns directly. -/
namespace Jihoo.NativeKernel.NativeCoreCodeApplicationFinalization

open NativeArena Environment
open NativeCoreTransformExact (State)
open NativeCorePureComputationNormal (Outcome Progress ExpandedNormalization)
open NativeCoreBinderTraversal (VisitsFrom)
open NativeCoreGhostSpineInference (Infer Visit Inferred RetainedComparisons next_progress)

def finish (ghost : Infer) (normal : Visit) (boxed : Nat → Bool) (state : State)
    (candidate root : Nat) (head : Bool) : Outcome (List (Nat × Nat)) :=
  if head then ⟨state,.ok []⟩
  else
    (normal state candidate).next fun exposed selected =>
      match exposed.arena[selected]? with
      | some (.node (.pi _) _) => NativeCoreCodePartialApplication.run ghost normal boxed exposed root
      | _ => ⟨exposed,.ok []⟩

theorem finish_progress
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (room : state.steps ≤ limit) :
    Progress limit state (finish ghost normal boxed state candidate root head) := by
  unfold finish
  split
  · exact Progress.atState _ _
  · apply next_progress (normalProgress _ _) room
    intro _ _ exposedRoom
    split
    · exact NativeCoreCodePartialApplication.run_progress ghostProgress normalProgress exposedRoom
    · exact Progress.atState _ _

private theorem linearity_backward
    (normalBackward : ∀ {state root answer}, (normal state root).result = .ok answer →
      Backward state.arena → Backward (normal state root).state.arena)
    (accepted : (NativeCoreCodeLinearity.run normal boxed state domain).result = .ok linear)
    (backward : Backward state.arena) :
    Backward (NativeCoreCodeLinearity.run normal boxed state domain).state.arena := by
  unfold NativeCoreCodeLinearity.run at accepted ⊢
  obtain ⟨candidate,normalized,next⟩ := Outcome.next_success accepted
  rw [next] at accepted ⊢
  split at accepted
  · rename_i pairType
    simp only [ite_eq_left pairType]
    exact normalBackward normalized backward
  · rename_i ordinary
    simp only [ite_eq_right ordinary]
    obtain ⟨selected,again,finished⟩ := Outcome.next_success accepted
    rw [finished]
    exact normalBackward again (normalBackward normalized backward)

private theorem visits_backward
    (ghostBackward : ∀ {state root answer}, (ghost state root).result = .ok answer →
      Backward state.arena → Backward (ghost state root).state.arena)
    (normalBackward : ∀ {state root answer}, (normal state root).result = .ok answer →
      Backward state.arena → Backward (normal state root).state.arena)
    (visited : NativeCoreCodePartialApplication.Visits ghost normal boxed source state root final pairs)
    (backward : Backward state.arena) : Backward final.arena := by
  induction visited with
  | head => exact backward
  | stops _ inferred normalized _ => exact normalBackward normalized (ghostBackward inferred backward)
  | erased _ inferred normalized _ _ ih => exact ih (normalBackward normalized (ghostBackward inferred backward))
  | relevant _ inferred normalized _ tested _ ih =>
    exact ih (linearity_backward normalBackward tested (normalBackward normalized (ghostBackward inferred backward)))

theorem finish_backward
    (ghostBackward : ∀ {state root answer}, (ghost state root).result = .ok answer →
      Backward state.arena → Backward (ghost state root).state.arena)
    (normalBackward : ∀ {state root answer}, (normal state root).result = .ok answer →
      Backward state.arena → Backward (normal state root).state.arena)
    (success : (finish ghost normal boxed state candidate root head).result = .ok pairs)
    (backward : Backward state.arena) :
    Backward (finish ghost normal boxed state candidate root head).state.arena := by
  unfold finish at success ⊢
  split at success
  · rename_i inner
    simp only [ite_eq_left inner]
    exact backward
  · rename_i top
    simp only [ite_eq_right top]
    obtain ⟨selected,normalized,entered⟩ := Outcome.next_success success
    rw [entered] at success ⊢
    split at success
    · have replayed := (NativeCoreCodePartialApplication.run_visits success).2
      exact visits_backward ghostBackward normalBackward replayed (normalBackward normalized backward)
    · exact normalBackward normalized backward

def run (functionInfer : Infer) (argumentInfer : Bool → Infer) (ghost : Infer)
    (normal : Nat → Visit) (env : Environment) (boxed : Nat → Bool) (limit depth : Nat)
    (state : State) (root function argument : Nat) (head : Bool) : Outcome Inferred :=
  (NativeCoreCodeApplication.run functionInfer argumentInfer normal env limit depth state root function argument true).next
    fun instantiated initial =>
      (finish ghost (normal depth) boxed instantiated initial.typeRoot root head).next fun after comparisons =>
        ⟨after,.ok ⟨initial.typeRoot,initial.compared ++ comparisons⟩⟩

theorem run_progress
    (calleeProgress : ∀ state root, state.steps ≤ limit → Progress limit state (functionInfer state root))
    (argumentProgress : ∀ mode state root, state.steps ≤ limit → Progress limit state (argumentInfer mode state root))
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (room : state.steps ≤ limit) :
    Progress limit state (run functionInfer argumentInfer ghost normal env boxed limit depth state root function argument head) := by
  unfold run
  apply next_progress (NativeCoreCodeApplication.run_progress calleeProgress argumentProgress normalProgress room) room
  intro _ _ instantiatedRoom
  exact (finish_progress ghostProgress (normalProgress depth) instantiatedRoom).next (fun _ => Progress.atState _ _)

/-- The result still denotes the original substituted codomain.
The application typing follows the same checked callee and argument. -/
theorem run_refines (wf : UnifiedProgram.EnvWellFormed env)
    (free : NativeCoreCodeArgumentPolicy.GlobalFreeOutputs base normal)
    (normalSound : ∀ depth, VisitsFrom base (ExpandedNormalization env) (normal depth))
    (normalProgress : ∀ depth state root, Progress limit state (normal depth state root))
    (calleeSound : NativeCoreCodeApplication.Sound env loans base ctx limit false functionInfer)
    (argumentSound : ∀ mode, NativeCoreCodeApplication.Sound env loans base ctx limit mode (argumentInfer mode))
    (calleeProgress : ∀ state root, state.steps ≤ limit → Progress limit state (functionInfer state root))
    (argumentProgress : ∀ mode state root, state.steps ≤ limit → Progress limit state (argumentInfer mode state root))
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (ghostBackward : ∀ {state root answer}, (ghost state root).result = .ok answer →
      Backward state.arena → Backward (ghost state root).state.arena)
    (normalBackward : ∀ {state root answer}, (normal depth state root).result = .ok answer →
      Backward state.arena → Backward (normal depth state root).state.arena)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (fn : Represents state.arena function f) (arg : Represents state.arena argument a)
    (success : (run functionInfer argumentInfer ghost normal env boxed limit depth state root function argument head).result =
      .ok answer)
    (ambient : Prefix
      (run functionInfer argumentInfer ghost normal env boxed limit depth state root function argument head).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (run functionInfer argumentInfer ghost normal env boxed limit depth state root function argument head).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧ ∃ type, Represents after answer.typeRoot type ∧ LoanTyping.HasType env loans ctx false
      (.app (EnvironmentDelta.expand env f) (EnvironmentDelta.expand env a)) (EnvironmentDelta.expand env type) := by
  unfold run at success ambient ⊢
  obtain ⟨initial,initialOk,initialNext⟩ := Outcome.next_success success
  rw [initialNext] at success ambient ⊢
  obtain ⟨comparisons,checked,finishNext⟩ := Outcome.next_success success
  rw [finishNext] at success ambient ⊢
  simp only [Except.ok.injEq] at success
  subst answer
  let instantiated := NativeCoreCodeApplication.run functionInfer argumentInfer normal env limit depth state root function argument true
  have initialCost := NativeCoreCodeApplication.run_progress (env := env) (depth := depth) (state := state)
    (root := root) (function := function) (argument := argument) (head := true)
    calleeProgress argumentProgress normalProgress room
  have within := initialCost.accepted room initial initialOk
  have finishCost := finish_progress (state := instantiated.state) (candidate := initial.typeRoot)
    (root := root) (head := head) (boxed := boxed) ghostProgress (normalProgress depth) within
  obtain ⟨kept,initialBackward,type,represented,typed⟩ := NativeCoreCodeApplication.run_refines wf free normalSound normalProgress
    calleeSound argumentSound calleeProgress argumentProgress onBase room fn arg initialOk
    (finishCost.kept.trans ambient) (fun pair member => retained pair (List.mem_append_left _ member))
  exact ⟨kept.trans finishCost.kept,finish_backward ghostBackward normalBackward checked ∘ initialBackward,
    type,represented.frame finishCost.kept,typed⟩

end Jihoo.NativeKernel.NativeCoreCodeApplicationFinalization
