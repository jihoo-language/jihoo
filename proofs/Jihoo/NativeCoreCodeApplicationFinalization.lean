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
open NativeCoreGhostSpineInference (Infer Visit Inferred InferSound PairRetained RetainedComparisons next_progress)

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

private theorem visited_prefix
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (visited : NativeCoreCodePartialApplication.Visits ghost normal boxed source state root final pairs)
    (room : state.steps ≤ limit) : Prefix state.arena final.arena := by
  induction visited with
  | head => exact .refl _
  | stops _ inferred normalized _ =>
    exact (ghostProgress _ _ room).kept.trans (normalProgress _ _).kept
  | @erased root state callee answer selected domain body final compared argument read inferred normalized product rest ih =>
    have first := ghostProgress state callee room
    have second := normalProgress (ghost state callee).state answer.typeRoot
    have afterInfer := first.accepted room _ inferred
    have afterNormal := second.accepted afterInfer _ normalized
    exact first.kept.trans (second.kept.trans (ih afterNormal))
  | @relevant root state callee answer selected domain body final compared argument read inferred normalized product tested rest ih =>
    have first := ghostProgress state callee room
    have second := normalProgress (ghost state callee).state answer.typeRoot
    have afterInfer := first.accepted room _ inferred
    have afterNormal := second.accepted afterInfer _ normalized
    have third := NativeCoreCodeLinearity.run_progress (boxed := boxed)
      (state := (normal (ghost state callee).state answer.typeRoot).state) (type := domain) normalProgress
    have afterTest := third.accepted afterNormal _ tested
    exact first.kept.trans (second.kept.trans (third.kept.trans (ih afterTest)))

private theorem first_child (held : Represents arena root term)
    (read : arena[root]? = some (.node op [first,second])) :
    ∃ child, Represents arena first child := by
  cases held with
  | var read' => rw [read] at read'; cases read'
  | node read' _ children =>
    rw [read] at read'
    cases read'
    cases children with
    | cons firstRep rest => exact ⟨_,firstRep⟩

private theorem callee_frame
    (ghostSound : InferSound env base ctx limit ghost)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (rootRep : Represents state.arena root T)
    (read : state.arena[root]? = some (.node .app [callee,argument]))
    (inferred : (ghost state callee).result = .ok answer)
    (normalized : (normal (ghost state callee).state answer.typeRoot).result = .ok selected)
    (ambient : Prefix (ghost state callee).state.arena final)
    (retained : RetainedComparisons final answer) :
    let after := (normal (ghost state callee).state answer.typeRoot).state.arena
    Prefix state.arena after ∧ (Backward state.arena → Backward after) ∧
      ∃ F P, Represents after callee F ∧ Represents after selected P := by
  obtain ⟨F,calleeRep⟩ := first_child rootRep read
  obtain ⟨first,firstBack,_,typeRep,_⟩ := ghostSound onBase room calleeRep inferred ambient retained
  obtain ⟨second,secondBack,returned,represented,_⟩ := normalSound (onBase.trans first) typeRep normalized
  exact ⟨first.trans second,secondBack ∘ firstBack,F,returned,calleeRep.frame (first.trans second),represented⟩

private theorem visits_backward
    (ghostSound : InferSound env base ctx limit ghost)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (metadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (visited : NativeCoreCodePartialApplication.Visits ghost normal boxed source state root final pairs)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit) (rootRep : Represents state.arena root input)
    (ambient : Prefix final.arena total) (retained : ∀ pair ∈ pairs, PairRetained total pair)
    (backward : Backward state.arena) : Backward final.arena := by
  induction visited generalizing input with
  | head => exact backward
  | stops read inferred normalized _ =>
    have after := (normalProgress _ _).kept.trans ambient
    exact (callee_frame ghostSound normalSound onBase room rootRep read inferred normalized after retained).2.1 backward
  | @erased root state callee answer selected domain body final compared argument read inferred normalized product tail ih =>
    have first := ghostProgress state callee room
    have second := normalProgress (ghost state callee).state answer.typeRoot
    have localRoom := second.accepted (first.accepted room _ inferred) _ normalized
    have later := visited_prefix ghostProgress normalProgress tail localRoom
    obtain ⟨kept,safe,_,_,held,_⟩ := callee_frame ghostSound normalSound onBase room rootRep read inferred normalized
      (second.kept.trans (later.trans ambient)) (fun pair member => retained pair (List.mem_append_left _ member))
    exact ih (onBase.trans kept) localRoom held ambient (fun pair member => retained pair (List.mem_append_right _ member)) (safe backward)
  | @relevant root state callee answer selected domain body final compared argument read inferred normalized product tested tail ih =>
    have first := ghostProgress state callee room
    have second := normalProgress (ghost state callee).state answer.typeRoot
    have third := NativeCoreCodeLinearity.run_progress (boxed := boxed)
      (state := (normal (ghost state callee).state answer.typeRoot).state) (type := domain) normalProgress
    have beforeTest := second.accepted (first.accepted room _ inferred) _ normalized
    have localRoom := third.accepted beforeTest _ tested
    have later := visited_prefix ghostProgress normalProgress tail localRoom
    obtain ⟨kept,safe,_,_,held,productRep⟩ := callee_frame ghostSound normalSound onBase room rootRep read inferred normalized
      (second.kept.trans (third.kept.trans (later.trans ambient))) (fun pair member => retained pair (List.mem_append_left _ member))
    obtain ⟨_,domainRep⟩ := first_child productRep product
    obtain ⟨linearityKept,linearityBack,_⟩ := NativeCoreCodeLinearity.run_refines metadata normalSound
      (onBase.trans kept) domainRep tested
    exact ih (onBase.trans (kept.trans linearityKept)) localRoom (held.frame linearityKept) ambient
      (fun pair member => retained pair (List.mem_append_right _ member)) (linearityBack (safe backward))

/-- Every finalization visit has a represented original input. The actual
inference and normalization witnesses preserve its backward references,
including the recursive ownership scan of a partial application. -/
theorem finish_backward
    (ghostSound : InferSound env base ctx limit ghost)
    (normalSound : VisitsFrom base (ExpandedNormalization env) normal)
    (ghostProgress : ∀ state root, state.steps ≤ limit → Progress limit state (ghost state root))
    (normalProgress : ∀ state root, Progress limit state (normal state root))
    (metadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (rootRep : Represents state.arena root T) (candidateRep : Represents state.arena candidate C)
    (success : (finish ghost normal boxed state candidate root head).result = .ok pairs)
    (ambient : Prefix (finish ghost normal boxed state candidate root head).state.arena final)
    (retained : ∀ pair ∈ pairs, PairRetained final pair)
    (backward : Backward state.arena) : Backward (finish ghost normal boxed state candidate root head).state.arena := by
  unfold finish at success ambient ⊢
  split at success
  · rename_i inner
    simp only [ite_eq_left inner]
    exact backward
  · rename_i top
    simp only [ite_eq_right top] at ambient ⊢
    obtain ⟨selected,normalized,entered⟩ := Outcome.next_success success
    rw [entered] at success ambient ⊢
    obtain ⟨kept,safe,_,_,_⟩ := normalSound onBase candidateRep normalized
    split at success
    · rename_i flag refs pi
      simp only [pi] at ambient ⊢
      have afterRoom := (normalProgress _ _).accepted room _ normalized
      have observed := (NativeCoreCodePartialApplication.run_visits success).2
      exact visits_backward ghostSound normalSound ghostProgress normalProgress metadata observed
        (onBase.trans kept) afterRoom (rootRep.frame kept) ambient retained (safe backward)
    · exact safe backward

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
    (ghostSound : InferSound env base ctx limit ghost)
    (metadata : NativeCoreGhostReferenceTypes.BoxedFamilies env boxed)
    (onBase : Prefix base state.arena) (room : state.steps ≤ limit)
    (rootRep : Represents state.arena root T) (fn : Represents state.arena function f) (arg : Represents state.arena argument a)
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
  have finished := finish_backward ghostSound (normalSound depth) ghostProgress (normalProgress depth) metadata
    (onBase.trans kept) within (rootRep.frame kept) represented checked ambient
      (fun pair member => retained pair (List.mem_append_right _ member))
  exact ⟨kept.trans finishCost.kept,finished ∘ initialBackward,type,represented.frame finishCost.kept,typed⟩

end Jihoo.NativeKernel.NativeCoreCodeApplicationFinalization
