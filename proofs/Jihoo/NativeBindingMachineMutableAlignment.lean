import Jihoo.NativeBindingMachineAlignment
import Jihoo.NativeBindingMachineMutable

/-! Extended instructions suspend ordinary frames while evaluating their operands.
The indexed machine retains the usual erasure and captured-slot alignment in
both the active stack and every pending operand or callback. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

def BufferFrameAligned : BufferFrame → Prop
  | .owner index value | .loadOwner _ index value => CodeAligned index ∧ CodeAligned value
  | .index _ value | .loadIndex _ _ value | .usubLeft value => CodeAligned value
  | _ => True

def PendingAligned (pending : List (BufferFrame × List Frame)) : Prop :=
  ∀ entry ∈ pending, BufferFrameAligned entry.1 ∧ StackAligned entry.2

structure StateAligned (state : State) : Prop where
  control : ControlAligned state.control
  stack : StackAligned state.stack
  pending : PendingAligned state.pending

private theorem PendingAligned.cons (aligned : PendingAligned rest)
    (frame : BufferFrameAligned first) (stack : StackAligned saved) :
    PendingAligned ((first,saved) :: rest) := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨frame,stack⟩
  · exact aligned entry member

private theorem PendingAligned.tail (aligned : PendingAligned (head :: rest)) :
    PendingAligned rest := fun entry member => aligned entry (List.mem_cons_of_mem _ member)

private theorem PendingAligned.savedStacks (aligned : PendingAligned pending) :
    StackAligned (pending.flatMap Prod.snd) := by
  intro frame member
  obtain ⟨entry,found,inSaved⟩ := List.mem_flatMap.mp member
  exact (aligned entry found).2 frame inSaved

theorem StateAligned.activeStack (aligned : StateAligned state) : StackAligned state.activeStack := by
  intro frame member
  rcases List.mem_append.mp member with active | saved
  · exact aligned.stack frame active
  · exact aligned.pending.savedStacks frame saved

private theorem executeLegacy_aligned {nextAction : Action} (pending : PendingAligned state.pending)
    (ready : ActionAligned nextAction) : StateAligned (executeLegacy state nextAction).1 := by
  have legacy := execute_aligned (heap := state.heap.metadata) ready
  cases nextAction with
  | control | allocate | free | lend | close => exact ⟨legacy.1,legacy.2,pending⟩
  | read =>
      simp only [executeLegacy]
      split
      · exact ⟨ValueAligned.integer,ready,pending⟩
      · exact ⟨True.intro,ready,pending⟩
  | borrow key object stack =>
      have allFrames : StackAligned (stack ++ state.pending.flatMap Prod.snd) := by
        intro frame member
        rcases List.mem_append.mp member with active | saved
        · exact ready frame active
        · exact pending.savedStacks frame saved
      have borrowed := execute_aligned (heap := state.heap.metadata)
        (next := .borrow key object (stack ++ state.pending.flatMap Prod.snd)) allFrames
      exact ⟨borrowed.1,ready,pending⟩

private theorem ownedAccessFailure_aligned (pending : PendingAligned state.pending) :
    StateAligned (ownedAccessFailure state object).1 := by
  simp only [ownedAccessFailure]
  split <;> try split
  all_goals exact ⟨True.intro,StackAligned.empty,pending⟩

private theorem resumeBuffer_aligned (aligned : StateAligned state)
    (pending : state.pending = (frame,saved) :: rest) (ready : ValueAligned value) :
    StateAligned (resumeBuffer state frame saved rest value).1 := by
  have suspended := aligned.pending
  rw [pending] at suspended
  have top := suspended (frame,saved) List.mem_cons_self
  have outer := suspended.tail
  cases frame <;> cases value <;> simp only [resumeBuffer]
  all_goals first
    | exact ⟨True.intro,StackAligned.empty,aligned.pending⟩
    | skip
  case owner.owner => exact ⟨top.1.1,aligned.stack,outer.cons top.1.2 top.2⟩
  case index.natural => exact ⟨top.1,aligned.stack,outer.cons True.intro top.2⟩
  case value.integer =>
    split
    · exact ⟨ValueAligned.owner,top.2,outer⟩
    · exact ownedAccessFailure_aligned aligned.pending
  case loadOwner.owner => exact ⟨top.1.1,aligned.stack,outer.cons top.1.2 top.2⟩
  case loadIndex.natural =>
    split
    · exact ⟨top.1,aligned.stack,outer.cons True.intro top.2⟩
    · exact ownedAccessFailure_aligned aligned.pending
  case loadContinuation.closure =>
    rename_i object origin number erased domain body context origins captured
    cases erased
    · exact executeLegacy_aligned
        (state := { state with pending := (.loadOwnerArgument object origin,saved) :: rest })
        (outer.cons True.intro top.2)
        (applyValue_retained_aligned ready rfl ValueAligned.integer StackAligned.empty)
    · exact ⟨True.intro,StackAligned.empty,aligned.pending⟩
  case loadOwnerArgument.closure =>
    cases ‹Bool›
    · exact executeLegacy_aligned (state := { state with pending := rest }) outer
        (applyValue_retained_aligned ready rfl ValueAligned.owner top.2)
    · exact ⟨True.intro,StackAligned.empty,aligned.pending⟩
  case usubLeft.natural => exact ⟨top.1,aligned.stack,outer.cons True.intro top.2⟩
  case usubRight.natural =>
    split
    · exact ⟨ValueAligned.natural,top.2,outer⟩
    · exact ⟨True.intro,top.2,outer⟩
  case refinement.natural => exact ⟨ready,top.2,outer⟩

theorem step_aligned (aligned : StateAligned state) (stepped : step state = some (next,event)) :
    StateAligned next := by
  have ready := aligned.control
  cases control : state.control with
  | fault => simp [step,control] at stepped
  | evaluate code =>
      rw [control] at ready
      simp only [step,control] at stepped
      split at stepped
      · cases stepped
        exact ⟨ready,StackAligned.empty,aligned.pending.cons ⟨ready,ready⟩ aligned.stack⟩
      · cases stepped
        exact ⟨ready,StackAligned.empty,aligned.pending.cons ⟨ready,ready⟩ aligned.stack⟩
      · cases stepped
        exact ⟨ready,StackAligned.empty,aligned.pending.cons ready aligned.stack⟩
      · cases stepped
        exact ⟨ready,StackAligned.empty,aligned.pending.cons True.intro aligned.stack⟩
      · cases stepped
        exact ⟨ready,StackAligned.empty,aligned.pending.cons True.intro aligned.stack⟩
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        exact executeLegacy_aligned aligned.pending (evaluate_action_aligned ready aligned.stack)
  | returned value =>
      rw [control] at ready
      simp only [step,control] at stepped
      cases chosen : returnAction value state.stack with
      | some action =>
          rw [chosen] at stepped
          have same := congrArg Prod.fst (Option.some.inj stepped)
          change _ = next at same
          rw [← same]
          exact executeLegacy_aligned aligned.pending (return_action_aligned ready aligned.stack chosen)
      | none =>
          rw [chosen] at stepped
          cases pending : state.pending with
          | nil => simp [pending] at stepped
          | cons head rest =>
              obtain ⟨frame,saved⟩ := head
              rw [pending] at stepped
              have same := congrArg Prod.fst (Option.some.inj stepped)
              change _ = next at same
              rw [← same]
              exact resumeBuffer_aligned aligned pending ready

theorem run_aligned (fuel : Nat) (aligned : StateAligned state) : StateAligned (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact aligned
  | succ fuel ih =>
      cases stepped : step state with
      | none => simpa only [run,stepped] using aligned
      | some result =>
          obtain ⟨next,event⟩ := result
          simpa only [run,stepped] using ih (step_aligned aligned stepped)

theorem initial_run_aligned (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State) :
    StateAligned (run fuel (initial term heap)).state :=
  run_aligned fuel ⟨SlotsAligned.nil,StackAligned.empty,fun _ member => by cases member⟩

theorem initial_run_code_aligned (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (evaluating : (run fuel (initial term heap)).state.control = .evaluate code) : CodeAligned code := by
  have control := (initial_run_aligned term fuel heap).control
  rw [evaluating] at control
  exact control

theorem initial_run_code_variable_step (term : Term) (fuel : Nat) (heap : SizedBufferHeap.State)
    (evaluating : (run fuel (initial term heap)).state.control = .evaluate code)
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .var index) :
    let state := (run fuel (initial term heap)).state
    ∃ value, ValueAligned value ∧ step state = some ({ state with control := .returned value },none) := by
  rw [shape] at typed
  obtain ⟨binding,selected,relevant⟩ := loan_code_variable_permission typed
  have aligned := initial_run_code_aligned term fuel heap evaluating
  obtain ⟨option,stored,flag⟩ := SlotsAligned.ready aligned index binding selected
  cases option with
  | none => simp [relevant] at flag
  | some value =>
      refine ⟨value,SlotsAligned.valueAt aligned stored,?_⟩
      simp only [step,evaluating,shape,evaluateAction,stored,executeLegacy,execute,Option.map_none]

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
