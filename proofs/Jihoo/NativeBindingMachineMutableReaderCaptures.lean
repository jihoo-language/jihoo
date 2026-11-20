import Jihoo.NativeBindingMachineMutableReferenceProvenance
import Jihoo.NativeBindingMachineReaderCaptures

/-! Reader entry bounds the references in its saved continuation and in
all enclosing frames. Buffer operations may suspend and resume portions
of the stack without losing those bounds. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

private def ReaderOuterBounds (stack : List Frame) (pending : List (BufferFrame × List Frame)) : Prop :=
  ∀ entry ∈ readerFrames stack, PendingReferences entry.1 pending

private theorem ReaderOuterBounds.transport (ready : ReaderOuterBounds before pending)
    (same : readerFrames before = readerFrames after) : ReaderOuterBounds after pending :=
  fun entry member => ready entry (same.symm ▸ member)

private def ChunkReaderBounds (stack : List Frame) (pending : List (BufferFrame × List Frame)) : Prop :=
  ReaderCaptureBounds stack ∧ ReaderOuterBounds stack pending

private theorem emptyChunk : ChunkReaderBounds [] pending :=
  ⟨ReaderCaptureBounds.empty,fun _ member => by cases member⟩

private def SuspendedReaderBounds : List (BufferFrame × List Frame) → Prop
  | [] => True
  | (_,saved) :: rest => ChunkReaderBounds saved rest ∧ SuspendedReaderBounds rest

def ReaderCaptureWorld (state : State) : Prop :=
  ChunkReaderBounds state.stack state.pending ∧ SuspendedReaderBounds state.pending

private theorem executeLegacy_pending (state : State) (action : Action) :
    (executeLegacy state action).1.pending = state.pending := by
  cases action <;> simp only [executeLegacy,execute,fail]
  all_goals try split
  all_goals try split
  all_goals rfl

private theorem executeLegacy_chunk_bounds (state : State) (action : Action)
    (references : ActionReferences state.heap.metadata.heap.nextLease action)
    (pending : PendingReferences state.heap.metadata.heap.nextLease state.pending)
    (changed : FrameChange state.stack action) (captures : ActionReaderCaptureBounds action)
    (outer : ReaderOuterBounds state.stack state.pending) :
    ChunkReaderBounds (executeLegacy state action).1.stack state.pending := by
  cases action with
  | control => exact ⟨captures,outer.transport changed⟩
  | allocate =>
      simp only [executeLegacy,execute]
      split <;> exact ⟨captures,outer.transport changed⟩
  | free =>
      simp only [executeLegacy,execute]
      split
      · split <;> exact ⟨captures,outer.transport changed⟩
      · exact ⟨captures,outer.transport changed⟩
  | lend object name origin reader continuation stack =>
      have previous : ReaderOuterBounds stack state.pending := outer.transport changed
      simp only [executeLegacy,execute]
      split
      · refine ⟨captures.begin_reader references.2.1 references.2.2 object name origin reader.origin,?_⟩
        intro entry member
        change entry ∈ (state.heap.metadata.heap.nextLease,object,name) :: readerFrames stack at member
        rcases List.mem_cons.mp member with rfl | member
        · exact pending
        · exact previous entry member
      · exact ⟨captures,previous⟩
  | close token object result origin resultOrigin continuation stack =>
      obtain ⟨name,same⟩ := changed
      have previous : ReaderOuterBounds stack state.pending := fun entry member =>
        outer entry (same.symm ▸ List.mem_cons_of_mem (token,object,name) member)
      simp only [executeLegacy,execute]
      split
      · exact ⟨captures.cons_nonreader rfl,previous⟩
      · exact ⟨captures,previous⟩
  | borrow => exact ⟨captures,outer.transport changed⟩
  | read =>
      simp only [executeLegacy,fail]
      split <;> exact ⟨captures,outer.transport changed⟩

private theorem executeLegacy_reader_bounds (state : State) (action : Action)
    (references : ActionReferences state.heap.metadata.heap.nextLease action)
    (pending : PendingReferences state.heap.metadata.heap.nextLease state.pending)
    (changed : FrameChange state.stack action) (captures : ActionReaderCaptureBounds action)
    (ready : ReaderCaptureWorld state) : ReaderCaptureWorld (executeLegacy state action).1 := by
  unfold ReaderCaptureWorld
  rw [executeLegacy_pending]
  exact ⟨executeLegacy_chunk_bounds state action references pending changed captures ready.1.2,ready.2⟩

private theorem resumeBuffer_reader_bounds (ready : ReaderCaptureWorld state)
    (empty : state.stack = []) (pending : state.pending = (frame,saved) :: rest) (value : Value) :
    ReaderCaptureWorld (resumeBuffer state frame saved rest value).1 := by
  have savedBounds := ready.2
  rw [pending] at savedBounds
  have emptyBounds {outer : List (BufferFrame × List Frame)} : ChunkReaderBounds state.stack outer := by
    rw [empty]
    exact emptyChunk
  have accessFailure (object : Nat) : ReaderCaptureWorld (ownedAccessFailure state object).1 := by
    simp only [ownedAccessFailure,fail]
    split
    · exact ⟨emptyChunk,ready.2⟩
    · split <;> exact ⟨emptyChunk,ready.2⟩
  cases frame <;> cases value <;> simp only [resumeBuffer,fail]
  all_goals first
    | exact ready
    | exact ⟨emptyChunk,ready.2⟩
    | exact ⟨emptyChunk,savedBounds⟩
    | exact ⟨emptyBounds,savedBounds⟩
    | exact savedBounds
    | skip
  case value.integer =>
      split
      · exact savedBounds
      · exact accessFailure _
  case loadIndex.natural =>
      split
      · exact ⟨emptyBounds,savedBounds⟩
      · exact accessFailure _
  case arrayElements.integer =>
      split
      · exact savedBounds
      · exact ⟨emptyBounds,savedBounds⟩
  all_goals
    cases ‹Bool› <;> simp only [applyValue,executeLegacy,execute] <;>
      first | exact ⟨emptyChunk,ready.2⟩ | exact ⟨emptyChunk,savedBounds⟩ | exact savedBounds

theorem step_reader_capture_world (references : StateReferences state) (ready : ReaderCaptureWorld state)
    (stepped : step state = some (next,event)) : ReaderCaptureWorld next := by
  have controlBound : ControlReferences state.heap.metadata.heap.nextLease state.control := references.1.1
  cases control : state.control with
  | fault => simp [step,control] at stepped
  | evaluate code =>
      have controlReady : CodeReferences state.heap.metadata.heap.nextLease code := by
        simpa only [control,ControlReferences] using controlBound
      simp only [step,control] at stepped
      split at stepped
      all_goals first
        | solve | cases stepped; exact ⟨emptyChunk,ready⟩
        | skip
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        simp only [beginArray]
        split
        · split
          · exact ready
          · exact ⟨emptyChunk,ready⟩
        · exact ready
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        exact executeLegacy_reader_bounds state _ (evaluate_action_references controlReady references.1.2)
          references.2 (evaluate_frame_change _ _) (evaluate_action_reader_captures code ready.1.1) ready
  | returned value =>
      have controlReady : ValueReferences state.heap.metadata.heap.nextLease value := by
        simpa only [control,ControlReferences] using controlBound
      simp only [step,control] at stepped
      cases chosen : returnAction value state.stack with
      | some action =>
          rw [chosen] at stepped
          have same := congrArg Prod.fst (Option.some.inj stepped)
          change _ = next at same
          rw [← same]
          exact executeLegacy_reader_bounds state _ (return_action_references controlReady references.1.2 chosen)
            references.2 (return_frame_change _ _ _ chosen)
            (return_action_reader_captures value ready.1.1 chosen) ready
      | none =>
          have empty : state.stack = [] := by
            cases stack : state.stack with
            | nil => rfl
            | cons frame rest => simp [stack,returnAction] at chosen
          rw [chosen] at stepped
          cases pending : state.pending with
          | nil => simp [pending] at stepped
          | cons head rest =>
              obtain ⟨frame,saved⟩ := head
              rw [pending] at stepped
              have same := congrArg Prod.fst (Option.some.inj stepped)
              change _ = next at same
              rw [← same]
              exact resumeBuffer_reader_bounds ready empty pending value

theorem initial_run_reader_capture_world (term : Term) (fuel : Nat) :
    ReaderCaptureWorld (run fuel (initial term)).state := by
  let preserve {state : State} (invariant : Invariant state)
      (references : StateReferences state) (ready : ReaderCaptureWorld state) (fuel : Nat) :
      ReaderCaptureWorld (run fuel state).state := by
    induction fuel generalizing state with
    | zero => exact ready
    | succ fuel ih =>
        simp only [run]
        cases stepped : step state with
        | none => exact ready
        | some result =>
            obtain ⟨next,event⟩ := result
            exact ih (step_invariant invariant stepped) (step_references invariant.1 references stepped)
              (step_reader_capture_world references ready stepped)
  exact preserve (state := initial term) ⟨SizedBufferHeap.empty_valid,ReaderInventory.empty⟩
    ⟨⟨ValuesReferences.nil,StackReferences.empty⟩,fun _ member => by cases member⟩ ⟨emptyChunk,True.intro⟩ fuel

/-- Immediately before a real reader close, its original saved continuation
and every frame beneath it still contain only references older than its token. -/
theorem initial_run_finish_capture_bounds (term : Term) (fuel : Nat)
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin continuation :: stack) :
    CodeReferences token continuation ∧ StackReferences token stack ∧
      PendingReferences token (run fuel (initial term)).state.pending := by
  have captures := (initial_run_reader_capture_world term fuel).1
  rw [stackShape] at captures
  obtain ⟨continuationReady,stackReady⟩ := captures.1.finish
  have member : (token,object,name) ∈ readerFrames
      (.lendFinish token object name origin resultOrigin continuation :: stack) := by
    change (token,object,name) ∈ (token,object,name) :: readerFrames stack
    exact List.mem_cons_self
  exact ⟨continuationReady,stackReady,captures.2 _ member⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
