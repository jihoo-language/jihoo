import Jihoo.NativeBindingMachineMutable
import Jihoo.NativeBindingMachineReferenceProvenance

/-! Reference provenance for indexed execution also covers the captures
that are suspended in Buffer, arithmetic, and array continuation frames. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

def BufferFrameReferences (limit : Nat) : BufferFrame → Prop
  | .owner index value | .loadOwner _ index value =>
      CodeReferences limit index ∧ CodeReferences limit value
  | .index _ value | .loadIndex _ _ value | .usubLeft value |
      .arrayElements value _ _ => CodeReferences limit value
  | .value _ _ | .loadContinuation _ _ _ | .loadOwnerArgument _ _ |
      .usubRight _ | .refinement => True

def PendingReferences (limit : Nat) (pending : List (BufferFrame × List Frame)) : Prop :=
  ∀ frame ∈ pending, BufferFrameReferences limit frame.1 ∧ StackReferences limit frame.2

def StateReferences (state : State) : Prop :=
  BindingMachine.StateReferences ⟨state.heap.metadata,state.control,state.stack⟩ ∧
    PendingReferences state.heap.metadata.heap.nextLease state.pending

private theorem BufferFrameReferences.mono (ready : BufferFrameReferences before frame) (grows : before ≤ after) :
    BufferFrameReferences after frame := by
  cases frame <;> simp only [BufferFrameReferences] at ready ⊢
  all_goals first | exact ⟨ready.1.mono grows,ready.2.mono grows⟩ | exact ready.mono grows | trivial

private theorem PendingReferences.mono (pending : PendingReferences before frames) (grows : before ≤ after) :
    PendingReferences after frames := by
  intro frame member
  obtain ⟨code,stack⟩ := pending frame member
  exact ⟨code.mono grows,stack.mono grows⟩

private theorem PendingReferences.cons (pending : PendingReferences limit rest)
    (frame : BufferFrameReferences limit first) (stack : StackReferences limit saved) :
    PendingReferences limit ((first,saved) :: rest) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨frame,stack⟩
  · exact pending pair member

private theorem PendingReferences.head (pending : PendingReferences limit ((frame,saved) :: rest)) :
    BufferFrameReferences limit frame ∧ StackReferences limit saved :=
  pending _ List.mem_cons_self

private theorem PendingReferences.tail (pending : PendingReferences limit ((frame,saved) :: rest)) :
    PendingReferences limit rest :=
  fun pair member => pending pair (List.mem_cons_of_mem _ member)

private theorem execute_lease_counter (heap : SizedBufferHeap.State) (action : Action) :
    heap.heap.nextLease ≤ (execute heap action).1.heap.heap.nextLease := by
  cases action
  all_goals simp only [execute]
  all_goals try exact Nat.le_refl _
  all_goals split <;> try split <;> first | exact Nat.le_refl _ | exact Nat.le_succ _

private theorem executeLegacy_references (valid : SizedBufferHeap.Valid state.heap.metadata)
    (pending : PendingReferences state.heap.metadata.heap.nextLease state.pending)
    (ready : ActionReferences state.heap.metadata.heap.nextLease action) :
    StateReferences (executeLegacy state action).1 := by
  have executed := BindingMachine.execute_references valid ready
  have later := pending.mono (execute_lease_counter state.heap.metadata action)
  cases action
  all_goals first | exact ⟨executed,later⟩ | skip
  case borrow key object stack =>
    simp only [executeLegacy,execute]
    split
    · rename_i token selected
      split
      · rename_i leased
        exact ⟨⟨ValueReferences.reference (valid.leased token object leased).1,ready⟩,pending⟩
      · exact ⟨⟨True.intro,ready⟩,pending⟩
    · exact ⟨⟨True.intro,ready⟩,pending⟩
  case read token index stack =>
    simp only [executeLegacy]
    split
    · exact ⟨⟨ValueReferences.integer,ready.2⟩,pending⟩
    · exact ⟨⟨True.intro,ready.2⟩,pending⟩

private theorem accessFailure_references (ready : StateReferences state) :
    StateReferences (ownedAccessFailure state object).1 := by
  simp only [ownedAccessFailure]
  split <;> try split
  all_goals exact ⟨⟨True.intro,StackReferences.empty⟩,ready.2⟩

private theorem resumeBuffer_references (valid : SizedBufferHeap.Valid state.heap.metadata)
    (ready : StateReferences state)
    (pending : state.pending = (frame,saved) :: rest)
    (returned : ValueReferences state.heap.metadata.heap.nextLease value) :
    StateReferences (resumeBuffer state frame saved rest value).1 := by
  have suspended := ready.2
  rw [pending] at suspended
  have top := suspended.head
  have outer := suspended.tail
  cases frame <;> cases value <;> simp only [resumeBuffer]
  all_goals first
    | exact ⟨⟨True.intro,StackReferences.empty⟩,ready.2⟩
    | skip
  case owner.owner =>
    exact ⟨⟨top.1.1,ready.1.2⟩,outer.cons top.1.2 top.2⟩
  case index.natural =>
    exact ⟨⟨top.1,ready.1.2⟩,outer.cons True.intro top.2⟩
  case value.integer =>
    split
    · rename_i heap written
      have metadata := (SizedBufferHeap.IndexedState.store_spec valid written).2.2.2.1
      exact ⟨⟨ValueReferences.owner,metadata.symm ▸ top.2⟩,metadata.symm ▸ outer⟩
    · exact accessFailure_references ready
  case loadOwner.owner =>
    exact ⟨⟨top.1.1,ready.1.2⟩,outer.cons top.1.2 top.2⟩
  case loadIndex.natural =>
    split
    · exact ⟨⟨top.1,ready.1.2⟩,outer.cons True.intro top.2⟩
    · exact accessFailure_references ready
  case loadContinuation.closure =>
    rename_i object origin number erased domain body context origins captured
    cases erased
    · exact executeLegacy_references (state := { state with pending := (.loadOwnerArgument object origin,saved) :: rest })
        valid (outer.cons True.intro top.2) (applyValue_references_retained returned .integer StackReferences.empty)
    · exact ⟨⟨True.intro,StackReferences.empty⟩,ready.2⟩
  case loadOwnerArgument.closure =>
    rename_i object origin erased domain body context origins captured
    cases erased
    · exact executeLegacy_references (state := { state with pending := rest }) valid outer
        (applyValue_references_retained returned .owner top.2)
    · exact ⟨⟨True.intro,StackReferences.empty⟩,ready.2⟩
  case usubLeft.natural =>
    exact ⟨⟨top.1,ready.1.2⟩,outer.cons True.intro top.2⟩
  case usubRight.natural =>
    split
    · exact ⟨⟨ValueReferences.natural,top.2⟩,outer⟩
    · exact ⟨⟨True.intro,top.2⟩,outer⟩
  case refinement.natural => exact ⟨⟨ValueReferences.natural,top.2⟩,outer⟩
  case arrayElements.integer =>
    split
    · exact ⟨⟨ValueReferences.array,top.2⟩,outer⟩
    · exact ⟨⟨top.1,ready.1.2⟩,outer.cons top.1 top.2⟩

/-- Every real transition preserves reference provenance, including all
stored or recursively captured references in suspended continuations. -/
theorem step_references (valid : SizedBufferHeap.Valid state.heap.metadata)
    (ready : StateReferences state) (stepped : step state = some (next,event)) :
    StateReferences next := by
  have controlReady := ready.1.1
  change ControlReferences state.heap.metadata.heap.nextLease state.control at controlReady
  cases control : state.control with
  | fault => simp [step,control] at stepped
  | evaluate code =>
      rw [control] at controlReady
      simp only [step,control] at stepped
      split at stepped
      · cases stepped
        exact ⟨⟨controlReady,StackReferences.empty⟩,ready.2.cons ⟨controlReady,controlReady⟩ ready.1.2⟩
      · cases stepped
        exact ⟨⟨controlReady,StackReferences.empty⟩,ready.2.cons ⟨controlReady,controlReady⟩ ready.1.2⟩
      · cases stepped
        exact ⟨⟨controlReady,StackReferences.empty⟩,ready.2.cons controlReady ready.1.2⟩
      · cases stepped
        exact ⟨⟨controlReady,StackReferences.empty⟩,ready.2.cons True.intro ready.1.2⟩
      · cases stepped
        exact ⟨⟨controlReady,StackReferences.empty⟩,ready.2.cons True.intro ready.1.2⟩
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        simp only [beginArray]
        split
        · split
          · exact ⟨⟨ValueReferences.array,ready.1.2⟩,ready.2⟩
          · exact ⟨⟨controlReady,StackReferences.empty⟩,ready.2.cons controlReady ready.1.2⟩
        · exact ⟨⟨True.intro,ready.1.2⟩,ready.2⟩
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        exact executeLegacy_references valid ready.2 (evaluate_action_references controlReady ready.1.2)
  | returned value =>
      rw [control] at controlReady
      simp only [step,control] at stepped
      cases chosen : returnAction value state.stack with
      | some action =>
          rw [chosen] at stepped
          have same := congrArg Prod.fst (Option.some.inj stepped)
          change _ = next at same
          rw [← same]
          exact executeLegacy_references valid ready.2 (return_action_references controlReady ready.1.2 chosen)
      | none =>
          rw [chosen] at stepped
          cases pending : state.pending with
          | nil => simp [pending] at stepped
          | cons pair rest =>
              obtain ⟨frame,saved⟩ := pair
              rw [pending] at stepped
              have same := congrArg Prod.fst (Option.some.inj stepped)
              change _ = next at same
              rw [← same]
              exact resumeBuffer_references valid ready pending controlReady

theorem run_references (valid : SizedBufferHeap.Valid state.heap.metadata)
    (ready : StateReferences state) (fuel : Nat) : StateReferences (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact ready
  | succ fuel ih =>
      simp only [run]
      cases stepped : step state with
      | none => exact ready
      | some result =>
          obtain ⟨next,event⟩ := result
          have nextValid := SizedBufferHeap.steps_valid valid (step_lifecycle valid stepped)
          exact ih nextValid (step_references valid ready stepped)

theorem initial_run_references (term : Term) (fuel : Nat) :
    StateReferences (run fuel (initial term)).state :=
  run_references SizedBufferHeap.empty_valid
    ⟨⟨ValuesReferences.nil,StackReferences.empty⟩,fun _ member => by cases member⟩ fuel

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
