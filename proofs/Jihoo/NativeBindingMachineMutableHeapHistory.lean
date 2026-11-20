import Jihoo.NativeBindingMachineMutable

/-! Indexed execution records the exact allocation and lease history of its
metadata. Cell reads and writes are separate observations: after Store a read
can differ from the uniform allocation payload recorded in the metadata. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

private def lifecycleEvent? : SizedBufferHeap.Event → Option SizedBufferHeap.Event
  | .read _ _ _ => none
  | event => some event

def Event.lifecycle? : Event → Option SizedBufferHeap.Event
  | .legacy (.heap event) => lifecycleEvent? event
  | _ => none

private theorem project_lifecycle (steps : SizedBufferHeap.Steps before events after) :
    SizedBufferHeap.Steps before (events.filterMap lifecycleEvent?) after := by
  induction steps with
  | nil => exact .nil
  | cons first _ ih =>
      cases first with
      | alloc => exact .cons .alloc ih
      | free live unborrowed => exact .cons (.free live unborrowed) ih
      | beginLease live => exact .cons (.beginLease live) ih
      | close present => exact .cons (.close present) ih
      | read => exact ih

private theorem legacy_lifecycle (event : Option BindingMachine.Event) :
    (event.map Event.legacy).toList.filterMap Event.lifecycle? =
      (eventHeap event).filterMap lifecycleEvent? := by
  cases event with
  | none => rfl
  | some event => cases event <;> rfl

private theorem execute_metadata_steps (valid : SizedBufferHeap.Valid heap) (action : Action) :
    SizedBufferHeap.Steps heap
      (((execute heap action).2.map Event.legacy).toList.filterMap Event.lifecycle?)
      (execute heap action).1.heap := by
  rw [legacy_lifecycle]
  exact project_lifecycle (execute_heap_steps valid action)

private theorem executeLegacy_metadata_steps (valid : SizedBufferHeap.Valid state.heap.metadata) (action : Action) :
    SizedBufferHeap.Steps state.heap.metadata ((executeLegacy state action).2.toList.filterMap Event.lifecycle?)
      (executeLegacy state action).1.heap.metadata := by
  cases action
  case borrow =>
    simp only [executeLegacy,execute]
    split <;> try split
    all_goals exact .nil
  case read =>
    simp only [executeLegacy]
    split <;> exact .nil
  all_goals exact execute_metadata_steps valid _

private theorem ownedAccessFailure_metadata_steps (state : State) (object : Nat) :
    SizedBufferHeap.Steps state.heap.metadata
      ((ownedAccessFailure state object).2.toList.filterMap Event.lifecycle?)
      (ownedAccessFailure state object).1.heap.metadata := by
  simp only [ownedAccessFailure]
  split <;> try split
  all_goals exact .nil

private theorem resumeBuffer_metadata_steps (valid : SizedBufferHeap.Valid state.heap.metadata)
    (frame : BufferFrame) (saved : List Frame) (rest : List (BufferFrame × List Frame)) (value : Value) :
    SizedBufferHeap.Steps state.heap.metadata ((resumeBuffer state frame saved rest value).2.toList.filterMap Event.lifecycle?)
      (resumeBuffer state frame saved rest value).1.heap.metadata := by
  cases frame <;> cases value <;> simp only [resumeBuffer]
  all_goals first | exact .nil | skip
  case value.integer =>
    split
    · rename_i heap written
      have metadata := (SizedBufferHeap.IndexedState.store_spec valid written).2.2.2.1
      rw [metadata]
      exact .nil
    · exact ownedAccessFailure_metadata_steps state _
  case loadIndex.natural =>
    split
    · exact .nil
    · exact ownedAccessFailure_metadata_steps state _
  case loadContinuation.closure => cases ‹Bool› <;> exact .nil
  case loadOwnerArgument.closure => cases ‹Bool› <;> exact .nil
  case arrayElements.integer => split <;> exact .nil

private theorem projected_step {pair : State × Option Event} {next : State} {event : Option Event}
    (same : pair = (next,event))
    (steps : SizedBufferHeap.Steps before (pair.2.toList.filterMap Event.lifecycle?) pair.1.heap.metadata) :
    SizedBufferHeap.Steps before (event.toList.filterMap Event.lifecycle?) next.heap.metadata := by
  simpa only [same] using steps

/-- The metadata-changing event of a real step is an actual heap transition.
Observations, cell-only writes, and faults preserve this metadata. -/
theorem step_lifecycle (valid : SizedBufferHeap.Valid state.heap.metadata)
    (stepped : step state = some (next,event)) :
    SizedBufferHeap.Steps state.heap.metadata (event.toList.filterMap Event.lifecycle?) next.heap.metadata := by
  cases control : state.control with
  | fault => simp [step,control] at stepped
  | evaluate code =>
      simp only [step,control] at stepped
      split at stepped
      all_goals first
        | solve | cases stepped; exact .nil
        | skip
      · have pair := Option.some.inj stepped
        have sameState := congrArg Prod.fst pair
        have sameEvent := congrArg Prod.snd pair
        change _ = next at sameState
        change _ = event at sameEvent
        rw [← sameState,← sameEvent]
        simp only [beginArray]
        split <;> try split
        all_goals exact .nil
      · exact projected_step (Option.some.inj stepped) (executeLegacy_metadata_steps valid _)
  | returned value =>
      simp only [step,control] at stepped
      cases chosen : returnAction value state.stack with
      | some action =>
          rw [chosen] at stepped
          exact projected_step (Option.some.inj stepped) (executeLegacy_metadata_steps valid action)
      | none =>
          rw [chosen] at stepped
          cases pending : state.pending with
          | nil => simp [pending] at stepped
          | cons head rest =>
              obtain ⟨frame,saved⟩ := head
              rw [pending] at stepped
              exact projected_step (Option.some.inj stepped) (resumeBuffer_metadata_steps valid frame saved rest value)

private theorem lifecycle_append (first : SizedBufferHeap.Steps before events middle)
    (second : SizedBufferHeap.Steps middle later after) : SizedBufferHeap.Steps before (events ++ later) after := by
  induction first with
  | nil => exact second
  | cons first _ ih => exact .cons first (ih second)

/-- The real event prefix determines the heap metadata, including prefixes
that exhaust fuel or fault inside a suspended operand. -/
theorem run_lifecycle (valid : SizedBufferHeap.Valid state.heap.metadata) (fuel : Nat) :
    SizedBufferHeap.Steps state.heap.metadata ((run fuel state).events.filterMap Event.lifecycle?)
      (run fuel state).state.heap.metadata := by
  induction fuel generalizing state with
  | zero => exact .nil
  | succ fuel ih =>
      simp only [run]
      cases observed : step state with
      | none => exact .nil
      | some result =>
          obtain ⟨next,event⟩ := result
          have first := step_lifecycle valid observed
          have rest := ih (SizedBufferHeap.steps_valid valid first)
          simpa only [List.filterMap_append] using lifecycle_append first rest

/-- Existing captured Buffer sizes remain true across arbitrary indexed
execution starting at a reachable prefix, including Store and Load callbacks. -/
theorem reachable_run_owner_sizes (term : Term) (prefixFuel suffixFuel : Nat)
    (sizes : OwnerSizes env (run prefixFuel (initial term)).state.heap.metadata code meanings) :
    OwnerSizes env (run suffixFuel (run prefixFuel (initial term)).state).state.heap.metadata code meanings :=
  sizes.steps (run_lifecycle (initial_run_invariant term prefixFuel).1 suffixFuel)

/-- No subsequent Store, Load or allocation revives an already released
identity. Its recorded length also remains the original allocation length. -/
theorem reachable_run_released_owner (term : Term) (prefixFuel suffixFuel : Nat)
    (old : object < (run prefixFuel (initial term)).state.heap.metadata.heap.nextObject)
    (released : (run prefixFuel (initial term)).state.heap.metadata.heap.live object = false) :
    let before := (run prefixFuel (initial term)).state.heap.metadata
    let after := (run suffixFuel (run prefixFuel (initial term)).state).state.heap.metadata
    object < after.heap.nextObject ∧ after.heap.live object = false ∧ after.length object = before.length object := by
  have steps := run_lifecycle (initial_run_invariant term prefixFuel).1 suffixFuel
  obtain ⟨beforeLimit,dead⟩ := HeapLeases.dead_steps old released (SizedBufferHeap.steps_project steps)
  exact ⟨beforeLimit,dead,(SizedBufferHeap.lengths_preserved old steps).2⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
