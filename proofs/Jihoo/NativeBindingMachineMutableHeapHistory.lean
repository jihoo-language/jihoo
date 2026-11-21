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
  have repeatSteps (cursor : Iteration) (accumulator : Value) (origin : Term) :
      SizedBufferHeap.Steps state.heap.metadata
        ((continueIteration state cursor accumulator origin saved rest).2.toList.filterMap Event.lifecycle?)
        (continueIteration state cursor accumulator origin saved rest).1.heap.metadata := by
    unfold continueIteration
    split <;> exact .nil
  cases frame <;> cases value <;> simp only [resumeBuffer]
  all_goals first | exact .nil | exact repeatSteps _ _ _ | skip
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
  case iterationIndex.closure | iterationBound.closure | iterationAccumulator.closure =>
    cases ‹Bool› <;> exact .nil

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

private theorem step_owner_live_iff (old : object < before.heap.nextObject)
    (step : SizedBufferHeap.Step before event after) :
    after.heap.live object = true ↔ before.heap.live object = true ∧ event ≠ .free object := by
  cases step with
  | alloc => simp [SizedBufferHeap.allocate,HeapLeases.put,Nat.ne_of_lt old]
  | free =>
      simp only [SizedBufferHeap.release,HeapLeases.put]
      split
      · rename_i same
        simp [same]
      · rename_i other
        simp [Ne.symm other]
  | beginLease => simp [SizedBufferHeap.lend]
  | close => simp [SizedBufferHeap.close]
  | read => simp

theorem lifecycle_owner_live_iff (old : object < before.heap.nextObject)
    (steps : SizedBufferHeap.Steps before events after) :
    after.heap.live object = true ↔ before.heap.live object = true ∧ .free object ∉ events := by
  revert old
  induction steps with
  | nil => simp
  | cons step _ ih =>
      intro old
      rw [ih (SizedBufferHeap.length_preserved old step).1,step_owner_live_iff old step]
      simp only [List.mem_cons,not_or]
      constructor
      · rintro ⟨⟨initial,notStep⟩,notTail⟩
        exact ⟨initial,Ne.symm notStep,notTail⟩
      · rintro ⟨initial,notStep,notTail⟩
        exact ⟨⟨initial,Ne.symm notStep⟩,notTail⟩

/-- An earlier allocation is live exactly when it was live at the first
snapshot and has no release event in the actual intervening execution. -/
theorem reachable_run_owner_live_iff (term : Term) (prefixFuel suffixFuel : Nat)
    (old : object < (run prefixFuel (initial term)).state.heap.metadata.heap.nextObject) :
    let before := (run prefixFuel (initial term)).state
    let suffix := run suffixFuel before
    suffix.state.heap.metadata.heap.live object = true ↔
      before.heap.metadata.heap.live object = true ∧ .free object ∉ suffix.events.filterMap Event.lifecycle? :=
  lifecycle_owner_live_iff old (run_lifecycle (initial_run_invariant term prefixFuel).1 suffixFuel)

private theorem literal_store_released_steps (state : State) (evaluating : state.control = .evaluate actual)
    (shape : actual.term = .store (.var owner) (.natural offset) (.integer value) evidence)
    (stored : actual.values[owner]? = some (some (.owner object)))
    (offsetWidth : offset < 2^64) (valueWidth : ValueReduction.signed64 value)
    (dead : state.heap.metadata.heap.live object = false) :
    run 7 state = ⟨⟨state.heap,.fault .deadOwner,[],
      (.value object offset,state.stack) :: state.pending⟩,[],7⟩ := by
  have noWrite : state.heap.store object offset (encodeInteger value) = none := by
    unfold SizedBufferHeap.IndexedState.store
    exact ite_eq_right (by intro guard; rw [dead] at guard; cases guard.1)
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,stored,executeLegacy,execute,
    Option.map_none,returnAction,resumeBuffer,offsetWidth,valueWidth,ite_true,noWrite,ownedAccessFailure,dead]
  rfl

/-- For a real Store reached from a previously live owner world, the actual
release history selects the outcome. Its sizes and reader inventory are
recovered from execution. A released owner reaches the dead-owner fault,
while a retained owner performs the exact write at the original Buffer type. -/
theorem reachable_typed_literal_store_history (term : Term) (prefixFuel suffixFuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run suffixFuel (run prefixFuel (initial term)).state).state.control = .evaluate actual)
    (view : CanonicalView actual source indices)
    (typed : LoanClosingTyped env loans false source meanings type)
    (sizes : OwnerSizes env (run prefixFuel (initial term)).state.heap.metadata source meanings)
    (shape : actual.term = .store (.var owner) (.natural offset) (.integer value)
      (.decide (.natural offset) (.natural count)))
    (stored : actual.values[owner]? = some (some (.owner object)))
    (previousLive : (run prefixFuel (initial term)).state.heap.metadata.heap.live object = true)
    (coverage : LoanCoverage source loans (run suffixFuel (run prefixFuel (initial term)).state).state.activeStack)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans source.context source.term = some resource)
    (budget : LoanTyping.ResourceQuantity.LoanBudget source.context.length loans resource) :
    let suffix := run suffixFuel (run prefixFuel (initial term)).state
    let state := suffix.state
    if .free object ∈ suffix.events.filterMap Event.lifecycle? then
      run 7 state = ⟨⟨state.heap,.fault .deadOwner,[],(.value object offset,state.stack) :: state.pending⟩,[],7⟩
    else
      ∃ heap,
        run 7 state = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
          [.store object offset (encodeInteger value)],7⟩ ∧
        heap.metadata = state.heap.metadata ∧ heap.metadata.length object = count ∧
        LoanTyping.Conversion.Conv env (.buffer (.natural count)) type ∧
        decodeInteger (heap.cell object offset) = value ∧
        ∀ token index, heap.read token index = state.heap.read token index := by
  let suffix := run suffixFuel (run prefixFuel (initial term)).state
  let state := suffix.state
  change (if .free object ∈ suffix.events.filterMap Event.lifecycle? then _ else _)
  have initial := initial_run_invariant term prefixFuel
  have old := initial.1.allocated object previousLive
  have liveness := reachable_run_owner_live_iff term prefixFuel suffixFuel old
  by_cases released : .free object ∈ suffix.events.filterMap Event.lifecycle?
  · rw [ite_eq_left released]
    have dead : state.heap.metadata.heap.live object = false := by
      cases current : state.heap.metadata.heap.live object with
      | false => rfl
      | true => exact False.elim ((liveness.mp current).2 released)
    have sourceShape : source.term = .store (.var (indices owner)) (.natural offset) (.integer value)
        (.decide (.natural offset) (.natural count)) := by
      rw [← view.termEq,shape]
      simp only [Term.rename,renameArgs,Op.binders,liftRenaming]
    obtain ⟨_,_,sourceTyped,_⟩ := typed
    rw [sourceShape] at sourceTyped
    obtain ⟨_,_,offsetTyped,valueTyped,_,_⟩ := sourceTyped.store_inputs
    exact literal_store_released_steps state evaluating shape stored offsetTyped.natural_bound valueTyped.integer_bound dead
  · rw [ite_eq_right released]
    have live : state.heap.metadata.heap.live object = true := liveness.mpr ⟨previousLive,released⟩
    exact typed_literal_store state history (run_invariant suffixFuel initial) evaluating view typed
      (reachable_run_owner_sizes term prefixFuel suffixFuel sizes) shape stored live coverage checked budget

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
