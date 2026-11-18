import Jihoo.NativeBindingMachineMutable
import Jihoo.NativeBindingMachineNumeric

/-! Numeric widths throughout indexed-buffer execution. The ordinary machine
handles widths of runtime values, closures, frames, and allocation metadata.
Stores and allocations establish widths of the cells they write, and indexed
reads transport those widths into returned values and Load continuations. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

def BufferFrameNumbers : BufferFrame → Prop
  | .owner index fill | .loadOwner _ index fill => CodeNumbers index ∧ CodeNumbers fill
  | .index _ fill | .loadIndex _ _ fill | .usubLeft fill => CodeNumbers fill
  | .value _ index | .usubRight index => index < 2^64
  | .loadContinuation _ _ value => ValueReduction.signed64 value
  | .loadOwnerArgument _ _ => True

def PendingNumbers (pending : List (BufferFrame × List Frame)) : Prop :=
  ∀ frame ∈ pending, BufferFrameNumbers frame.1 ∧ StackNumbers frame.2

private theorem PendingNumbers.cons (pending : PendingNumbers rest)
    (frame : BufferFrameNumbers first) (stack : StackNumbers saved) :
    PendingNumbers ((first,saved) :: rest) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨frame,stack⟩
  · exact pending pair member

private theorem PendingNumbers.head (pending : PendingNumbers ((frame,saved) :: rest)) :
    BufferFrameNumbers frame ∧ StackNumbers saved :=
  pending _ List.mem_cons_self

private theorem PendingNumbers.tail (pending : PendingNumbers ((frame,saved) :: rest)) :
    PendingNumbers rest :=
  fun pair member => pending pair (List.mem_cons_of_mem _ member)

def CellNumbers (heap : SizedBufferHeap.IndexedState) : Prop :=
  ∀ object index, heap.cell object index < 2^64

structure StateNumbers (state : State) : Prop where
  legacy : BindingMachine.StateNumbers ⟨state.heap.metadata,state.control,state.stack⟩
  pending : PendingNumbers state.pending
  cells : CellNumbers state.heap

variable {action : Action}

private theorem allocated_payload_bound (ready : ActionNumbers action)
    (allocated : (execute heap action).2 = some (.heap (.alloc object count payload))) :
    payload < 2^64 := by
  cases action with
  | control control stack activation =>
      cases activation <;> simp [execute] at allocated
  | allocate len fill stack =>
      simp only [execute] at allocated
      split at allocated
      · cases allocated
        exact encode_integer_bound ready.2.1
      · contradiction
  | lend | close =>
      simp only [execute] at allocated
      split at allocated <;> simp at allocated
  | free | borrow | read =>
      simp only [execute] at allocated
      split at allocated
      · split at allocated <;> simp at allocated
      · simp at allocated

private theorem legacy_cells (bounded : StateNumbers state) (ready : ActionNumbers action) :
    ∀ object index,
      (match (execute state.heap.metadata action).2 with
       | some (.heap (.alloc allocated _ fill)) => HeapLeases.put state.heap.cell allocated (fun _ => fill)
       | _ => state.heap.cell) object index < 2^64 := by
  intro object index
  cases written : (execute state.heap.metadata action).2 with
  | none => exact bounded.cells object index
  | some event =>
      cases event with
      | heap event =>
          cases event with
          | alloc allocated count fill =>
              have width := allocated_payload_bound ready written
              change HeapLeases.put state.heap.cell allocated (fun _ => fill) object index < 2^64
              simp only [HeapLeases.put]
              split
              · exact width
              · exact bounded.cells object index
          | _ => exact bounded.cells object index
      | activate => exact bounded.cells object index

private theorem read_payload_bound (bounded : CellNumbers heap)
    (read : heap.read token index = some payload) : payload < 2^64 := by
  unfold SizedBufferHeap.IndexedState.read at read
  obtain ⟨object,_,read⟩ := Option.bind_eq_some_iff.mp read
  split at read
  · cases read
    exact bounded object index
  · contradiction

private theorem load_payload_bound (bounded : CellNumbers heap)
    (read : heap.load object index = some payload) : payload < 2^64 := by
  unfold SizedBufferHeap.IndexedState.load at read
  split at read
  · cases read
    exact bounded object index
  · contradiction

private theorem store_cell_numbers (bounded : CellNumbers heap) (width : payload < 2^64)
    (written : heap.store object index payload = some after) :
    after.metadata = heap.metadata ∧ CellNumbers after := by
  unfold SizedBufferHeap.IndexedState.store at written
  split at written
  · cases written
    refine ⟨rfl,?_⟩
    intro selected offset
    simp only [HeapLeases.put]
    split
    · simp only [HeapLeases.put]
      split
      · exact width
      · exact bounded object offset
    · exact bounded selected offset
  · contradiction

private theorem executeLegacy_numbers (bounded : StateNumbers state) (ready : ActionNumbers action) :
    StateNumbers (executeLegacy state action).1 := by
  have legacy := execute_numbers bounded.legacy.1 ready
  have cells := legacy_cells bounded ready
  cases action with
  | control | allocate | free | lend | close =>
      exact ⟨legacy,bounded.pending,cells⟩
  | borrow =>
      simp only [executeLegacy,execute]
      split <;> try split
      all_goals first
        | exact ⟨⟨bounded.legacy.1,ValueNumbers.reference,ready⟩,bounded.pending,bounded.cells⟩
        | exact ⟨⟨bounded.legacy.1,True.intro,ready⟩,bounded.pending,bounded.cells⟩
  | read =>
      simp only [executeLegacy]
      split
      · rename_i payload read
        exact ⟨⟨bounded.legacy.1,ValueNumbers.integer (decode_integer_bound (read_payload_bound bounded.cells read)),
          ready.2⟩,bounded.pending,bounded.cells⟩
      · exact ⟨⟨bounded.legacy.1,True.intro,ready.2⟩,bounded.pending,bounded.cells⟩

private theorem accessFailure_numbers (bounded : StateNumbers state) :
    StateNumbers (ownedAccessFailure state object).1 := by
  simp only [ownedAccessFailure]
  split <;> try split
  all_goals exact ⟨⟨bounded.legacy.1,True.intro,StackNumbers.empty⟩,bounded.pending,bounded.cells⟩

private theorem resumeBuffer_numbers (bounded : StateNumbers state)
    (pending : state.pending = (frame,saved) :: rest) (ready : ValueNumbers value) :
    StateNumbers (resumeBuffer state frame saved rest value).1 := by
  have suspended := bounded.pending
  rw [pending] at suspended
  have top := suspended.head
  have outer := suspended.tail
  cases frame <;> cases value <;> simp only [resumeBuffer]
  all_goals first
    | exact ⟨⟨bounded.legacy.1,True.intro,StackNumbers.empty⟩,bounded.pending,bounded.cells⟩
    | skip
  case owner.owner =>
    exact ⟨⟨bounded.legacy.1,top.1.1,bounded.legacy.2.2⟩,outer.cons top.1.2 top.2,bounded.cells⟩
  case index.natural =>
    exact ⟨⟨bounded.legacy.1,top.1,bounded.legacy.2.2⟩,outer.cons ready.naturalBound top.2,bounded.cells⟩
  case value.integer =>
    split
    · rename_i heap written
      obtain ⟨metadata,cells⟩ := store_cell_numbers bounded.cells (encode_integer_bound ready.integerBound) written
      exact ⟨⟨metadata ▸ bounded.legacy.1,ValueNumbers.owner,top.2⟩,outer,cells⟩
    · exact accessFailure_numbers bounded
  case loadOwner.owner =>
    exact ⟨⟨bounded.legacy.1,top.1.1,bounded.legacy.2.2⟩,outer.cons top.1.2 top.2,bounded.cells⟩
  case loadIndex.natural =>
    split
    · rename_i payload loaded
      have integer := decode_integer_bound (load_payload_bound bounded.cells loaded)
      exact ⟨⟨bounded.legacy.1,top.1,bounded.legacy.2.2⟩,outer.cons integer top.2,bounded.cells⟩
    · exact accessFailure_numbers bounded
  case loadContinuation.closure =>
    rename_i object origin number erased domain body context origins captured
    cases erased
    · exact executeLegacy_numbers
        (state := { state with pending := (.loadOwnerArgument object origin,saved) :: rest })
        ⟨bounded.legacy,outer.cons True.intro top.2,bounded.cells⟩
        (applyValue_numbers_retained ready (.integer top.1) StackNumbers.empty)
    · exact ⟨⟨bounded.legacy.1,True.intro,StackNumbers.empty⟩,bounded.pending,bounded.cells⟩
  case loadOwnerArgument.closure =>
    rename_i object origin erased domain body context origins captured
    cases erased
    · exact executeLegacy_numbers (state := { state with pending := rest })
        ⟨bounded.legacy,outer,bounded.cells⟩
        (applyValue_numbers_retained ready .owner top.2)
    · exact ⟨⟨bounded.legacy.1,True.intro,StackNumbers.empty⟩,bounded.pending,bounded.cells⟩
  case usubLeft.natural =>
    exact ⟨⟨bounded.legacy.1,top.1,bounded.legacy.2.2⟩,outer.cons ready.naturalBound top.2,bounded.cells⟩
  case usubRight.natural =>
    split
    · exact ⟨⟨bounded.legacy.1,.natural (Nat.lt_of_le_of_lt (Nat.sub_le _ _) top.1),top.2⟩,
        outer,bounded.cells⟩
    · exact ⟨⟨bounded.legacy.1,True.intro,top.2⟩,outer,bounded.cells⟩

/-- Every indexed-buffer transition preserves numeric widths, including
faults and nested Load and Store continuations. -/
theorem step_numbers (bounded : StateNumbers state) (stepped : step state = some (next,event)) :
    StateNumbers next := by
  have controlReady := bounded.legacy.2.1
  change ControlNumbers state.control at controlReady
  cases control : state.control with
  | fault => simp [step,control] at stepped
  | evaluate code =>
      rw [control] at controlReady
      simp only [step,control] at stepped
      split at stepped
      · cases stepped
        exact ⟨⟨bounded.legacy.1,controlReady,StackNumbers.empty⟩,
          bounded.pending.cons ⟨controlReady,controlReady⟩ bounded.legacy.2.2,bounded.cells⟩
      · cases stepped
        exact ⟨⟨bounded.legacy.1,controlReady,StackNumbers.empty⟩,
          bounded.pending.cons ⟨controlReady,controlReady⟩ bounded.legacy.2.2,bounded.cells⟩
      · cases stepped
        exact ⟨⟨bounded.legacy.1,controlReady,StackNumbers.empty⟩,
          bounded.pending.cons controlReady bounded.legacy.2.2,bounded.cells⟩
      · have same := congrArg Prod.fst (Option.some.inj stepped)
        change _ = next at same
        rw [← same]
        exact executeLegacy_numbers bounded (evaluate_action_numbers controlReady bounded.legacy.2.2)
  | returned value =>
      rw [control] at controlReady
      simp only [step,control] at stepped
      cases chosen : returnAction value state.stack with
      | some action =>
          rw [chosen] at stepped
          have same := congrArg Prod.fst (Option.some.inj stepped)
          change _ = next at same
          rw [← same]
          exact executeLegacy_numbers bounded (return_action_numbers controlReady bounded.legacy.2.2 chosen)
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
              exact resumeBuffer_numbers bounded pending controlReady

theorem run_numbers (fuel : Nat) (bounded : StateNumbers state) : StateNumbers (run fuel state).state := by
  induction fuel generalizing state with
  | zero => exact bounded
  | succ fuel ih =>
      cases stepped : step state with
      | none => simpa only [run,stepped] using bounded
      | some result =>
          obtain ⟨next,event⟩ := result
          simpa only [run,stepped] using ih (step_numbers bounded stepped)

theorem initial_run_numbers (term : Term) (fuel : Nat) : StateNumbers (run fuel (initial term)).state :=
  run_numbers fuel ⟨BindingMachine.initial_numbers term,
    (fun _ member => by cases member),
    fun object _ => HeapNumbers.empty.payload object⟩

theorem initial_run_cell_bound (term : Term) (fuel object index : Nat) :
    (run fuel (initial term)).state.heap.cell object index < 2^64 :=
  (initial_run_numbers term fuel).cells object index

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
