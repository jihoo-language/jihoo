import Jihoo.NativeBindingMachineIndexValues

/-! Actual Index executions with exact original source types. Heap validity,
reader inventory and numeric interpretation come from the real initial prefix;
source/control/owner-slot association is still the local fundamental gap. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

theorem LoanSourceTyped.ifLt_no
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .ifLt left right yes no) :
    LoanSourceTyped env loans mode (code.child no) type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨result,leftTyped,rightTyped,yesTyped,noTyped⟩ := source.ifLt_inputs
  have rebuilt : LoanTyping.HasType env loans code.context mode (.ifLt left right yes no) result :=
    .ifLt leftTyped rightTyped yesTyped noTyped
  have original := rebuilt.unique history.wellFormed source
  exact ⟨closing,result,noTyped,(original.substitution code.origins history.wellFormed.closed).trans converted⟩

/-- Literal proof typing constructs the five transitions and original-type
integer. Reachability supplies validity, readers and numeric bounds; callers
supply no safe-event, successful-run or output-typing certificate. -/
theorem reachable_named_index_execution (term : Term) (entryFuel fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (allocated : (run entryFuel (initial term)).state.heap = SizedBufferHeap.allocate before count fill)
    (code : Code) (evaluating : (run fuel (run entryFuel (initial term)).state).state.control = .evaluate code)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .index (.borrow (.var owner)) (.natural offset)
      (.decide (.natural offset) (.natural count)))
    (slots : LoanSlots code loans (run fuel (run entryFuel (initial term)).state).state.stack)
    (stored : code.values[owner]? = some (some (.owner before.heap.nextObject))) :
    ∃ token,
      run 5 (run fuel (run entryFuel (initial term)).state).state =
        ⟨⟨(run fuel (run entryFuel (initial term)).state).state.heap,
          .returned (.integer (decodeInteger ((run fuel (run entryFuel (initial term)).state).state.heap.heap.payload before.heap.nextObject))),
          (run fuel (run entryFuel (initial term)).state).state.stack⟩,
          [.heap (.read token offset ((run fuel (run entryFuel (initial term)).state).state.heap.heap.payload before.heap.nextObject))],5⟩ ∧
      LoanTyping.HasType env [] [] true
        (.integer (decodeInteger ((run fuel (run entryFuel (initial term)).state).state.heap.heap.payload before.heap.nextObject))) type := by
  have original := typed.index_conversion history shape
  obtain ⟨closing,localType,source,converted⟩ := typed
  obtain ⟨token,executed⟩ := allocated_named_index_executes_valid history
    (initial_run_heap_valid term entryFuel) (initial_reader_inventory term entryFuel) allocated fuel evaluating source shape slots stored
  have bounded := decode_integer_bound
    ((run_numbers (initial_run_numbers term entryFuel) fuel).1.payload before.heap.nextObject)
  exact ⟨token,executed,(LoanTyping.HasType.integer bounded.1 bounded.2).convert original⟩

/-- The actual comparison selects either a constructed original-type read
result or entry into the original-type else body. No reader/heap/numeric
invariant is supplied by the caller. General slot/layout and control typing
must still be reconstructed for arbitrary admitted source programs. -/
theorem reachable_dynamic_index_execution (term : Term) (entryFuel fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (allocated : (run entryFuel (initial term)).state.heap = SizedBufferHeap.allocate before count fill)
    (code : Code) (evaluating : (run fuel (run entryFuel (initial term)).state).state.control = .evaluate code)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no)
    (entered : Loans.Entered code.context.length loans)
    (slots : LoanSlots code loans (run fuel (run entryFuel (initial term)).state).state.stack)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (storedOwner : code.values[owner]? = some (some (.owner before.heap.nextObject))) :
    if offset < count then
      ∃ token,
        run 10 (run fuel (run entryFuel (initial term)).state).state =
          ⟨⟨(run fuel (run entryFuel (initial term)).state).state.heap,
            .returned (.integer (decodeInteger ((run fuel (run entryFuel (initial term)).state).state.heap.heap.payload before.heap.nextObject))),
            (run fuel (run entryFuel (initial term)).state).state.stack⟩,
            [.heap (.read token offset ((run fuel (run entryFuel (initial term)).state).state.heap.heap.payload before.heap.nextObject))],10⟩ ∧
        LoanTyping.HasType env [] [] true
          (.integer (decodeInteger ((run fuel (run entryFuel (initial term)).state).state.heap.heap.payload before.heap.nextObject))) type
    else run 5 (run fuel (run entryFuel (initial term)).state).state =
        ⟨⟨(run fuel (run entryFuel (initial term)).state).state.heap,.evaluate (code.child no),
          (run fuel (run entryFuel (initial term)).state).state.stack⟩,[],5⟩ ∧
      LoanSourceTyped env loans false (code.child no) type := by
  have original := typed.ifLt_index_conversion history shape
  have elseTyped := typed.ifLt_no history shape
  obtain ⟨closing,localType,source,converted⟩ := typed
  have executed := allocated_dynamic_index_executes_valid (initial_run_heap_valid term entryFuel)
    (initial_reader_inventory term entryFuel) allocated fuel code evaluating source shape entered slots
    storedIndex storedLength storedOwner
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte] at executed ⊢
    obtain ⟨token,executed⟩ := executed
    have bounded := decode_integer_bound
      ((run_numbers (initial_run_numbers term entryFuel) fuel).1.payload before.heap.nextObject)
    exact ⟨token,executed,(LoanTyping.HasType.integer bounded.1 bounded.2).convert original⟩
  · simp only [compared,↓reduceIte] at executed ⊢
    exact ⟨executed,elseTyped⟩

end Jihoo.NativeKernel.Environment.BindingMachine
