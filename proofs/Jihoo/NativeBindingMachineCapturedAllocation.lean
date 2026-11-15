import Jihoo.NativeBindingMachineValueKinds

/-! Allocation reads arbitrary typed captured size/fill slots. Source variable
inversion and the value context construct their runtime representations,
bounds and dependent result annotation; stored numbers and success are outputs.
The full admission-to-control-stack invariant remains a separate obligation. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

set_option linter.unusedSimpArgs false in
private theorem captured_allocation_five_steps (heap : SizedBufferHeap.State)
    (code : Code) (countIndex fillIndex count : Nat) (fill : Int) (stack : List Frame)
    (shape : code.term = .alloc (.var countIndex) (.var fillIndex))
    (countStored : code.values[countIndex]? = some (some (.natural count)))
    (fillStored : code.values[fillIndex]? = some (some (.integer fill))) :
    run 5 ⟨heap,.evaluate code,stack⟩ =
      if count*8+8 < 2^64 then
        ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
          [.heap (.alloc heap.heap.nextObject count (encodeInteger fill))],5⟩
      else ⟨⟨heap,.fault .allocationOverflow,stack⟩,[],5⟩ := by
  simp only [run,step,action,evaluateAction,returnAction,execute,shape,Code.child,
    countStored,fillStored,Option.map_some,Option.map_none]
  split <;> simp_all only [↓reduceIte] <;> rfl

/-- The input is the original full source allocation judgment at any actual
prefix, with its constructed captured-value context. Neither selected numeric
values, width certificates, output typing nor an allocation-success oracle is
an input. Successful execution realizes the SAME closed source result type. -/
theorem reachable_captured_allocation (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (shape : code.term = .alloc (.var countIndex) (.var fillIndex)) :
    ∃ count fill,
      code.values[countIndex]? = some (some (.natural count)) ∧
      code.values[fillIndex]? = some (some (.integer fill)) ∧
      meanings countIndex = .natural count ∧ meanings fillIndex = .integer fill ∧
      count < 2^64 ∧ ValueReduction.signed64 fill ∧
      let heap := (run fuel (initial term)).state.heap
      let stack := (run fuel (initial term)).state.stack
      if count*8+8 < 2^64 then
        BufferValue env (SizedBufferHeap.allocate heap count (encodeInteger fill)) (.owner heap.heap.nextObject) type ∧
        run 5 (run fuel (initial term)).state =
          ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
            [.heap (.alloc heap.heap.nextObject count (encodeInteger fill))],5⟩
      else run 5 (run fuel (initial term)).state = ⟨⟨heap,.fault .allocationOverflow,stack⟩,[],5⟩ := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  have aligned := initial_run_code_aligned term fuel _ evaluating
  have countTyped : LoanClosingTyped env loans false (code.child (.var countIndex)) meanings .u64 :=
    ⟨closing,.u64,source.alloc_inputs.1,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  have fillTyped : LoanClosingTyped env loans false (code.child (.var fillIndex)) meanings .i64 :=
    ⟨closing,.i64,source.alloc_inputs.2,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .i64 .i64 from .refl _)⟩
  obtain ⟨countValue,countStored,countKind⟩ := (context.child _).variable_kind history countTyped aligned rfl
  obtain ⟨fillValue,fillStored,fillKind⟩ := (context.child _).variable_kind history fillTyped aligned rfl
  obtain ⟨count,rfl⟩ := countKind.natural_shape history.wellFormed.admissible
  obtain ⟨fill,rfl⟩ := fillKind.integer_shape history.wellFormed.admissible
  have countMeaning := context.scalars.1 countIndex count countStored
  have fillMeaning := context.scalars.2 fillIndex fill fillStored
  have countBound : count < 2^64 := by
    have actual := countTyped.closed history
    simp only [Code.child,Term.subst,countMeaning] at actual
    exact actual.natural_bound
  have fillBound : ValueReduction.signed64 fill := by
    have actual := fillTyped.closed history
    simp only [Code.child,Term.subst,fillMeaning] at actual
    exact actual.integer_bound
  have resultConverted := (source.principalView.substitution meanings history.wellFormed.closed).trans converted
  have bufferConverted : LoanTyping.Conversion.Conv env (.buffer (.natural count)) type := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub,countMeaning] using resultConverted
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate code,(run fuel (initial term)).state.stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have executed := captured_allocation_five_steps (run fuel (initial term)).state.heap code
    countIndex fillIndex count fill (run fuel (initial term)).state.stack shape countStored fillStored
  rw [← stateShape] at executed
  refine ⟨count,fill,countStored,fillStored,countMeaning,fillMeaning,countBound,fillBound,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at executed ⊢
    exact ⟨BufferValue.allocate bufferConverted,executed⟩
  · simpa only [fits,↓reduceIte] using executed

end Jihoo.NativeKernel.Environment.BindingMachine
