import Jihoo.NativeBindingMachineScalarClosing
import Jihoo.NativeBindingMachineOwnerProvenance

/-! A genuinely computed U64 argument becomes a retained allocation-size
binder. The source signature is closed at the actual value, rather than by
assuming conversion of its effectful provenance to a numeral. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

set_option linter.unusedSimpArgs false in
private theorem computed_allocation_six_steps (heap : SizedBufferHeap.State)
    (domain : Term) (context : Context) (origins : Nat → Term) (captured : List (Option Value))
    (argumentOrigin : Term) (count : Nat) (fill : Int) (stack : List Frame)
    (fillBound : ValueReduction.signed64 fill) :
    run 6 ⟨heap,.returned (.natural count),
      .argument (.closure false domain (.alloc (.var 0) (.integer fill)) context origins captured) argumentOrigin :: stack⟩ =
      if count*8+8 < 2^64 then
        ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
          [.activate false (.alloc (.var 0) (.integer fill)) argumentOrigin,
            .heap (.alloc heap.heap.nextObject count (encodeInteger fill))],6⟩
      else
        ⟨⟨heap,.fault .allocationOverflow,stack⟩,
          [.activate false (.alloc (.var 0) (.integer fill)) argumentOrigin],6⟩ := by
  simp only [run,step,action,returnAction,applyValue,execute,evaluateAction,enter,Code.child,
    List.getElem?_cons_zero,fillBound,↓reduceIte,Option.map_some]
  split <;> simp_all only [↓reduceIte] <;> rfl

/-- The complete source function typing determines the actual dependent
Buffer type after binding a runtime natural. Neither a literal source count
nor typing of an observed output is a premise. -/
theorem computed_allocation_entry_typing
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain (.alloc (.var 0) (.integer fill)),context,origins,captured⟩ meanings
      (.pi false .u64 (.buffer (.var 0))))
    (bounded : count < 2^64) (argumentOrigin : Term) :
    let bodyCode := enter false domain (.alloc (.var 0) (.integer fill)) context origins captured argumentOrigin (some (.natural count))
    LoanClosingTyped env loans false bodyCode (consValues (.natural count) meanings) (.buffer (.natural count)) ∧
      ValueReduction.signed64 fill := by
  have entered := enter_natural_closing history typed bounded argumentOrigin
  have bodyTyped : LoanClosingTyped env loans false
      (enter false domain (.alloc (.var 0) (.integer fill)) context origins captured argumentOrigin (some (.natural count)))
      (consValues (.natural count) meanings) (.buffer (.natural count)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub,single] using entered
  have closed : LoanTyping.HasType env [] [] true (.alloc (.natural count) (.integer fill)) (.buffer (.natural count)) := by
    simpa only [enter,Term.subst,substArgs,Op.binders,liftSub,consValues] using bodyTyped.closed history
  exact ⟨bodyTyped,closed.alloc_inputs.2.integer_bound⟩

private theorem argument_capture_owners
    (owners : StackOwners limit
      (.argument (.closure false domain body context origins captured) argumentOrigin :: stack)) :
    ValuesOwners limit captured := by
  have function := owners.head
  change ValueOwners limit (.closure false domain body context origins captured) at function
  cases function with
  | closure ready => exact ready

/-- At any actual natural call boundary, construct the dependent allocation
and its Buffer interpretation. Bounds, freshness and absence from every old
capture come from reachability. The source origin is retained and never
assumed convertible to the actual numeral. Byte overflow remains explicit. -/
theorem reachable_computed_allocation (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain (.alloc (.var 0) (.integer fill)),context,origins,captured⟩ meanings
      (.pi false .u64 (.buffer (.var 0))))
    (returned : (run fuel (initial term)).state.control = .returned (.natural count))
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain (.alloc (.var 0) (.integer fill)) context origins captured) argumentOrigin :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let bodyCode := enter false domain (.alloc (.var 0) (.integer fill)) context origins captured argumentOrigin (some (.natural count))
    LoanClosingTyped env loans false bodyCode (consValues (.natural count) meanings) (.buffer (.natural count)) ∧
      bodyCode.origins 0 = argumentOrigin ∧
      (∀ (index : Nat) value, captured[index]? = some (some value) → ¬ OwnerOccurs heap.heap.nextObject value) ∧
      if count*8+8 < 2^64 then
        BufferValue env (SizedBufferHeap.allocate heap count (encodeInteger fill)) (.owner heap.heap.nextObject) (.buffer (.natural count)) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
            [.activate false (.alloc (.var 0) (.integer fill)) argumentOrigin,
              .heap (.alloc heap.heap.nextObject count (encodeInteger fill))],6⟩
      else run 6 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,stack⟩,
          [.activate false (.alloc (.var 0) (.integer fill)) argumentOrigin],6⟩ := by
  have bounded := initial_run_natural_bound term fuel returned
  obtain ⟨bodyTyped,fillBound⟩ := computed_allocation_entry_typing history typed bounded argumentOrigin
  have owners := (initial_run_owners term fuel).2
  rw [stackShape] at owners
  have capturedOwners := argument_capture_owners owners
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.returned (.natural count),
        .argument (.closure false domain (.alloc (.var 0) (.integer fill)) context origins captured) argumentOrigin :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have executed := computed_allocation_six_steps (run fuel (initial term)).state.heap domain context origins captured argumentOrigin count fill stack fillBound
  rw [← stateShape] at executed
  refine ⟨bodyTyped,rfl,?_,?_⟩
  · intro index value stored occurs
    have earlier := occurs.before_limit (capturedOwners.valueAt stored)
    omega
  · by_cases fits : count*8+8 < 2^64
    · simp only [fits,↓reduceIte] at executed ⊢
      exact ⟨BufferValue.allocate (.refl _),executed⟩
    · simpa only [fits,↓reduceIte] using executed

/-- A returned second closure retains the computed size and source origin,
while its input type is closed at the actual size. -/
theorem two_scalar_second_entry_typing
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false countDomain (.lam false fillDomain (.alloc (.var 1) (.var 0))),context,origins,captured⟩ meanings
      (.pi false .u64 (.pi false .i64 (.buffer (.var 1)))))
    (bounded : count < 2^64) (countOrigin : Term) :
    LoanClosingTyped env loans false
      ⟨.lam false fillDomain (.alloc (.var 1) (.var 0)),⟨countDomain,false⟩ :: context,
        consValues countOrigin origins,some (.natural count) :: captured⟩ (consValues (.natural count) meanings)
      (.pi false .i64 (.buffer (.natural count))) := by
  have entered := enter_natural_closing history typed bounded countOrigin
  simpa only [enter,Term.subst,substArgs,Op.binders,liftSub,liftSubOne,single,Term.rename,renameArgs,liftRenaming] using entered

set_option linter.unusedSimpArgs false in
private theorem two_scalar_six_steps (heap : SizedBufferHeap.State)
    (domain : Term) (context : Context) (origins : Nat → Term) (captured : List (Option Value))
    (argumentOrigin : Term) (count : Nat) (fill : Int) (stack : List Frame) :
    run 6 ⟨heap,.returned (.integer fill),
      .argument (.closure false domain (.alloc (.var 1) (.var 0)) context origins (some (.natural count) :: captured)) argumentOrigin :: stack⟩ =
      if count*8+8 < 2^64 then
        ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
          [.activate false (.alloc (.var 1) (.var 0)) argumentOrigin,
            .heap (.alloc heap.heap.nextObject count (encodeInteger fill))],6⟩
      else
        ⟨⟨heap,.fault .allocationOverflow,stack⟩,
          [.activate false (.alloc (.var 1) (.var 0)) argumentOrigin],6⟩ := by
  simp only [run,step,action,returnAction,applyValue,execute,evaluateAction,enter,Code.child,
    List.getElem?_cons_zero,List.getElem?_cons_succ,↓reduceIte,Option.map_some]
  split <;> simp_all only [↓reduceIte] <;> rfl

/-- Both size and fill may be computed before this captured second call.
The value closing uses both actual values and allocation reads both retained
slots, without output typing or source-origin conversion assumptions. -/
theorem reachable_two_scalar_allocation (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain (.alloc (.var 1) (.var 0)),context,origins,some (.natural count) :: captured⟩
      (consValues (.natural count) meanings) (.pi false .i64 (.buffer (.natural count))))
    (returned : (run fuel (initial term)).state.control = .returned (.integer fill))
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain (.alloc (.var 1) (.var 0)) context origins (some (.natural count) :: captured)) argumentOrigin :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let bodyCode := enter false domain (.alloc (.var 1) (.var 0)) context origins (some (.natural count) :: captured)
      argumentOrigin (some (.integer fill))
    LoanClosingTyped env loans false bodyCode (consValues (.integer fill) (consValues (.natural count) meanings)) (.buffer (.natural count)) ∧
      bodyCode.origins 0 = argumentOrigin ∧
      if count*8+8 < 2^64 then
        BufferValue env (SizedBufferHeap.allocate heap count (encodeInteger fill)) (.owner heap.heap.nextObject) (.buffer (.natural count)) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.returned (.owner heap.heap.nextObject),stack⟩,
            [.activate false (.alloc (.var 1) (.var 0)) argumentOrigin,
              .heap (.alloc heap.heap.nextObject count (encodeInteger fill))],6⟩
      else run 6 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,stack⟩,
          [.activate false (.alloc (.var 1) (.var 0)) argumentOrigin],6⟩ := by
  have bounded := initial_run_integer_bound term fuel returned
  have entryTyped := enter_integer_closing history typed bounded argumentOrigin
  have bodyTyped : LoanClosingTyped env loans false
      (enter false domain (.alloc (.var 1) (.var 0)) context origins (some (.natural count) :: captured)
        argumentOrigin (some (.integer fill)))
      (consValues (.integer fill) (consValues (.natural count) meanings)) (.buffer (.natural count)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub,single] using entryTyped
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.returned (.integer fill),
        .argument (.closure false domain (.alloc (.var 1) (.var 0)) context origins (some (.natural count) :: captured)) argumentOrigin :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have executed := two_scalar_six_steps (run fuel (initial term)).state.heap domain context origins captured argumentOrigin count fill stack
  rw [← stateShape] at executed
  refine ⟨bodyTyped,rfl,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at executed ⊢
    exact ⟨BufferValue.allocate (.refl _),executed⟩
  · simpa only [fits,↓reduceIte] using executed

end Jihoo.NativeKernel.Environment.BindingMachine
