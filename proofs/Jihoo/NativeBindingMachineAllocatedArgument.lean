import Jihoo.NativeBindingMachineCapturedBranch

/-! A source-typed captured allocation becomes an actual retained Buffer
argument. The canonical ghost allocation is reconstructed from source input
and actual numeric slots, independently of the original argument provenance.
No caller supplies output typing or a successful allocation/call certificate. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

private theorem allocated_argument_entry
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false argumentType result))
    (context : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (argument : LoanTyping.HasType env [] [] true (.alloc (.natural count) (.integer fill)) argumentType)
    (object : Nat) (origin : Term) :
    let bodyCode := enter false domain body ctx origins captured origin (some (.owner object))
    let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
    LoanClosingTyped env loans false bodyCode bodyMeanings
      (result.subst (single (.alloc (.natural count) (.integer fill)))) ∧
      ValueContext env bodyCode bodyMeanings := by
  obtain ⟨closing,localType,source,actualType⟩ := typed
  obtain ⟨sort,bodyType,binder,bodyTyped,sourceType⟩ := source.lamView
  have converted := (sourceType.substitution meanings history.wellFormed.closed).trans actualType
  have convertedPi : LoanTyping.Conversion.Conv env
      (.pi false (domain.subst meanings) (bodyType.subst (liftSubOne meanings)))
      (.pi false argumentType result) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using converted
  obtain ⟨sameFlag,domainConverted,bodyConverted⟩ := convertedPi.pi_injective history.wellFormed.admissible
  have argumentTyped := argument.convert domainConverted.symm
  have argumentKind : ValueKind env (.owner object) (domain.subst meanings) :=
    ⟨.natural count,argument.principalView.trans domainConverted.symm⟩
  refine ⟨⟨closing.consValues argumentTyped,bodyType,bodyTyped,?_⟩,
    ⟨context.closing.consValues argumentTyped,?_,?_⟩⟩
  · simpa only [subst_lift_consValues] using bodyConverted.substitution
      (single (.alloc (.natural count) (.integer fill))) history.wellFormed.closed
  · constructor
    · intro index actual stored
      cases index with
      | zero => cases stored
      | succ index => exact context.scalars.1 index actual stored
    · intro index actual stored
      cases index with
      | zero => cases stored
      | succ index => exact context.scalars.2 index actual stored
  · intro index binding actual selected stored
    cases index with
    | zero =>
        simp only [enter,lookup,Option.some.injEq] at selected
        subst binding
        have same : Value.owner object = actual := Option.some.inj (Option.some.inj stored)
        subst actual
        simpa only [shift_subst_consValues] using argumentKind
    | succ index =>
        obtain ⟨previous,found,same⟩ := Option.map_eq_some_iff.mp selected
        subst binding
        simpa only [shift_subst_consValues] using context.kinds index previous actual found stored

/-- The actual allocation inputs and the pending source function construct
both the live Buffer and its dependent retained body context. The original
source allocation and function judgments are inputs; runtime argument typing,
values, byte fit, success and output interpretation are derived. -/
theorem reachable_allocated_argument_entry (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (allocationTyped : LoanClosingTyped env allocationLoans false code allocationMeanings argumentType)
    (allocationContext : ValueContext env code allocationMeanings)
    (shape : code.term = .alloc (.var countIndex) (.var fillIndex))
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false domain body,ctx,origins,captured⟩ meanings (.pi false argumentType result))
    (functionContext : ValueContext env ⟨.lam false domain body,ctx,origins,captured⟩ meanings)
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack) :
    ∃ count fill, allocationMeanings countIndex = .natural count ∧ allocationMeanings fillIndex = .integer fill ∧
      let heap := (run fuel (initial term)).state.heap
      let bodyCode := enter false domain body ctx origins captured argumentOrigin (some (.owner heap.heap.nextObject))
      let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
      if count*8+8 < 2^64 then
        BufferValue env (SizedBufferHeap.allocate heap count (encodeInteger fill)) (.owner heap.heap.nextObject) argumentType ∧
        LoanClosingTyped env loans false bodyCode bodyMeanings
          (result.subst (single (.alloc (.natural count) (.integer fill)))) ∧
        ValueContext env bodyCode bodyMeanings ∧ bodyCode.origins 0 = argumentOrigin ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨SizedBufferHeap.allocate heap count (encodeInteger fill),.evaluate bodyCode,stack⟩,
            [.heap (.alloc heap.heap.nextObject count (encodeInteger fill)),.activate false body argumentOrigin],6⟩
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,
          .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack⟩,[],5⟩ := by
  obtain ⟨count,fill,countStored,fillStored,countMeaning,fillMeaning,countBound,fillBound,allocated⟩ :=
    reachable_captured_allocation term fuel history evaluating allocationTyped allocationContext shape
  have canonicalTyped : LoanTyping.HasType env [] [] true
      (.alloc (.natural count) (.integer fill)) argumentType := by
    simpa only [shape,Term.subst,substArgs,Op.binders,liftSub,countMeaning,fillMeaning] using
      allocationTyped.closed history
  obtain ⟨bodyTyped,bodyContext⟩ := allocated_argument_entry history functionTyped functionContext canonicalTyped
    (run fuel (initial term)).state.heap.heap.nextObject argumentOrigin
  refine ⟨count,fill,countMeaning,fillMeaning,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at allocated ⊢
    obtain ⟨buffer,executed⟩ := allocated
    rw [stackShape] at executed
    have one : run 1
        ⟨SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill),
          .returned (.owner (run fuel (initial term)).state.heap.heap.nextObject),
          .argument (.closure false domain body ctx origins captured) argumentOrigin :: stack⟩ =
        ⟨⟨SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill),
          .evaluate (enter false domain body ctx origins captured argumentOrigin
            (some (.owner (run fuel (initial term)).state.heap.heap.nextObject))),stack⟩,
          [.activate false body argumentOrigin],1⟩ := by
      simp only [run,step,action,returnAction,applyValue,execute,Option.map_some]
      rfl
    have composed := run_add 5 1 (run fuel (initial term)).state
    dsimp only at composed
    rw [executed] at composed
    dsimp only at composed
    rw [one] at composed
    exact ⟨buffer,bodyTyped,bodyContext,rfl,composed⟩
  · simpa only [fits,↓reduceIte,stackShape] using allocated

set_option linter.unusedSimpArgs false in
private theorem owned_lend_three_steps (heap : SizedBufferHeap.State) (code : Code)
    (object : Nat) (reader continuation : Term) (stack : List Frame)
    (shape : code.term = .lend (.var 0) reader continuation)
    (stored : code.values[0]? = some (some (.owner object))) (live : heap.heap.live object = true) :
    run 3 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨SizedBufferHeap.lend heap object,.evaluate (code.child reader),
        .lendReader heap.heap.nextLease object (some code.context.length) (code.origins 0)
          (code.child reader).origin (code.child continuation) :: stack⟩,
        [.heap (.beginLease heap.heap.nextLease object)],3⟩ := by
  simp only [run,step,action,evaluateAction,returnAction,execute,shape,stored,live,Code.child,
    Term.subst,Nat.sub_zero,↓reduceIte,Option.map_some]
  rfl

/-- The source allocation supplies a fresh live owner to the original typed
Lend body. Nine actual transitions allocate, bind and open its named lease;
no runtime owner, heap snapshot, live-owner or Lend-success certificate is
supplied. Reader code retains the constructed owner value context. -/
theorem reachable_allocated_argument_lend (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (allocationTyped : LoanClosingTyped env allocationLoans false code allocationMeanings argumentType)
    (allocationContext : ValueContext env code allocationMeanings)
    (shape : code.term = .alloc (.var countIndex) (.var fillIndex))
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false domain (.lend (.var 0) reader continuation),ctx,origins,captured⟩ meanings
      (.pi false argumentType result))
    (functionContext : ValueContext env
      ⟨.lam false domain (.lend (.var 0) reader continuation),ctx,origins,captured⟩ meanings)
    (stackShape : (run fuel (initial term)).state.stack =
      .argument (.closure false domain (.lend (.var 0) reader continuation) ctx origins captured) argumentOrigin :: stack) :
    ∃ count fill, allocationMeanings countIndex = .natural count ∧ allocationMeanings fillIndex = .integer fill ∧
      let heap := (run fuel (initial term)).state.heap
      let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
      let bodyCode := enter false domain (.lend (.var 0) reader continuation) ctx origins captured
        argumentOrigin (some (.owner heap.heap.nextObject))
      let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
      if count*8+8 < 2^64 then
        let lent := SizedBufferHeap.lend allocated heap.heap.nextObject
        BufferValue env lent (.owner heap.heap.nextObject) argumentType ∧
        ValueContext env (bodyCode.child reader) bodyMeanings ∧
        lent.heap.lease heap.heap.nextLease = some heap.heap.nextObject ∧
        ReaderInventory lent (readerFrames
          (.lendReader heap.heap.nextLease heap.heap.nextObject (some bodyCode.context.length) (bodyCode.origins 0)
            (bodyCode.child reader).origin (bodyCode.child continuation) :: stack)) ∧
        run 9 (run fuel (initial term)).state =
          ⟨⟨lent,.evaluate (bodyCode.child reader),
            .lendReader heap.heap.nextLease heap.heap.nextObject (some bodyCode.context.length) (bodyCode.origins 0)
              (bodyCode.child reader).origin (bodyCode.child continuation) :: stack⟩,
            [.heap (.alloc heap.heap.nextObject count (encodeInteger fill)),
              .activate false (.lend (.var 0) reader continuation) argumentOrigin,
              .heap (.beginLease heap.heap.nextLease heap.heap.nextObject)],9⟩
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,
          .argument (.closure false domain (.lend (.var 0) reader continuation) ctx origins captured)
            argumentOrigin :: stack⟩,[],5⟩ := by
  obtain ⟨count,fill,countMeaning,fillMeaning,entry⟩ := reachable_allocated_argument_entry term fuel history
    evaluating allocationTyped allocationContext shape functionTyped functionContext stackShape
  refine ⟨count,fill,countMeaning,fillMeaning,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at entry ⊢
    obtain ⟨buffer,bodyTyped,bodyContext,origin,executed⟩ := entry
    let bodyCode := enter false domain (.lend (.var 0) reader continuation) ctx origins captured
      argumentOrigin (some (.owner (run fuel (initial term)).state.heap.heap.nextObject))
    have live : (SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill)).heap.live
        (run fuel (initial term)).state.heap.heap.nextObject = true := by
      simp only [SizedBufferHeap.allocate,HeapLeases.put,ite_true]
    have lent := owned_lend_three_steps
      (SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill)) bodyCode
      (run fuel (initial term)).state.heap.heap.nextObject reader continuation stack rfl rfl live
    have composed := run_add 6 3 (run fuel (initial term)).state
    dsimp only at composed
    rw [executed] at composed
    dsimp only at composed
    rw [lent] at composed
    have inventory := run_reader_inventory (state := (run fuel (initial term)).state)
      (initial_run_heap_valid term fuel) (initial_reader_inventory term fuel) 9
    rw [composed] at inventory
    refine ⟨buffer,bodyContext.child reader,?_,inventory,composed⟩
    simp only [SizedBufferHeap.lend,SizedBufferHeap.allocate,HeapLeases.put,ite_true]
  · simpa only [fits,↓reduceIte] using entry

end Jihoo.NativeKernel.Environment.BindingMachine
