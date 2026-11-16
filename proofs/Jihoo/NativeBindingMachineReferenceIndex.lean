import Jihoo.NativeBindingMachineSizedBorrow

/-! A reader uses its actual reference argument. The authentic full Lend input
and immutable captured owner sizes construct the real Index guard, including
specialized checked readers and arbitrary nested outer reader frames. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds

/-- Source read typing connects literal evidence to the actual owner length
and the real reference binder's annotation. No allocation snapshot is needed. -/
theorem LoanClosingTyped.reference_index_heap
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode code meanings type)
    (sizes : OwnerSizes env heap code meanings)
    (shape : code.term = .lend (.var owner)
      (.lam false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))))
      (.lam false first (.lam false again body)))
    (stored : code.values[owner]? = some (some (.owner object))) :
    ∃ valueType, LoanTyping.Outlived env valueType ∧ offset < 2^64 ∧ offset < count ∧
      heap.length object = count ∧ LoanTyping.Conversion.Conv env .i64 (valueType.subst meanings) ∧
      LoanTyping.Conversion.Conv env (.ref (.buffer (.natural count))) (domain.subst meanings) := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨ownerType,valueType,sort,ownerTyped,owned,binder,domainConverted,readTyped,outlived⟩ :=
    source.explicitLendReaderInputs history.wellFormed
  simp only [Lending.read,Term.subst,substArgs,Op.binders,liftSub,single] at readTyped
  obtain ⟨size,indexOwner,indexTyped,evidence⟩ := readTyped.named_index_owner history.wellFormed
  obtain ⟨offsetBound,countBound,ordered⟩ := evidence.literal_decide_limits history.wellFormed
  have indexedSize := sizes.typed_variable history indexOwner stored
  have bufferSize : OwnerSize env heap object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using indexedSize
  have physical := bufferSize.buffer_length history
  have closedEvidence := evidence.ghostSubstitution history.wellFormed closing
  have evidenceTyped : LoanTyping.HasType env [] [] true (.decide (.natural offset) (.natural count))
      (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using closedEvidence
  have checked := (evidenceTyped.principalView.lt_injective history.wellFormed.admissible).2
  have length : heap.length object = count :=
    (physical.trans checked.symm).natural_injective history.wellFormed.admissible
  have readerType : LoanTyping.Conversion.Conv env .i64 (valueType.subst meanings) := by
    simpa only [Term.subst,substArgs] using
      readTyped.principalView.substitution meanings history.wellFormed.closed
  have ownerSize := (sizes.typed_variable history ownerTyped stored).realization
  rw [length] at ownerSize
  have domainClosed : LoanTyping.Conversion.Conv env (domain.subst meanings)
      (.ref (ownerType.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      domainConverted.substitution meanings history.wellFormed.closed
  exact ⟨valueType,outlived,offsetBound,ordered,length,readerType,
    (RawLend.Conv.node .ref (.cons ownerSize .nil)).trans domainClosed.symm⟩

set_option linter.unusedSimpArgs false in
private theorem reference_reader_six_steps (heap : SizedBufferHeap.State) (code : Code)
    (domain : Term) (offset count token object : Nat) (name : Option Nat)
    (ownerOrigin readerOrigin : Term) (continuation : Code) (rest : List Frame)
    (offsetBound : offset < 2^64) (leased : heap.heap.lease token = some object)
    (bound : offset < heap.length object) :
    let readerBody := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
    let bodyCode := enter false domain readerBody code.context code.origins code.values
      (.borrow ownerOrigin) (some (.reference token))
    run 6 ⟨heap,.returned (.closure false domain readerBody code.context code.origins code.values),
      .lendReader token object name ownerOrigin readerOrigin continuation :: rest⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),
        .lendFinish token object name ownerOrigin bodyCode.origin continuation :: rest⟩,
        [.activate false readerBody (.borrow ownerOrigin),.heap (.read token offset (heap.heap.payload object))],6⟩ := by
  simp only [run,step,action,returnAction,applyValue,execute,evaluateAction,enter,Code.child,
    List.getElem?_cons_zero,offsetBound,leased,bound,↓reduceIte,Option.map_some]
  rfl

/-- The complete input Lend constructs a successful read through the actual
reference argument in six transitions, including activation. Bound and length
are outputs, and the read integer has its source-derived reader result type.
No arbitrary callback typing, successful read or output typing is supplied. -/
theorem reachable_reference_index_reader (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (sourceShape : code.term = .lend (.var owner)
      (.lam false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))))
      (.lam false first (.lam false again body)))
    (slots : LoanSlots code loans rest) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (controlShape : (run fuel (initial term)).state.control = .returned
      (.closure false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count)))
        code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerOrigin continuation :: rest) :
    let heap := (run fuel (initial term)).state.heap
    let readerBody := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
    let bodyCode := enter false domain readerBody code.context code.origins code.values
      (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
    let bodyMeanings := consValues (.borrow ((Term.var owner).subst meanings)) meanings
    let afterStack := .lendFinish token object (some (code.context.length-owner))
      ((Term.var owner).subst code.origins) bodyCode.origin continuation :: rest
    ∃ valueType, LoanTyping.Outlived env valueType ∧ heap.length object = count ∧ offset < count ∧
      ReferenceSize env heap token (domain.subst meanings) ∧
      LoanTyping.HasType env [] [] true (.integer (decodeInteger (heap.heap.payload object))) (valueType.subst meanings) ∧
      ValueContext env bodyCode bodyMeanings ∧ OwnerSizes env heap bodyCode bodyMeanings ∧
      LoanSlots bodyCode (Loans.enter code.context.length owner loans) afterStack ∧
      ReaderInventory heap (readerFrames afterStack) ∧
      run 6 (run fuel (initial term)).state =
        ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),afterStack⟩,
          [.activate false readerBody (.borrow ((Term.var owner).subst code.origins)),
            .heap (.read token offset (heap.heap.payload object))],6⟩ := by
  obtain ⟨valueType,outlived,offsetBound,ordered,length,readerType,referenceType⟩ :=
    typed.reference_index_heap history sizes sourceShape stored
  obtain ⟨actualType,actualOutlived,bodyTyped,bodyContext,bodySlots,leased,live,activated⟩ :=
    reachable_value_reader_activation term fuel code history typed context sourceShape slots entered stored controlShape stackShape
  have valueTyped := (initial_run_decoded_integer_typed (env := env) term fuel object).convert readerType
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,
        .returned (.closure false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count)))
          code.context code.origins code.values),
        .lendReader token object (some (code.context.length-owner))
          ((Term.var owner).subst code.origins) readerOrigin continuation :: rest⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have executed := reference_reader_six_steps (run fuel (initial term)).state.heap code domain offset count token object
    (some (code.context.length-owner)) ((Term.var owner).subst code.origins) readerOrigin continuation rest
    offsetBound leased (by omega)
  dsimp only at executed
  rw [← stateShape] at executed
  have inventory := run_reader_inventory (state := (run fuel (initial term)).state)
    (initial_run_heap_valid term fuel) (initial_reader_inventory term fuel) 6
  rw [executed] at inventory
  refine ⟨valueType,outlived,length,ordered,⟨object,count,leased,live,length,referenceType⟩,
    valueTyped,bodyContext,sizes.enter_reference _ _ _ _ _,bodySlots,inventory,executed⟩

end Jihoo.NativeKernel.Environment.BindingMachine
