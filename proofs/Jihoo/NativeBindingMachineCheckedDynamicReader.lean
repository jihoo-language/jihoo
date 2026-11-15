import Jihoo.NativeBindingMachineValueHandoff

/-! The actual resource check supplies its specialized CODE read, even when
no arbitrary-argument callback judgment exists. That read determines captured
operands and the true Buffer length; execution uses the real reference binder. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- A comparison-guarded reader uses its retained reference below the erased
comparison hypothesis. Other captures shift under the reference binder. -/
def dynamicReferenceReader (index length : Nat) (no : Term) : Term :=
  .ifLt (.var (index+1)) (.var (length+1))
    (.index (.var 1) (.var (index+2)) (.var 0)) (no.rename Nat.succ)

theorem dynamic_reference_read_source (owner index length : Nat) (no : Term) :
    Lending.read (.var owner) (dynamicReferenceReader index length no) =
      .ifLt (.var index) (.var length) (dynamicRead owner index) no := by
  simp only [Lending.read,dynamicReferenceReader,dynamicRead,Term.subst,substArgs,Op.binders,liftSub,
    liftSubOne,single,Term.rename,renameArgs,liftRenaming,Term.shift_subst_single]

/-- The same original projection retains its authentic source judgment,
specialized read and zero/one owner contract. No callback typing is invented. -/
theorem checked_dynamic_reader_source
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans ctx
      (.lend (.var owner) (.lam false domain (dynamicReferenceReader index length no))
        (.lam false first (.lam false again body))) = some control) :
    ∃ outside reader mode rest,
      LoanTyping.HasType env loans ctx false
        (.lend (.var owner) (.lam false domain (dynamicReferenceReader index length no))
          (.lam false first (.lam false again body))) outside ∧
      LoanTyping.HasType env (Loans.enter ctx.length owner loans) ctx false
        (.ifLt (.var index) (.var length) (dynamicRead owner index) no) first ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter ctx.length owner loans) ctx
        (.ifLt (.var index) (.var length) (dynamicRead owner index) no) = some reader ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans (⟨first,false⟩ :: ctx)
        (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      reader.demand owner = some 0 ∧ (Jihoo.Quantity.Control.scope mode rest).demand owner = some 1 ∧
      control = .seq reader (.scope mode rest) := by
  obtain ⟨outside,sort,result,reader,mode,rest,originalScope,readScope,restScope,formed,controlScoped,
    sourceTyped,readTyped,binder,bodyTyped,resolved,readProjected,restProjected,readZero,restOne,same⟩ :=
    LoanTyping.ResourceQuantity.dependent_project_contract checked
  rw [dynamic_reference_read_source] at readTyped readProjected
  exact ⟨outside,reader,mode,rest,sourceTyped,readTyped,readProjected,restProjected,readZero,restOne,same⟩

private theorem checked_natural_slot
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (context : ValueContext env code meanings) (aligned : CodeAligned code)
    (typed : LoanTyping.HasType env stack code.context false (.var index) .u64) :
    ∃ number, code.values[index]? = some (some (.natural number)) ∧ meanings index = .natural number := by
  have closed : LoanClosingTyped env stack false (code.child (.var index)) meanings .u64 :=
    ⟨context.closing,.u64,typed,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨value,stored,kind⟩ := (context.child _).variable_kind history closed aligned rfl
  obtain ⟨number,rfl⟩ := kind.natural_shape history.wellFormed.admissible
  exact ⟨number,stored,context.scalars.1 index number stored⟩

/-- This only substitutes in proved conversion equations to remove an erased
source binder. The dummy substitution is never used as a typed proof. -/
private theorem checked_reader_length
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env stack code.context false
      (.ifLt (.var index) (.var length) (dynamicRead owner index) no) first)
    (sizes : OwnerSizes env heap code meanings)
    (stored : code.values[owner]? = some (some (.owner object)))
    (lengthMeaning : meanings length = .natural count) : heap.length object = count := by
  obtain ⟨result,leftTyped,rightTyped,yesTyped,noTyped⟩ := typed.ifLt_inputs
  obtain ⟨size,ownerTyped,indexTyped,evidence⟩ := yesTyped.named_index_owner history.wellFormed
  let branch := branchCode false (code.child (dynamicRead owner index)) (.var index) (.var length)
  let branchMeanings := consValues (.natural 0) meanings
  have branchSizes : OwnerSizes env heap branch branchMeanings := sizes.branch false _ _ _ _
  have ownerStored : branch.values[owner+1]? = some (some (.owner object)) := by
    simpa only [branch,branchCode,Code.child,List.getElem?_cons_succ] using stored
  have ownerSize := branchSizes.typed_variable history ownerTyped ownerStored
  have bufferSize : OwnerSize env heap object (.buffer (size.subst branchMeanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using ownerSize
  have physical := bufferSize.buffer_length history
  obtain ⟨binding,selected,converted⟩ := evidence.principalView
  simp only [lookup,Option.some.injEq] at selected
  subst binding
  have boundTypes : LoanTyping.Conversion.Conv env
      (.lt (.var (index+1)) (.var (length+1))) (.lt (.var (index+1)) size) := by
    simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using converted
  have lengthConverted := (boundTypes.lt_injective history.wellFormed.admissible).2.substitution
    branchMeanings history.wellFormed.closed
  have actual : LoanTyping.Conversion.Conv env (.natural count) (size.subst branchMeanings) := by
    simpa only [branchMeanings,Term.subst,consValues,lengthMeaning] using lengthConverted
  exact (physical.trans actual.symm).natural_injective history.wellFormed.admissible

set_option linter.unusedSimpArgs false in
private theorem dynamic_reference_eleven_steps (heap : SizedBufferHeap.State) (code : Code)
    (domain no : Term) (index length offset count token object : Nat) (name : Option Nat)
    (ownerOrigin readerOrigin : Term) (continuation : Code) (rest : List Frame)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (leased : heap.heap.lease token = some object) (size : heap.length object = count)
    (compared : offset < count) :
    let readerBody := dynamicReferenceReader index length no
    let bodyCode := enter false domain readerBody code.context code.origins code.values
      (.borrow ownerOrigin) (some (.reference token))
    run 11 ⟨heap,.returned (.closure false domain readerBody code.context code.origins code.values),
      .lendReader token object name ownerOrigin readerOrigin continuation :: rest⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),
        .lendFinish token object name ownerOrigin bodyCode.origin continuation :: rest⟩,
        [.activate false readerBody (.borrow ownerOrigin),.heap (.read token offset (heap.heap.payload object))],11⟩ := by
  simp only [run,step,action,returnAction,applyValue,execute,evaluateAction,enter,Code.child,
    dynamicReferenceReader,branchCode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    storedIndex,storedLength,leased,size,compared,decide_true,Bool.false_eq_true,↓reduceIte,Option.map_some]
  rfl

set_option linter.unusedSimpArgs false in
private theorem dynamic_reference_else_six_steps (heap : SizedBufferHeap.State) (code : Code)
    (domain no : Term) (index length offset count token object : Nat) (name : Option Nat)
    (ownerOrigin readerOrigin : Term) (continuation : Code) (rest : List Frame)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (compared : ¬ offset < count) :
    let readerBody := dynamicReferenceReader index length no
    let bodyCode := enter false domain readerBody code.context code.origins code.values
      (.borrow ownerOrigin) (some (.reference token))
    run 6 ⟨heap,.returned (.closure false domain readerBody code.context code.origins code.values),
      .lendReader token object name ownerOrigin readerOrigin continuation :: rest⟩ =
      ⟨⟨heap,.evaluate (bodyCode.child (no.rename Nat.succ)),
        .lendFinish token object name ownerOrigin bodyCode.origin continuation :: rest⟩,
        [.activate false readerBody (.borrow ownerOrigin)],6⟩ := by
  simp only [run,step,action,returnAction,applyValue,execute,evaluateAction,enter,Code.child,
    dynamicReferenceReader,List.getElem?_cons_zero,List.getElem?_cons_succ,
    storedIndex,storedLength,compared,decide_false,Bool.false_eq_true,↓reduceIte,Option.map_some]
  rfl

/-- The actual full resource check constructs source typing, captured numeric
values and the physical read bound. The reader's original reference binder is
executed; neither a generic callback nor numeric/output/success oracle occurs. -/
theorem reachable_checked_dynamic_reference_reader (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (shape : code.term = .lend (.var owner) (.lam false domain (dynamicReferenceReader index length no))
      (.lam false first (.lam false again body)))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (stored : code.values[owner]? = some (some (.owner object)))
    (returned : (run fuel (initial term)).state.control = .returned
      (.closure false domain (dynamicReferenceReader index length no) code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
        readerOrigin continuation :: rest) :
    ∃ outside offset count reader mode remaining,
      LoanClosingTyped env loans false code meanings (Term.subst meanings outside) ∧
      code.values[index]? = some (some (.natural offset)) ∧ code.values[length]? = some (some (.natural count)) ∧
      meanings index = .natural offset ∧ meanings length = .natural count ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter code.context.length owner loans) code.context
        (.ifLt (.var index) (.var length) (dynamicRead owner index) no) = some reader ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans (⟨first,false⟩ :: code.context)
        (body.subst (single ((Term.var owner).rename Nat.succ))) = some remaining ∧
      reader.demand owner = some 0 ∧ (Jihoo.Quantity.Control.scope mode remaining).demand owner = some 1 ∧
      control = .seq reader (.scope mode remaining) ∧
      let heap := (run fuel (initial term)).state.heap
      let readerBody := dynamicReferenceReader index length no
      let bodyCode := enter false domain readerBody code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
      let bodyMeanings := consValues (.borrow ((Term.var owner).subst meanings)) meanings
      let afterStack := .lendFinish token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) bodyCode.origin continuation :: rest
      heap.length object = count ∧ heap.heap.lease token = some object ∧ heap.heap.live object = true ∧
      ValueContext env bodyCode bodyMeanings ∧ OwnerSizes env heap bodyCode bodyMeanings ∧
      if offset < count then
        LoanTyping.HasType env [] [] true (.integer (decodeInteger (heap.heap.payload object))) (first.subst meanings) ∧
        ReaderInventory heap (readerFrames afterStack) ∧
        run 11 (run fuel (initial term)).state =
          ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),afterStack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins)),
              .heap (.read token offset (heap.heap.payload object))],11⟩
      else
        LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst bodyMeanings) (first.subst meanings) ∧
        ReaderInventory heap (readerFrames afterStack) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨heap,.evaluate (bodyCode.child (no.rename Nat.succ)),afterStack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))],6⟩ := by
  obtain ⟨outside,reader,mode,remaining,sourceTyped,readTyped,readProjected,restProjected,readZero,restOne,same⟩ :=
    checked_dynamic_reader_source (shape ▸ checked)
  have originalSource : LoanTyping.HasType env loans code.context false code.term outside := by
    simpa only [shape] using sourceTyped
  have sourceClosing : LoanClosingTyped env loans false code meanings (Term.subst meanings outside) :=
    ⟨context.closing,outside,originalSource,.refl _⟩
  have aligned : CodeAligned code := initial_run_closure_captures term fuel _ returned
  obtain ⟨result,leftTyped,rightTyped,yesTyped,noTyped⟩ := readTyped.ifLt_inputs
  obtain ⟨offset,indexStored,indexMeaning⟩ := checked_natural_slot history context aligned leftTyped
  obtain ⟨count,lengthStored,lengthMeaning⟩ := checked_natural_slot history context aligned rightTyped
  have physical := checked_reader_length history readTyped sizes stored lengthMeaning
  obtain ⟨valueType,outlived,bodyTyped,bodyContext⟩ := value_reader_closing history sourceClosing context shape token
  have bodySizes := sizes.enter_reference domain (dynamicReferenceReader index length no)
    (.borrow ((Term.var owner).subst code.origins)) (.borrow ((Term.var owner).subst meanings)) token
  have readers := initial_run_readers_live term fuel
  rw [stackShape] at readers
  have leased := readers _ List.mem_cons_self token object (some (code.context.length-owner)) rfl
  have live := (initial_run_heap_valid term fuel).leased token object leased |>.2
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,
        .returned (.closure false domain (dynamicReferenceReader index length no) code.context code.origins code.values),
        .lendReader token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
          readerOrigin continuation :: rest⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  refine ⟨outside,offset,count,reader,mode,remaining,sourceClosing,indexStored,lengthStored,indexMeaning,lengthMeaning,
    readProjected,restProjected,readZero,restOne,same,physical,leased,live,bodyContext,bodySizes,?_⟩
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte]
    have originalType : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
      simpa only [Term.subst,substArgs] using
        (readTyped.ifLt_index_result history.wellFormed).substitution meanings history.wellFormed.closed
    have valueTyped := (initial_run_decoded_integer_typed (env := env) term fuel object).convert originalType
    have executed := dynamic_reference_eleven_steps (run fuel (initial term)).state.heap code domain no index length offset count
      token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins) readerOrigin continuation rest
      indexStored lengthStored leased physical compared
    dsimp only at executed
    rw [← stateShape] at executed
    have inventory := run_reader_inventory (state := (run fuel (initial term)).state)
      (initial_run_heap_valid term fuel) (initial_reader_inventory term fuel) 11
    rw [executed] at inventory
    exact ⟨valueTyped,inventory,executed⟩
  · simp only [compared,↓reduceIte]
    have noClosed := noTyped.ghostSubstitution history.wellFormed context.closing
    have scalarResult := (LoanTyping.HasType.ifLt leftTyped rightTyped yesTyped noTyped).unique history.wellFormed readTyped
    have noOriginal := noClosed.convert (scalarResult.substitution meanings history.wellFormed.closed)
    have noResult : LoanTyping.HasType env [] [] true
        ((no.rename Nat.succ).subst (consValues (.borrow ((Term.var owner).subst meanings)) meanings)) (first.subst meanings) := by
      simpa only [shift_subst_consValues] using noOriginal
    have executed := dynamic_reference_else_six_steps (run fuel (initial term)).state.heap code domain no index length offset count
      token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins) readerOrigin continuation rest
      indexStored lengthStored compared
    dsimp only at executed
    rw [← stateShape] at executed
    have inventory := run_reader_inventory (state := (run fuel (initial term)).state)
      (initial_run_heap_valid term fuel) (initial_reader_inventory term fuel) 6
    rw [executed] at inventory
    exact ⟨noResult,inventory,executed⟩

end Jihoo.NativeKernel.Environment.BindingMachine
