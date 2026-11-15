import Jihoo.NativeBindingMachineAllocatedDynamicRelease

/-! One original call judgment/resource query supplies the function, argument
and exact body receipt. The actual three-step call prefix is constructed;
no independent component typing or pending-call success oracle is assumed. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- Complete call inversion fixes the actual lambda erasure flag and retains
its original dependent result conversion under the value closing. -/
theorem LoanClosingTyped.lambda_call_inputs
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .app (.lam false domain body) argument) :
    ∃ argumentType result,
      LoanClosingTyped env loans false (code.child (.lam false domain body)) meanings (.pi false argumentType result) ∧
      LoanClosingTyped env loans false (code.child argument) meanings argumentType ∧
      LoanTyping.Conversion.Conv env (result.subst (single (argument.subst meanings))) type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨erased,argumentType,result,functionTyped,argumentTyped,allowed,applicationConverted⟩ := source.appView
  obtain ⟨sort,bodyType,binder,bodyTyped,functionConverted⟩ := functionTyped.lamView
  have flag := (functionConverted.pi_injective history.wellFormed.admissible).1
  subst erased
  refine ⟨argumentType.subst meanings,result.subst (liftSubOne meanings),
    ⟨closing,.pi false argumentType result,functionTyped,?_⟩,
    ⟨closing,argumentType,argumentTyped,.refl _⟩,?_⟩
  · simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (show LoanTyping.Conversion.Conv env
        (.pi false (argumentType.subst meanings) (result.subst (liftSubOne meanings)))
        (.pi false (argumentType.subst meanings) (result.subst (liftSubOne meanings))) from .refl _)
  · simpa only [Term.subst_instantiate] using
      (applicationConverted.substitution meanings history.wellFormed.closed).trans converted

private theorem literal_call_three_steps (heap : SizedBufferHeap.State) (code : Code)
    (domain body argument : Term) (stack : List Frame)
    (shape : code.term = .app (.lam false domain body) argument) :
    run 3 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨heap,.evaluate (code.child argument),
        .argument (.closure false domain body code.context code.origins code.values) (code.child argument).origin :: stack⟩,[],3⟩ := by
  simp only [run,step,action,evaluateAction,shape,Code.child,returnAction,execute,Option.map_some]
  rfl

/-- The original full call supplies all component source/resource judgments.
Successful guarded reading returns the actual fill at the EXACT input closed
call type, rather than only a separately chosen function-signature instance. -/
theorem reachable_call_dynamic_release (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+5) env loans code.context code.term = some control)
    (shape : code.term = .app
      (.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex))
      (.alloc (.var countIndex) (.var fillIndex)))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (slots : LoanSlots code loans (run fuel (initial term)).state.stack)
    (entered : Loans.Entered code.context.length loans)
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = 2) :
    ∃ count fill, meanings countIndex = .natural count ∧ meanings fillIndex = .integer fill ∧
      let heap := (run fuel (initial term)).state.heap
      let stack := (run fuel (initial term)).state.stack
      let object := heap.heap.nextObject
      let token := heap.heap.nextLease
      let argument := Term.alloc (.var countIndex) (.var fillIndex)
      let argumentOrigin := (code.child argument).origin
      let sourceBody := allocatedDynamicBody readerDomain first again no index length releaseIndex
      let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
      let lent := SizedBufferHeap.lend allocated object
      let released := SizedBufferHeap.release (SizedBufferHeap.close lent token) object
      let bodyCode := enter false ownerDomain sourceBody code.context code.origins code.values argumentOrigin (some (.owner object))
      let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
      let ownerOrigin := (Term.var 0).subst bodyCode.origins
      let readerBody := dynamicReferenceReader index length no
      let readerCode := enter false readerDomain readerBody bodyCode.context bodyCode.origins bodyCode.values
        (.borrow ownerOrigin) (some (.reference token))
      let readerMeanings := consValues (.borrow ((Term.var 0).subst bodyMeanings)) bodyMeanings
      let continuation := bodyCode.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))
      let finishStack := .lendFinish token object (some bodyCode.context.length) ownerOrigin readerCode.origin continuation :: stack
      if count*8+8 < 2^64 then
        ∃ offset, bodyMeanings index = .natural offset ∧ bodyMeanings length = .natural count ∧
          if offset < count then
            LoanTyping.HasType env [] [] true (.integer fill) type ∧
            released.heap.live object = false ∧ SizedBufferHeap.Valid released ∧ ReaderInventory released (readerFrames stack) ∧
            (run 33 (run fuel (initial term)).state).state = ⟨released,.returned (.integer fill),stack⟩ ∧
            eventsHeap (run 33 (run fuel (initial term)).state).events =
              [.alloc object count (encodeInteger fill),.beginLease token object,
                .read token offset (encodeInteger fill),.close token,.free object]
          else
            LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst readerMeanings) (first.subst bodyMeanings) ∧
            ValueContext env (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
            OwnerSizes env lent (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
            ReaderInventory lent (readerFrames finishStack) ∧
            (run 19 (run fuel (initial term)).state).state =
              ⟨lent,.evaluate (readerCode.child (no.rename Nat.succ)),finishStack⟩ ∧
            eventsHeap (run 19 (run fuel (initial term)).state).events =
              [.alloc object count (encodeInteger fill),.beginLease token object]
      else run 8 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,
          .argument (.closure false ownerDomain sourceBody code.context code.origins code.values) argumentOrigin :: stack⟩,[],8⟩ := by
  obtain ⟨argumentType,result,functionTyped,argumentTyped,resultConverted⟩ := typed.lambda_call_inputs history shape
  obtain ⟨bodyControl,bodyProjected⟩ := LoanTyping.ResourceQuantity.projectRaw_single_lambda_call_body
    (shape ▸ LoanTyping.ResourceQuantity.project_origin checked)
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate code,(run fuel (initial term)).state.stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have three := literal_call_three_steps (run fuel (initial term)).state.heap code ownerDomain
    (allocatedDynamicBody readerDomain first again no index length releaseIndex) (.alloc (.var countIndex) (.var fillIndex))
    (run fuel (initial term)).state.stack shape
  rw [← stateShape] at three
  have globalPrefix := run_add fuel 3 (initial term)
  dsimp only at globalPrefix
  rw [three] at globalPrefix
  have reachedState : (run (fuel+3) (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate (code.child (.alloc (.var countIndex) (.var fillIndex))),
        .argument (.closure false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex)
          code.context code.origins code.values) (code.child (.alloc (.var countIndex) (.var fillIndex))).origin ::
          (run fuel (initial term)).state.stack⟩ := congrArg (fun result => result.state) globalPrefix
  have reachedHeap := congrArg State.heap reachedState
  have laterSizes : OwnerSizes env (run (fuel+3) (initial term)).state.heap
      (code.child (.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex))) meanings := by
    rw [reachedHeap]
    exact sizes.child _
  have result := reachable_allocated_dynamic_release_body term (fuel+3) history (congrArg State.control reachedState)
    argumentTyped (context.child _) rfl functionTyped (context.child _) laterSizes (slots.child _) entered bodyProjected
    selectedAlias (congrArg State.stack reachedState)
  dsimp only at result
  rw [reachedHeap] at result
  obtain ⟨count,fill,countMeaning,fillMeaning,result⟩ := result
  have canonical : (Term.alloc (.var countIndex) (.var fillIndex)).subst meanings = .alloc (.natural count) (.integer fill) := by
    simp only [Term.subst,substArgs,Op.binders,liftSub,countMeaning,fillMeaning]
  rw [canonical] at resultConverted
  refine ⟨count,fill,countMeaning,fillMeaning,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at result ⊢
    obtain ⟨offset,indexMeaning,lengthMeaning,result⟩ := result
    refine ⟨offset,indexMeaning,lengthMeaning,?_⟩
    by_cases compared : offset < count
    · simp only [compared,↓reduceIte] at result ⊢
      obtain ⟨valueTyped,dead,valid,inventory,executed⟩ := result
      have composed := run_add 3 30 (run fuel (initial term)).state
      dsimp only at composed
      rw [three] at composed
      dsimp only at composed
      rw [reachedState] at executed
      rw [executed] at composed
      refine ⟨valueTyped.convert resultConverted,dead,valid,inventory,?_,?_⟩
      · exact congrArg (fun result => result.state) composed
      · simpa only [eventsHeap,List.nil_append,List.filterMap_cons,List.filterMap_nil] using
          congrArg (fun result => eventsHeap result.events) composed
    · simp only [compared,↓reduceIte] at result ⊢
      obtain ⟨noTyped,noContext,noSizes,inventory,executed⟩ := result
      have composed := run_add 3 16 (run fuel (initial term)).state
      dsimp only at composed
      rw [three] at composed
      dsimp only at composed
      rw [reachedState] at executed
      rw [executed] at composed
      refine ⟨noTyped,noContext,noSizes,inventory,?_,?_⟩
      · exact congrArg (fun result => result.state) composed
      · simpa only [eventsHeap,List.nil_append,List.filterMap_cons,List.filterMap_nil] using
          congrArg (fun result => eventsHeap result.events) composed
  · simp only [fits,↓reduceIte] at result ⊢
    have composed := run_add 3 5 (run fuel (initial term)).state
    dsimp only at composed
    rw [three] at composed
    dsimp only at composed
    rw [reachedState] at result
    rw [result] at composed
    exact composed

end Jihoo.NativeKernel.Environment.BindingMachine
