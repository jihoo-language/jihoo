import Jihoo.NativeBindingMachineAllocatedDynamicRelease
import Jihoo.NativeBindingMachineLiteralElseRelease

/-! Source-constructed allocation/reader entry composed with both guarded
outcomes. No successful else execution or intermediate value typing is assumed. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {bodyControl : Jihoo.Quantity.Control}

theorem reachable_allocated_literal_release (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate allocationCode)
    (allocationTyped : LoanClosingTyped env allocationLoans false allocationCode allocationMeanings argumentType)
    (allocationContext : ValueContext env allocationCode allocationMeanings)
    (allocationShape : allocationCode.term = .alloc (.var countIndex) (.var fillIndex))
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex),ctx,origins,captured⟩
      meanings (.pi false argumentType result))
    (functionContext : ValueContext env
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex),ctx,origins,captured⟩ meanings)
    (functionSizes : OwnerSizes env (run fuel (initial term)).state.heap
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex),ctx,origins,captured⟩ meanings)
    (functionSlots : LoanSlots
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex),ctx,origins,captured⟩ loans stack)
    (entered : Loans.Entered ctx.length loans)
    (checkedBody : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+4) env loans (⟨ownerDomain,false⟩ :: ctx)
      (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex) = some bodyControl)
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = 2)
    (stackShape : (run fuel (initial term)).state.stack = .argument
      (.closure false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex) ctx origins captured)
      argumentOrigin :: stack) :
    ∃ count fill, allocationMeanings countIndex = .natural count ∧ allocationMeanings fillIndex = .integer fill ∧
      let heap := (run fuel (initial term)).state.heap
      let object := heap.heap.nextObject
      let token := heap.heap.nextLease
      let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
      let lent := SizedBufferHeap.lend allocated object
      let released := SizedBufferHeap.release (SizedBufferHeap.close lent token) object
      let sourceBody := allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex
      let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
      if count*8+8 < 2^64 then
        ∃ offset, bodyMeanings index = .natural offset ∧ bodyMeanings length = .natural count ∧
          let value := if offset < count then fill else fallback
          let ticks := if offset < count then 30 else 26
          LoanTyping.HasType env [] [] true (.integer value)
            (result.subst (single (.alloc (.natural count) (.integer fill)))) ∧
          released.heap.live object = false ∧ SizedBufferHeap.Valid released ∧ ReaderInventory released (readerFrames stack) ∧
          (run ticks (run fuel (initial term)).state).state = ⟨released,.returned (.integer value),stack⟩ ∧
          eventsHeap (run ticks (run fuel (initial term)).state).events =
            [.alloc object count (encodeInteger fill),.beginLease token object] ++
              (if offset < count then [.read token offset (encodeInteger fill)] else []) ++ [.close token,.free object]
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,.argument (.closure false ownerDomain sourceBody ctx origins captured) argumentOrigin :: stack⟩,[],5⟩ := by
  have bodyProjected := checkedBody
  obtain ⟨count,fill,countMeaning,fillMeaning,allocatedResult⟩ := reachable_allocated_argument_sizes term fuel history
    evaluating allocationTyped allocationContext allocationShape functionTyped functionContext functionSizes stackShape
  have canonicalTyped : LoanTyping.HasType env [] [] true (.alloc (.natural count) (.integer fill)) argumentType := by
    simpa only [allocationShape,Term.subst,substArgs,Op.binders,liftSub,countMeaning,fillMeaning] using allocationTyped.closed history
  have fillBound := canonicalTyped.alloc_inputs.2.integer_bound
  refine ⟨count,fill,countMeaning,fillMeaning,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at allocatedResult ⊢
    obtain ⟨bodySizes,bodyContext,bodyTyped,allocatedRun⟩ := allocatedResult
    let heap := (run fuel (initial term)).state.heap
    let object := heap.heap.nextObject
    let token := heap.heap.nextLease
    let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
    let lent := SizedBufferHeap.lend allocated object
    let sourceBody := allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex
    let bodyCode := enter false ownerDomain sourceBody ctx origins captured argumentOrigin (some (.owner object))
    let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
    have live : allocated.heap.live object = true := by
      simp only [allocated,object,SizedBufferHeap.allocate,HeapLeases.put,ite_true]
    have nextRun := lend_reader_four_steps allocated bodyCode object readerDomain
      (dynamicReferenceReader index length (.integer fallback)) (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))
      stack rfl rfl live
    have tokenSame : allocated.heap.nextLease = token := rfl
    rw [tokenSame] at nextRun
    have ten := run_add 6 4 (run fuel (initial term)).state
    dsimp only at ten
    rw [allocatedRun] at ten
    dsimp only at ten
    rw [nextRun] at ten
    have globalPrefix := run_add fuel 10 (initial term)
    dsimp only at globalPrefix
    rw [ten] at globalPrefix
    have reachedState : (run (fuel+10) (initial term)).state =
        ⟨lent,.returned (.closure false readerDomain (dynamicReferenceReader index length (.integer fallback))
          bodyCode.context bodyCode.origins bodyCode.values),
          .lendReader token object (some bodyCode.context.length) ((Term.var 0).subst bodyCode.origins)
            (bodyCode.child (.lam false readerDomain (dynamicReferenceReader index length (.integer fallback)))).origin
            (bodyCode.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack⟩ :=
      congrArg (fun result => result.state) globalPrefix
    have reachedHeap := congrArg State.heap reachedState
    have lentSizes : OwnerSizes env lent bodyCode bodyMeanings := bodySizes.steps (.cons (.beginLease live) .nil)
    have laterSizes : OwnerSizes env (run (fuel+10) (initial term)).state.heap bodyCode bodyMeanings := by
      rw [reachedHeap]
      exact lentSizes
    have bodySlots : LoanSlots bodyCode loans stack :=
      functionSlots.enter entered false ownerDomain sourceBody argumentOrigin (some (.owner object))
    have bodyEntered : Loans.Entered bodyCode.context.length loans := by
      intro frame member
      have previous := entered frame member
      change _ ≤ ctx.length+1
      omega
    have checkedBody : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+4) env loans bodyCode.context bodyCode.term = some bodyControl :=
      bodyProjected
    have cycle := reachable_raw_fresh_literal_else_release (resourceFuel := resourceFuel+1) (owner := 0) term fuel (fuel+10) bodyCode
      history checkedBody rfl bodyContext laterSizes bodySlots bodyEntered rfl selectedAlias rfl stackShape
      (congrArg State.control reachedState) (by simpa only [Nat.sub_zero] using congrArg State.stack reachedState)
    dsimp only at cycle
    rw [reachedHeap] at cycle
    obtain ⟨outside,offset,observedCount,inferred,indexMeaning,lengthMeaning,physical,guarded,dead,valueTyped,inventory,valid,executed⟩ := cycle
    have physicalCount : lent.length object = count := SizedBufferHeap.allocation_length (v := encodeInteger fill)
    have sameCount : observedCount = count := physical.symm.trans physicalCount
    rw [sameCount] at lengthMeaning valueTyped executed
    have payload : lent.heap.payload object = encodeInteger fill := by
      simp only [lent,allocated,object,SizedBufferHeap.lend,SizedBufferHeap.allocate,HeapLeases.put,ite_true]
    have readFill : decodeInteger (lent.heap.payload object) = fill := by
      rw [payload]
      exact encode_decode_integer fillBound
    rw [readFill] at valueTyped executed
    obtain ⟨inferredClosing,inferredLocal,inferredSource,inferredConverted⟩ := inferred
    obtain ⟨declaredClosing,declaredLocal,declaredSource,declaredConverted⟩ := bodyTyped
    have targetConverted := inferredConverted.symm.trans
      (((inferredSource.unique history.wellFormed declaredSource).substitution bodyMeanings
        history.wellFormed.closed).trans declaredConverted)
    have targetType := valueTyped.convert targetConverted
    refine ⟨offset,indexMeaning,lengthMeaning,targetType,dead,valid,inventory,?_,?_⟩
    all_goals
      have composed := run_add 10 (if offset < count then 20 else 16) (run fuel (initial term)).state
      dsimp only at composed
      rw [ten] at composed
      dsimp only at composed
      rw [reachedState] at executed
      rw [executed] at composed
      by_cases compared : offset < count
      · simp only [compared,↓reduceIte] at composed ⊢
        first
        | exact congrArg (fun result => result.state) composed
        | simpa only [eventsHeap,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
            List.cons_append,List.nil_append,payload] using congrArg (fun result => eventsHeap result.events) composed
      · simp only [compared,↓reduceIte] at composed ⊢
        first
        | exact congrArg (fun result => result.state) composed
        | simpa only [eventsHeap,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
            List.cons_append,List.nil_append] using congrArg (fun result => eventsHeap result.events) composed
  · simpa only [fits,↓reduceIte] using allocatedResult

end Jihoo.NativeKernel.Environment.BindingMachine
