import Jihoo.NativeBindingMachineFreshDynamicRelease

/-! Original function resource checking supplies the exact internal Lend
receipt. Actual allocation constructs owner/value/size contexts and its reader
frame; no birth/current-reader or output/success certificate is supplied. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {functionControl bodyControl : Jihoo.Quantity.Control}

def allocatedDynamicBody (readerDomain first again no : Term) (index length releaseIndex : Nat) : Term :=
  .lend (.var 0) (.lam false readerDomain (dynamicReferenceReader index length no))
    (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))

set_option linter.unusedSimpArgs false in
private theorem lend_reader_four_steps (heap : SizedBufferHeap.State) (code : Code)
    (object : Nat) (domain readerBody continuation : Term) (stack : List Frame)
    (shape : code.term = .lend (.var 0) (.lam false domain readerBody) continuation)
    (stored : code.values[0]? = some (some (.owner object))) (live : heap.heap.live object = true) :
    run 4 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨SizedBufferHeap.lend heap object,.returned (.closure false domain readerBody code.context code.origins code.values),
        .lendReader heap.heap.nextLease object (some code.context.length) ((Term.var 0).subst code.origins)
          (code.child (.lam false domain readerBody)).origin (code.child continuation) :: stack⟩,
        [.heap (.beginLease heap.heap.nextLease object)],4⟩ := by
  simp only [run,step,action,evaluateAction,returnAction,execute,shape,stored,live,Code.child,
    Term.subst,Nat.sub_zero,↓reduceIte,Option.map_some]
  rfl

/-- Thirty actual transitions construct the allocation, argument binding,
Lend frame, guarded reference read, close, alias release and actual fill return.
The original function resource query supplies the body receipt. All later
source contexts and birth/frame associations are outputs of this proof. -/
theorem reachable_allocated_dynamic_release_body (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate allocationCode)
    (allocationTyped : LoanClosingTyped env allocationLoans false allocationCode allocationMeanings argumentType)
    (allocationContext : ValueContext env allocationCode allocationMeanings)
    (allocationShape : allocationCode.term = .alloc (.var countIndex) (.var fillIndex))
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩
      meanings (.pi false argumentType result))
    (functionContext : ValueContext env
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩ meanings)
    (functionSizes : OwnerSizes env (run fuel (initial term)).state.heap
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩ meanings)
    (functionSlots : LoanSlots
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩ loans stack)
    (entered : Loans.Entered ctx.length loans)
    (checkedBody : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+4) env loans (⟨ownerDomain,false⟩ :: ctx)
      (allocatedDynamicBody readerDomain first again no index length releaseIndex) = some bodyControl)
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = 2)
    (stackShape : (run fuel (initial term)).state.stack = .argument
      (.closure false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex) ctx origins captured)
      argumentOrigin :: stack) :
    ∃ count fill, allocationMeanings countIndex = .natural count ∧ allocationMeanings fillIndex = .integer fill ∧
      let heap := (run fuel (initial term)).state.heap
      let object := heap.heap.nextObject
      let token := heap.heap.nextLease
      let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
      let lent := SizedBufferHeap.lend allocated object
      let released := SizedBufferHeap.release (SizedBufferHeap.close lent token) object
      let sourceBody := allocatedDynamicBody readerDomain first again no index length releaseIndex
      let bodyCode := enter false ownerDomain sourceBody ctx origins captured argumentOrigin (some (.owner object))
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
            LoanTyping.HasType env [] [] true (.integer fill)
              (result.subst (single (.alloc (.natural count) (.integer fill)))) ∧
            released.heap.live object = false ∧ SizedBufferHeap.Valid released ∧ ReaderInventory released (readerFrames stack) ∧
            run 30 (run fuel (initial term)).state =
              ⟨⟨released,.returned (.integer fill),stack⟩,
                [.heap (.alloc object count (encodeInteger fill)),.activate false sourceBody argumentOrigin,
                  .heap (.beginLease token object),.activate false readerBody (.borrow ownerOrigin),
                  .heap (.read token offset (encodeInteger fill)),.heap (.close token),
                  .activate false (.lam false again (.free (.var releaseIndex) (.var 1))) readerCode.origin,
                  .activate false (.free (.var releaseIndex) (.var 1)) ownerOrigin,.heap (.free object)],30⟩
          else
            LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst readerMeanings) (first.subst bodyMeanings) ∧
            ValueContext env (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
            OwnerSizes env lent (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
            ReaderInventory lent (readerFrames finishStack) ∧
            run 16 (run fuel (initial term)).state =
              ⟨⟨lent,.evaluate (readerCode.child (no.rename Nat.succ)),finishStack⟩,
                [.heap (.alloc object count (encodeInteger fill)),.activate false sourceBody argumentOrigin,
                  .heap (.beginLease token object),.activate false readerBody (.borrow ownerOrigin)],16⟩
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
    let sourceBody := allocatedDynamicBody readerDomain first again no index length releaseIndex
    let bodyCode := enter false ownerDomain sourceBody ctx origins captured argumentOrigin (some (.owner object))
    let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
    have live : allocated.heap.live object = true := by
      simp only [allocated,object,SizedBufferHeap.allocate,HeapLeases.put,ite_true]
    have nextRun := lend_reader_four_steps allocated bodyCode object readerDomain
      (dynamicReferenceReader index length no) (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))
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
        ⟨lent,.returned (.closure false readerDomain (dynamicReferenceReader index length no)
          bodyCode.context bodyCode.origins bodyCode.values),
          .lendReader token object (some bodyCode.context.length) ((Term.var 0).subst bodyCode.origins)
            (bodyCode.child (.lam false readerDomain (dynamicReferenceReader index length no))).origin
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
    have cycle := reachable_raw_fresh_dynamic_reader_release (resourceFuel := resourceFuel+1) (owner := 0) term fuel (fuel+10) bodyCode
      history checkedBody rfl bodyContext laterSizes bodySlots bodyEntered rfl selectedAlias rfl stackShape
      (congrArg State.control reachedState) (by simpa only [Nat.sub_zero] using congrArg State.stack reachedState)
    dsimp only at cycle
    rw [reachedHeap] at cycle
    obtain ⟨outside,offset,observedCount,inferred,indexMeaning,lengthMeaning,physical,cycle⟩ := cycle
    have physicalCount : lent.length object = count := SizedBufferHeap.allocation_length (v := encodeInteger fill)
    have sameCount : observedCount = count := physical.symm.trans physicalCount
    rw [sameCount] at lengthMeaning cycle
    have payload : lent.heap.payload object = encodeInteger fill := by
      simp only [lent,allocated,object,SizedBufferHeap.lend,SizedBufferHeap.allocate,HeapLeases.put,ite_true]
    have readFill : decodeInteger (lent.heap.payload object) = fill := by
      rw [payload]
      exact encode_decode_integer fillBound
    refine ⟨offset,indexMeaning,lengthMeaning,?_⟩
    by_cases compared : offset < count
    · simp only [compared,↓reduceIte] at cycle ⊢
      obtain ⟨guarded,dead,valueTyped,exitSizes,inventory,valid,twenty,residual⟩ := cycle
      rw [readFill] at valueTyped twenty
      obtain ⟨inferredClosing,inferredLocal,inferredSource,inferredConverted⟩ := inferred
      obtain ⟨declaredClosing,declaredLocal,declaredSource,declaredConverted⟩ := bodyTyped
      have targetConverted := inferredConverted.symm.trans
        (((inferredSource.unique history.wellFormed declaredSource).substitution bodyMeanings
          history.wellFormed.closed).trans declaredConverted)
      have targetType := valueTyped.convert targetConverted
      have composed := run_add 10 20 (run fuel (initial term)).state
      dsimp only at composed
      rw [ten] at composed
      dsimp only at composed
      rw [reachedState] at twenty
      rw [twenty] at composed
      refine ⟨targetType,dead,valid,inventory,?_⟩
      simpa only [payload,List.cons_append,List.nil_append,Nat.reduceAdd] using composed
    · simp only [compared,↓reduceIte] at cycle ⊢
      obtain ⟨noTyped,noContext,noSizes,inventory,six⟩ := cycle
      have composed := run_add 10 6 (run fuel (initial term)).state
      dsimp only at composed
      rw [ten] at composed
      dsimp only at composed
      rw [reachedState] at six
      rw [six] at composed
      exact ⟨noTyped,noContext,noSizes,inventory,composed⟩
  · simpa only [fits,↓reduceIte] using allocatedResult

/-- The original full function query supplies the internal receipt. -/
theorem reachable_allocated_dynamic_release (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate allocationCode)
    (allocationTyped : LoanClosingTyped env allocationLoans false allocationCode allocationMeanings argumentType)
    (allocationContext : ValueContext env allocationCode allocationMeanings)
    (allocationShape : allocationCode.term = .alloc (.var countIndex) (.var fillIndex))
    (functionTyped : LoanClosingTyped env loans false
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩
      meanings (.pi false argumentType result))
    (functionContext : ValueContext env
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩ meanings)
    (functionSizes : OwnerSizes env (run fuel (initial term)).state.heap
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩ meanings)
    (functionSlots : LoanSlots
      ⟨.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex),ctx,origins,captured⟩ loans stack)
    (entered : Loans.Entered ctx.length loans)
    (checkedFunction : LoanTyping.ResourceQuantity.project (resourceFuel+5) env loans ctx
      (.lam false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex)) = some functionControl)
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = 2)
    (stackShape : (run fuel (initial term)).state.stack = .argument
      (.closure false ownerDomain (allocatedDynamicBody readerDomain first again no index length releaseIndex) ctx origins captured)
      argumentOrigin :: stack) :
    ∃ count fill, allocationMeanings countIndex = .natural count ∧ allocationMeanings fillIndex = .integer fill ∧
      let heap := (run fuel (initial term)).state.heap
      let object := heap.heap.nextObject
      let token := heap.heap.nextLease
      let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
      let lent := SizedBufferHeap.lend allocated object
      let released := SizedBufferHeap.release (SizedBufferHeap.close lent token) object
      let sourceBody := allocatedDynamicBody readerDomain first again no index length releaseIndex
      let bodyCode := enter false ownerDomain sourceBody ctx origins captured argumentOrigin (some (.owner object))
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
            LoanTyping.HasType env [] [] true (.integer fill)
              (result.subst (single (.alloc (.natural count) (.integer fill)))) ∧
            released.heap.live object = false ∧ SizedBufferHeap.Valid released ∧ ReaderInventory released (readerFrames stack) ∧
            run 30 (run fuel (initial term)).state =
              ⟨⟨released,.returned (.integer fill),stack⟩,
                [.heap (.alloc object count (encodeInteger fill)),.activate false sourceBody argumentOrigin,
                  .heap (.beginLease token object),.activate false readerBody (.borrow ownerOrigin),
                  .heap (.read token offset (encodeInteger fill)),.heap (.close token),
                  .activate false (.lam false again (.free (.var releaseIndex) (.var 1))) readerCode.origin,
                  .activate false (.free (.var releaseIndex) (.var 1)) ownerOrigin,.heap (.free object)],30⟩
          else
            LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst readerMeanings) (first.subst bodyMeanings) ∧
            ValueContext env (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
            OwnerSizes env lent (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
            ReaderInventory lent (readerFrames finishStack) ∧
            run 16 (run fuel (initial term)).state =
              ⟨⟨lent,.evaluate (readerCode.child (no.rename Nat.succ)),finishStack⟩,
                [.heap (.alloc object count (encodeInteger fill)),.activate false sourceBody argumentOrigin,
                  .heap (.beginLease token object),.activate false readerBody (.borrow ownerOrigin)],16⟩
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,.argument (.closure false ownerDomain sourceBody ctx origins captured) argumentOrigin :: stack⟩,[],5⟩ := by
  obtain ⟨mode,bodyControl,bodyProjected,functionProjected⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_lambda_body (LoanTyping.ResourceQuantity.project_origin checkedFunction)
  exact reachable_allocated_dynamic_release_body term fuel history evaluating allocationTyped allocationContext allocationShape
    functionTyped functionContext functionSizes functionSlots entered bodyProjected selectedAlias stackShape

end Jihoo.NativeKernel.Environment.BindingMachine
