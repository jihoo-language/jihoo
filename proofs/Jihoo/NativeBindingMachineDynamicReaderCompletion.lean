import Jihoo.NativeBindingMachineCheckedDynamicReader

/-! The authentic resource receipt drives a captured-number reference reader
through its guarded read, lease close and both actual continuation bindings.
The original full source/resource judgment is reconstructed, not supplied as
an arbitrary callback/output or execution-success premise. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- A true comparison has sixteen constructed activation/read/close/handoff
transitions at the original source result type. A false comparison retains
source-typed else entry with its reference and outer readers alive. -/
theorem reachable_raw_dynamic_reader_completion (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context code.term = some control)
    (shape : code.term = .lend (.var owner) (.lam false domain (dynamicReferenceReader index length no))
      (.lam false first (.lam false again body)))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (returned : (run fuel (initial term)).state.control = .returned
      (.closure false domain (dynamicReferenceReader index length no) code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
        readerOrigin (code.child (.lam false first (.lam false again body))) :: stack) :
    ∃ outside offset count reader mode remaining,
      LoanClosingTyped env loans false code meanings (Term.subst meanings outside) ∧
      meanings index = .natural offset ∧ meanings length = .natural count ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter code.context.length owner loans) code.context
        (.ifLt (.var index) (.var length) (dynamicRead owner index) no) = some reader ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans (⟨first,false⟩ :: code.context)
        (body.subst (single ((Term.var owner).rename Nat.succ))) = some remaining ∧
      reader.demand owner = some 0 ∧ (Jihoo.Quantity.Control.scope mode remaining).demand owner = some 1 ∧
      control = .seq reader (.scope mode remaining) ∧
      let heap := (run fuel (initial term)).state.heap
      let readerBody := dynamicReferenceReader index length no
      let readerCode := enter false domain readerBody code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
      let readerMeanings := consValues (.borrow ((Term.var owner).subst meanings)) meanings
      let finishStack := .lendFinish token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerCode.origin (code.child (.lam false first (.lam false again body))) :: stack
      heap.length object = count ∧
      if offset < count then
        let closed := SizedBufferHeap.close heap token
        let result := Value.integer (decodeInteger (heap.heap.payload object))
        let next := restoredContinuation code first again body ((Term.var owner).subst code.origins) readerCode.origin object result
        let nextMeanings := consValues ((Term.var owner).subst meanings)
          (consValues (.integer (decodeInteger (heap.heap.payload object))) meanings)
        run 16 (run fuel (initial term)).state =
          ⟨⟨closed,.evaluate next,stack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins)),
              .heap (.read token offset (heap.heap.payload object)),.heap (.close token),
              .activate false (.lam false again body) readerCode.origin,
              .activate false body ((Term.var owner).subst code.origins)],16⟩ ∧
        ValueContext env next nextMeanings ∧ OwnerSizes env closed next nextMeanings ∧
        LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) (Term.subst meanings outside) ∧
        LoanSlots next loans stack ∧ ReaderInventory closed (readerFrames stack) ∧ closed.heap.live object = true ∧
        (freeGuard closed object = true ↔ ¬ ObjectReader object stack) ∧
        (∀ selected, next.values[selected]? = (some result :: code.values)[Jihoo.Quantity.openOwner (owner+1) selected]?)
      else
        LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst readerMeanings) (first.subst meanings) ∧
        ValueContext env (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        OwnerSizes env heap (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        ReaderInventory heap (readerFrames finishStack) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨heap,.evaluate (readerCode.child (no.rename Nat.succ)),finishStack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))],6⟩ := by
  obtain ⟨outside,offset,count,reader,mode,remaining,sourceClosing,indexStored,lengthStored,indexMeaning,lengthMeaning,
    readProjected,restProjected,readZero,restOne,same,physical,leased,live,bodyContext,bodySizes,selected⟩ :=
    reachable_raw_dynamic_reference_reader term fuel code history checked shape context sizes stored returned stackShape
  refine ⟨outside,offset,count,reader,mode,remaining,sourceClosing,indexMeaning,lengthMeaning,
    readProjected,restProjected,readZero,restOne,same,physical,?_⟩
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte] at selected ⊢
    obtain ⟨valueTyped,inventory,executed⟩ := selected
    have reached := run_add fuel 11 (initial term)
    dsimp only at reached
    rw [executed] at reached
    have reachedState : (run (fuel+11) (initial term)).state =
        ⟨(run fuel (initial term)).state.heap,
          .returned (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))),
          .lendFinish token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
            (enter false domain (dynamicReferenceReader index length no) code.context code.origins code.values
              (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
            (code.child (.lam false first (.lam false again body))) :: stack⟩ :=
      congrArg (fun result => result.state) reached
    have reachedHeap := congrArg State.heap reachedState
    have laterSizes : OwnerSizes env (run (fuel+11) (initial term)).state.heap code meanings := by
      rw [reachedHeap]
      exact sizes
    have scalar : LoanTyping.ScalarReadShape (dynamicReferenceReader index length no) := .ifLt
    have handoff := reachable_raw_scalar_value_lend_handoff term (fuel+11) code history sourceClosing context laterSizes shape scalar
      checked stored slots entered (congrArg State.control reachedState) (congrArg State.stack reachedState)
    dsimp only at handoff
    rw [reachedHeap] at handoff
    obtain ⟨handed,nextContext,nextSizes,nextTyped,nextSlots,remainingReaders,oldLive,guard,aliases,resource⟩ := handoff
    have composed := run_add 11 5 (run fuel (initial term)).state
    dsimp only at composed
    rw [executed] at composed
    dsimp only at composed
    rw [reachedState] at handed
    rw [handed] at composed
    exact ⟨composed,nextContext,nextSizes,nextTyped,nextSlots,remainingReaders,oldLive,guard,aliases⟩
  · simp only [compared,↓reduceIte] at selected ⊢
    obtain ⟨noTyped,inventory,executed⟩ := selected
    exact ⟨noTyped,bodyContext.child _,bodySizes.child _,inventory,executed⟩

/-- The full outer resource query supplies its exact internal receipt. -/
theorem reachable_checked_dynamic_reader_completion (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (shape : code.term = .lend (.var owner) (.lam false domain (dynamicReferenceReader index length no))
      (.lam false first (.lam false again body)))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (returned : (run fuel (initial term)).state.control = .returned
      (.closure false domain (dynamicReferenceReader index length no) code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
        readerOrigin (code.child (.lam false first (.lam false again body))) :: stack) :
    ∃ outside offset count reader mode remaining,
      LoanClosingTyped env loans false code meanings (Term.subst meanings outside) ∧
      meanings index = .natural offset ∧ meanings length = .natural count ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter code.context.length owner loans) code.context
        (.ifLt (.var index) (.var length) (dynamicRead owner index) no) = some reader ∧
      LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans (⟨first,false⟩ :: code.context)
        (body.subst (single ((Term.var owner).rename Nat.succ))) = some remaining ∧
      reader.demand owner = some 0 ∧ (Jihoo.Quantity.Control.scope mode remaining).demand owner = some 1 ∧
      control = .seq reader (.scope mode remaining) ∧
      let heap := (run fuel (initial term)).state.heap
      let readerBody := dynamicReferenceReader index length no
      let readerCode := enter false domain readerBody code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
      let readerMeanings := consValues (.borrow ((Term.var owner).subst meanings)) meanings
      let finishStack := .lendFinish token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerCode.origin (code.child (.lam false first (.lam false again body))) :: stack
      heap.length object = count ∧
      if offset < count then
        let closed := SizedBufferHeap.close heap token
        let result := Value.integer (decodeInteger (heap.heap.payload object))
        let next := restoredContinuation code first again body ((Term.var owner).subst code.origins) readerCode.origin object result
        let nextMeanings := consValues ((Term.var owner).subst meanings)
          (consValues (.integer (decodeInteger (heap.heap.payload object))) meanings)
        run 16 (run fuel (initial term)).state =
          ⟨⟨closed,.evaluate next,stack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins)),
              .heap (.read token offset (heap.heap.payload object)),.heap (.close token),
              .activate false (.lam false again body) readerCode.origin,
              .activate false body ((Term.var owner).subst code.origins)],16⟩ ∧
        ValueContext env next nextMeanings ∧ OwnerSizes env closed next nextMeanings ∧
        LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) (Term.subst meanings outside) ∧
        LoanSlots next loans stack ∧ ReaderInventory closed (readerFrames stack) ∧ closed.heap.live object = true ∧
        (freeGuard closed object = true ↔ ¬ ObjectReader object stack) ∧
        (∀ selected, next.values[selected]? = (some result :: code.values)[Jihoo.Quantity.openOwner (owner+1) selected]?)
      else
        LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst readerMeanings) (first.subst meanings) ∧
        ValueContext env (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        OwnerSizes env heap (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        ReaderInventory heap (readerFrames finishStack) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨heap,.evaluate (readerCode.child (no.rename Nat.succ)),finishStack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))],6⟩ := by
  exact reachable_raw_dynamic_reader_completion term fuel code history (LoanTyping.ResourceQuantity.project_origin checked) shape
    context sizes slots entered stored returned stackShape

end Jihoo.NativeKernel.Environment.BindingMachine
