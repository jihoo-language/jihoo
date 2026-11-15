import Jihoo.NativeBindingMachineFreshDynamicRelease

/-! Complete the no-read branch of a fresh guarded reference reader. The
literal's width comes from original source typing; exact reachable inventory
and earlier frame provenance construct close and Free, including outer readers.
No selected branch, no-reader premise or successful suffix is supplied. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

private theorem integer_one_step (heap : SizedBufferHeap.State) (code : Code) (value : Int) (stack : List Frame)
    (shape : code.term = .integer value) (bounded : ValueReduction.signed64 value) :
    run 1 ⟨heap,.evaluate code,stack⟩ = ⟨⟨heap,.returned (.integer value),stack⟩,[],1⟩ := by
  simp only [run,step,action,evaluateAction,shape,bounded,↓reduceIte,execute,Option.map_some]
  rfl

/-- Both guarded outcomes close the actual lease and release the fresh owner.
A successful read returns the heap payload in twenty transitions; a failed
comparison evaluates its original literal and returns it in sixteen. The
original result typing is constructed in both cases. -/
theorem reachable_raw_fresh_literal_else_release (term : Term) (birthFuel fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some control)
    (shape : code.term = .lend (.var owner) (.lam false domain (dynamicReferenceReader index length (.integer fallback)))
      (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1)))))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (born : object = (run birthFuel (initial term)).state.heap.heap.nextObject)
    (birthStack : (run birthFuel (initial term)).state.stack = .argument function argumentOrigin :: stack)
    (returned : (run fuel (initial term)).state.control = .returned
      (.closure false domain (dynamicReferenceReader index length (.integer fallback)) code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins) readerOrigin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack) :
    ∃ outside offset count,
      LoanClosingTyped env loans false code meanings (Term.subst meanings outside) ∧
      meanings index = .natural offset ∧ meanings length = .natural count ∧
      let heap := (run fuel (initial term)).state.heap
      let closed := SizedBufferHeap.close heap token
      let released := SizedBufferHeap.release closed object
      let value := if offset < count then decodeInteger (heap.heap.payload object) else fallback
      let ticks := if offset < count then 20 else 16
      let readerBody := dynamicReferenceReader index length (.integer fallback)
      let readerCode := enter false domain readerBody code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
      heap.length object = count ∧ freeGuard closed object = true ∧ released.heap.live object = false ∧
      LoanTyping.HasType env [] [] true (.integer value) (Term.subst meanings outside) ∧
      ReaderInventory released (readerFrames stack) ∧ SizedBufferHeap.Valid released ∧
      run ticks (run fuel (initial term)).state =
        ⟨⟨released,.returned (.integer value),stack⟩,
          [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))] ++
            (if offset < count then [.heap (.read token offset (heap.heap.payload object))] else []) ++
            [.heap (.close token),.activate false (.lam false again (.free (.var releaseIndex) (.var 1))) readerCode.origin,
              .activate false (.free (.var releaseIndex) (.var 1)) ((Term.var owner).subst code.origins),.heap (.free object)],ticks⟩ := by
  obtain ⟨outside,offset,count,sourceClosing,indexMeaning,lengthMeaning,physical,completed⟩ :=
    reachable_raw_fresh_dynamic_reader_release term birthFuel fuel code history checked shape context sizes slots entered
      stored selectedAlias born birthStack returned stackShape
  refine ⟨outside,offset,count,sourceClosing,indexMeaning,lengthMeaning,physical,?_⟩
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte] at completed ⊢
    obtain ⟨guarded,dead,valueTyped,nextSizes,inventory,valid,executed,remaining⟩ := completed
    refine ⟨guarded,dead,valueTyped,inventory,valid,?_⟩
    simpa only [List.cons_append,List.nil_append] using executed
  · simp only [compared,↓reduceIte] at completed ⊢
    obtain ⟨noTyped,noContext,noSizes,inventory,six⟩ := completed
    have literalTyped : LoanTyping.HasType env [] [] true (.integer fallback)
        (first.subst meanings) := by
      simpa only [Term.rename,renameArgs,Term.subst,substArgs] using noTyped
    have bounded := literalTyped.integer_bound
    have one := integer_one_step (run fuel (initial term)).state.heap
      ((enter false domain (dynamicReferenceReader index length (.integer fallback)) code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).child ((Term.integer fallback).rename Nat.succ))
      fallback
      (.lendFinish token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
        (enter false domain (dynamicReferenceReader index length (.integer fallback)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack)
      (by simp only [Code.child,Term.rename,renameArgs]) bounded
    have seven := run_add 6 1 (run fuel (initial term)).state
    dsimp only at seven
    rw [six] at seven
    dsimp only at seven
    rw [one] at seven
    have globalPrefix := run_add fuel 7 (initial term)
    dsimp only at globalPrefix
    rw [seven] at globalPrefix
    have reachedState := congrArg (fun result => result.state) globalPrefix
    have reachedHeap := congrArg State.heap reachedState
    have laterSizes : OwnerSizes env (run (fuel+7) (initial term)).state.heap code meanings := by
      rw [reachedHeap]
      exact sizes
    have handoff := reachable_raw_scalar_value_lend_handoff term (fuel+7) code history sourceClosing context laterSizes shape
      (.ifLt : LoanTyping.ScalarReadShape (dynamicReferenceReader index length (.integer fallback)))
      checked stored slots entered (congrArg State.control reachedState) (congrArg State.stack reachedState)
    dsimp only at handoff
    rw [reachedHeap] at handoff
    obtain ⟨handed,nextContext,nextSizes,nextTyped,nextSlots,remainingReaders,live,guard,aliases,resource⟩ := handoff
    have twelve := run_add 7 5 (run fuel (initial term)).state
    dsimp only at twelve
    rw [seven] at twelve
    dsimp only at twelve
    rw [reachedState] at handed
    rw [handed] at twelve
    have oldOwners := (initial_run_owners term birthFuel).2
    rw [birthStack] at oldOwners
    have absent : ¬ ObjectReader object stack := by
      rw [born]
      exact oldOwners.tail.no_reader_at_limit
    have guarded := guard.mpr absent
    have closedValid := run_heap_valid (state := (run fuel (initial term)).state)
      (initial_run_heap_valid term fuel) 12
    rw [twelve] at closedValid
    have freeStep := SizedBufferHeap.Step.free live (freeGuard_unborrowed closedValid guarded)
    have releasedValid := SizedBufferHeap.step_valid closedValid freeStep
    have releasedInventory : ReaderInventory
        (SizedBufferHeap.release (SizedBufferHeap.close (run fuel (initial term)).state.heap token) object)
        (readerFrames stack) := ⟨remainingReaders.distinct,remainingReaders.live,remainingReaders.covered⟩
    have original := nextTyped
    simp only [restoredContinuation,enter,Term.subst,substArgs,Op.binders,liftSub,consValues] at original
    have valueTyped := original.free_tail
    have four := release_alias_return_four_steps (SizedBufferHeap.close (run fuel (initial term)).state.heap token)
      code first again ((Term.var owner).subst code.origins)
      (enter false domain (dynamicReferenceReader index length (.integer fallback)) code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
      object owner releaseIndex fallback stack stored selectedAlias live guarded
    dsimp only at four
    have sixteen := run_add 12 4 (run fuel (initial term)).state
    dsimp only at sixteen
    rw [twelve] at sixteen
    dsimp only at sixteen
    rw [four] at sixteen
    refine ⟨guarded,?_,valueTyped,releasedInventory,releasedValid,?_⟩
    · simp only [SizedBufferHeap.release,HeapLeases.put,ite_true]
    · simpa only [List.cons_append,List.nil_append,Nat.reduceAdd] using sixteen

end Jihoo.NativeKernel.Environment.BindingMachine
