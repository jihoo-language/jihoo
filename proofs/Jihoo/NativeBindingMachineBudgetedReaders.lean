import Jihoo.NativeBindingMachineBudgetedRelease

/-! An original dependent reader receipt plus enclosing-reader authority
constructs both actual read and literal-fallback release for any old owner.
Numeric operands, heap bounds and successful reader values are all derived. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

theorem reachable_raw_budgeted_literal_reader_release (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some control)
    (shape : code.term = .lend (.var owner) (.lam false domain (dynamicReferenceReader index length (.integer fallback)))
      (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1)))))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans control)
    (coverage : LoanCoverage code loans stack)
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
      let next := restoredContinuation code first again (.free (.var releaseIndex) (.var 1))
        ((Term.var owner).subst code.origins) readerCode.origin object (.integer value)
      let nextMeanings := consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings)
      heap.length object = count ∧ freeGuard closed object = true ∧ released.heap.live object = false ∧
      LoanTyping.HasType env [] [] true (.integer value) (Term.subst meanings outside) ∧
      OwnerSizes env released next nextMeanings ∧ LoanSlots next loans stack ∧ LoanCoverage next loans stack ∧
      ReaderInventory released (readerFrames stack) ∧ SizedBufferHeap.Valid released ∧
      run ticks (run fuel (initial term)).state =
        ⟨⟨released,.returned (.integer value),stack⟩,
          [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))] ++
            (if offset < count then [.heap (.read token offset (heap.heap.payload object))] else []) ++
            [.heap (.close token),.activate false (.lam false again (.free (.var releaseIndex) (.var 1))) readerCode.origin,
              .activate false (.free (.var releaseIndex) (.var 1)) ((Term.var owner).subst code.origins),.heap (.free object)],ticks⟩ ∧
      ∃ rest,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans (⟨first,false⟩ :: code.context)
          ((Term.var 1).subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
        LoanTyping.ResourceQuantity.LoanBudget (code.context.length+1) loans rest ∧ rest.demand (owner+1) = some 0 := by
  obtain ⟨outside,offset,count,reader,mode,remaining,sourceClosing,indexStored,lengthStored,indexMeaning,lengthMeaning,
    readProjected,restProjected,readZero,restOne,same,physical,leased,live,bodyContext,bodySizes,selected⟩ :=
    reachable_raw_dynamic_reference_reader term fuel code history checked shape context sizes stored returned stackShape
  let readerBody := dynamicReferenceReader index length (.integer fallback)
  let readerCode := enter false domain readerBody code.context code.origins code.values
    (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
  let finishStack := .lendFinish token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
    readerCode.origin (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack
  have readerPrefix : run (if offset < count then 11 else 7) (run fuel (initial term)).state =
      ⟨⟨(run fuel (initial term)).state.heap,
        .returned (.integer (if offset < count then decodeInteger ((run fuel (initial term)).state.heap.heap.payload object) else fallback)),finishStack⟩,
        [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))] ++
          (if offset < count then [.heap (.read token offset ((run fuel (initial term)).state.heap.heap.payload object))] else []),
        (if offset < count then 11 else 7)⟩ := by
    by_cases compared : offset < count
    · simp only [compared,↓reduceIte] at selected ⊢
      obtain ⟨valueTyped,inventory,eleven⟩ := selected
      exact eleven
    · simp only [compared,↓reduceIte] at selected ⊢
      obtain ⟨noTyped,inventory,six⟩ := selected
      have literalTyped : LoanTyping.HasType env [] [] true (.integer fallback) (first.subst meanings) := by
        simpa only [Term.rename,renameArgs,Term.subst,substArgs] using noTyped
      have bounded := literalTyped.integer_bound
      have one : run 1 ⟨(run fuel (initial term)).state.heap,
          .evaluate (readerCode.child ((Term.integer fallback).rename Nat.succ)),finishStack⟩ =
          ⟨⟨(run fuel (initial term)).state.heap,.returned (.integer fallback),finishStack⟩,[],1⟩ := by
        simp only [run,step,action,evaluateAction,Code.child,Term.rename,renameArgs,bounded,↓reduceIte,execute,Option.map_some]
        rfl
      have composed := run_add 6 1 (run fuel (initial term)).state
      dsimp only at composed
      rw [six] at composed
      dsimp only at composed
      rw [one] at composed
      exact composed
  have globalPrefix := run_add fuel (if offset < count then 11 else 7) (initial term)
  dsimp only at globalPrefix
  rw [readerPrefix] at globalPrefix
  have reachedState := congrArg (fun result => result.state) globalPrefix
  have reachedHeap := congrArg State.heap reachedState
  have laterSizes : OwnerSizes env (run (fuel+(if offset < count then 11 else 7)) (initial term)).state.heap code meanings := by
    rw [reachedHeap]
    exact sizes
  have nine := reachable_raw_budgeted_scalar_release term (fuel+(if offset < count then 11 else 7)) code history
    sourceClosing context laterSizes shape (.ifLt : LoanTyping.ScalarReadShape (dynamicReferenceReader index length (.integer fallback)))
    checked budget coverage stored selectedAlias slots entered (congrArg State.control reachedState) (congrArg State.stack reachedState)
  dsimp only at nine
  rw [reachedHeap] at nine
  obtain ⟨guarded,dead,valueTyped,nextSizes,nextSlots,nextCoverage,inventory,valid,executed,tailBudget⟩ := nine
  have composed := run_add (if offset < count then 11 else 7) 9 (run fuel (initial term)).state
  dsimp only at composed
  rw [readerPrefix] at composed
  dsimp only at composed
  rw [reachedState] at executed
  rw [executed] at composed
  have ticksAdd : (if offset < count then 11 else 7)+9 = (if offset < count then 20 else 16) := by split <;> rfl
  rw [ticksAdd] at composed
  exact ⟨outside,offset,count,sourceClosing,indexMeaning,lengthMeaning,physical,guarded,dead,valueTyped,
    nextSizes,nextSlots,nextCoverage,inventory,valid,composed,tailBudget⟩

end Jihoo.NativeKernel.Environment.BindingMachine
