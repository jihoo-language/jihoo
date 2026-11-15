import Jihoo.NativeBindingMachineDynamicReaderCompletion

/-! A fresh argument's identity cannot occur in its earlier caller's reader
frames. The authentic dynamic reader/resource check then constructs physical
read, close, alias release and scalar return without a supplied Free guard. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- Actual saved-frame provenance excludes every future allocation identity,
including when the old captured owner is already released. -/
theorem StackOwners.no_reader_at_limit (owners : StackOwners limit stack) : ¬ ObjectReader limit stack := by
  rintro ⟨frame,member,token,name,descriptor⟩
  have before := owners frame member
  cases frame <;> simp_all [Frame.reader?,FrameOwners]
  all_goals omega

set_option linter.unusedSimpArgs false in
private theorem release_alias_return_four_steps (heap : SizedBufferHeap.State) (code : Code)
    (first again ownerOrigin resultOrigin : Term) (object owner releaseIndex : Nat) (value : Int) (stack : List Frame)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selected : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (live : heap.heap.live object = true) (guarded : freeGuard heap object = true) :
    let body := Term.free (.var releaseIndex) (.var 1)
    let next := restoredContinuation code first again body ownerOrigin resultOrigin object (.integer value)
    run 4 ⟨heap,.evaluate next,stack⟩ =
      ⟨⟨SizedBufferHeap.release heap object,.returned (.integer value),stack⟩,[.heap (.free object)],4⟩ := by
  have aliasStored : (some (.owner object) :: some (.integer value) :: code.values)[releaseIndex]? =
      some (some (.owner object)) := by
    rcases selected with rfl | rfl
    · rfl
    · simpa only [Nat.add_assoc,List.getElem?_cons_succ] using stored
  simp only [run,step,action,evaluateAction,returnAction,execute,Code.child,restoredContinuation,enter,
    aliasStored,live,guarded,↓reduceIte,Option.map_some,List.getElem?_cons_succ,List.getElem?_cons_zero]
  rfl

/-- An earlier actual call prefix supplies fresh-identity provenance, not an
allocation snapshot or a safety certificate. Together with the authentic
Lend/resource receipt it derives the Free guard, releases either physical
owner alias once, and returns the actual scalar at the original inferred type.
Arbitrary earlier reader stacks are allowed. -/
theorem reachable_raw_fresh_dynamic_reader_release (term : Term) (birthFuel fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some control)
    (shape : code.term = .lend (.var owner) (.lam false domain (dynamicReferenceReader index length no))
      (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1)))))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (born : object = (run birthFuel (initial term)).state.heap.heap.nextObject)
    (birthStack : (run birthFuel (initial term)).state.stack = .argument function argumentOrigin :: stack)
    (returned : (run fuel (initial term)).state.control = .returned
      (.closure false domain (dynamicReferenceReader index length no) code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins) readerOrigin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack) :
    ∃ outside offset count,
      LoanClosingTyped env loans false code meanings (Term.subst meanings outside) ∧
      meanings index = .natural offset ∧ meanings length = .natural count ∧
      let heap := (run fuel (initial term)).state.heap
      let closed := SizedBufferHeap.close heap token
      let released := SizedBufferHeap.release closed object
      let readerBody := dynamicReferenceReader index length no
      let readerCode := enter false domain readerBody code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
      let readerMeanings := consValues (.borrow ((Term.var owner).subst meanings)) meanings
      let finishStack := .lendFinish token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerCode.origin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack
      heap.length object = count ∧
      if offset < count then
        let value := decodeInteger (heap.heap.payload object)
        let next := restoredContinuation code first again (.free (.var releaseIndex) (.var 1))
          ((Term.var owner).subst code.origins) readerCode.origin object (.integer value)
        let nextMeanings := consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings)
        freeGuard closed object = true ∧ released.heap.live object = false ∧
        LoanTyping.HasType env [] [] true (.integer value) (Term.subst meanings outside) ∧
        OwnerSizes env released next nextMeanings ∧ ReaderInventory released (readerFrames stack) ∧
        SizedBufferHeap.Valid released ∧
        run 20 (run fuel (initial term)).state =
          ⟨⟨released,.returned (.integer value),stack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins)),
              .heap (.read token offset (heap.heap.payload object)),.heap (.close token),
              .activate false (.lam false again (.free (.var releaseIndex) (.var 1))) readerCode.origin,
              .activate false (.free (.var releaseIndex) (.var 1)) ((Term.var owner).subst code.origins),
              .heap (.free object)],20⟩ ∧
        ∃ rest,
          LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans (⟨first,false⟩ :: code.context)
            ((Term.var 1).subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
          rest.demand (owner+1) = some 0 ∧
          (∀ events, Jihoo.Quantity.Prefix rest events → events.count (owner+1) = 0)
      else
        LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst readerMeanings) (first.subst meanings) ∧
        ValueContext env (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        OwnerSizes env heap (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        ReaderInventory heap (readerFrames finishStack) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨heap,.evaluate (readerCode.child (no.rename Nat.succ)),finishStack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))],6⟩ := by
  have oldOwners := (initial_run_owners term birthFuel).2
  rw [birthStack] at oldOwners
  have absent : ¬ ObjectReader object stack := by
    rw [born]
    exact oldOwners.tail.no_reader_at_limit
  obtain ⟨outside,offset,count,reader,mode,remaining,sourceClosing,indexMeaning,lengthMeaning,
    readProjected,restProjected,readZero,restOne,same,physical,completed⟩ :=
    reachable_raw_dynamic_reader_completion (resourceFuel := resourceFuel+2) term fuel code history checked shape
      context sizes slots entered stored returned stackShape
  refine ⟨outside,offset,count,sourceClosing,indexMeaning,lengthMeaning,physical,?_⟩
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte] at completed ⊢
    obtain ⟨executed,nextContext,nextSizes,nextTyped,nextSlots,inventory,live,guard,aliases⟩ := completed
    have guarded := guard.mpr absent
    have closedValid := run_heap_valid (state := (run fuel (initial term)).state)
      (initial_run_heap_valid term fuel) 16
    rw [executed] at closedValid
    have freeStep := SizedBufferHeap.Step.free live (freeGuard_unborrowed closedValid guarded)
    have releasedValid := SizedBufferHeap.step_valid closedValid freeStep
    have releasedSizes := nextSizes.steps (.cons freeStep .nil)
    have releasedInventory : ReaderInventory
        (SizedBufferHeap.release (SizedBufferHeap.close (run fuel (initial term)).state.heap token) object)
        (readerFrames stack) := ⟨inventory.distinct,inventory.live,inventory.covered⟩
    have original := nextTyped
    simp only [restoredContinuation,enter,Term.subst,substArgs,Op.binders,liftSub,consValues] at original
    have scalarTyped := original.free_tail
    have freed := release_alias_return_four_steps (SizedBufferHeap.close (run fuel (initial term)).state.heap token)
      code first again ((Term.var owner).subst code.origins)
      (enter false domain (dynamicReferenceReader index length no) code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
      object owner releaseIndex (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object)) stack
      stored selectedAlias live guarded
    dsimp only at freed
    have composed := run_add 16 4 (run fuel (initial term)).state
    dsimp only at composed
    rw [executed] at composed
    dsimp only at composed
    rw [freed] at composed
    refine ⟨guarded,?_,scalarTyped,releasedSizes,releasedInventory,releasedValid,composed,?_⟩
    · simp only [SizedBufferHeap.release,HeapLeases.put,ite_true]
    · exact LoanTyping.ResourceQuantity.raw_lend_free_tail_zero selectedAlias (shape ▸ checked)
  · simpa only [compared,↓reduceIte] using completed

/-- The full outer resource query supplies its exact internal receipt. -/
theorem reachable_fresh_dynamic_reader_release (term : Term) (birthFuel fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+3) env loans code.context code.term = some control)
    (shape : code.term = .lend (.var owner) (.lam false domain (dynamicReferenceReader index length no))
      (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1)))))
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = owner+2)
    (born : object = (run birthFuel (initial term)).state.heap.heap.nextObject)
    (birthStack : (run birthFuel (initial term)).state.stack = .argument function argumentOrigin :: stack)
    (returned : (run fuel (initial term)).state.control = .returned
      (.closure false domain (dynamicReferenceReader index length no) code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins) readerOrigin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack) :
    ∃ outside offset count,
      LoanClosingTyped env loans false code meanings (Term.subst meanings outside) ∧
      meanings index = .natural offset ∧ meanings length = .natural count ∧
      let heap := (run fuel (initial term)).state.heap
      let closed := SizedBufferHeap.close heap token
      let released := SizedBufferHeap.release closed object
      let readerBody := dynamicReferenceReader index length no
      let readerCode := enter false domain readerBody code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
      let readerMeanings := consValues (.borrow ((Term.var owner).subst meanings)) meanings
      let finishStack := .lendFinish token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerCode.origin
        (code.child (.lam false first (.lam false again (.free (.var releaseIndex) (.var 1))))) :: stack
      heap.length object = count ∧
      if offset < count then
        let value := decodeInteger (heap.heap.payload object)
        let next := restoredContinuation code first again (.free (.var releaseIndex) (.var 1))
          ((Term.var owner).subst code.origins) readerCode.origin object (.integer value)
        let nextMeanings := consValues ((Term.var owner).subst meanings) (consValues (.integer value) meanings)
        freeGuard closed object = true ∧ released.heap.live object = false ∧
        LoanTyping.HasType env [] [] true (.integer value) (Term.subst meanings outside) ∧
        OwnerSizes env released next nextMeanings ∧ ReaderInventory released (readerFrames stack) ∧
        SizedBufferHeap.Valid released ∧
        run 20 (run fuel (initial term)).state =
          ⟨⟨released,.returned (.integer value),stack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins)),
              .heap (.read token offset (heap.heap.payload object)),.heap (.close token),
              .activate false (.lam false again (.free (.var releaseIndex) (.var 1))) readerCode.origin,
              .activate false (.free (.var releaseIndex) (.var 1)) ((Term.var owner).subst code.origins),
              .heap (.free object)],20⟩ ∧
        ∃ rest,
          LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans (⟨first,false⟩ :: code.context)
            ((Term.var 1).subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
          rest.demand (owner+1) = some 0 ∧
          (∀ events, Jihoo.Quantity.Prefix rest events → events.count (owner+1) = 0)
      else
        LoanTyping.HasType env [] [] true ((no.rename Nat.succ).subst readerMeanings) (first.subst meanings) ∧
        ValueContext env (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        OwnerSizes env heap (readerCode.child (no.rename Nat.succ)) readerMeanings ∧
        ReaderInventory heap (readerFrames finishStack) ∧
        run 6 (run fuel (initial term)).state =
          ⟨⟨heap,.evaluate (readerCode.child (no.rename Nat.succ)),finishStack⟩,
            [.activate false readerBody (.borrow ((Term.var owner).subst code.origins))],6⟩ := by
  exact reachable_raw_fresh_dynamic_reader_release term birthFuel fuel code history (LoanTyping.ResourceQuantity.project_origin checked)
    shape context sizes slots entered stored selectedAlias born birthStack returned stackShape

end Jihoo.NativeKernel.Environment.BindingMachine
