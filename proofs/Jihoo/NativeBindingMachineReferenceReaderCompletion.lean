import Jihoo.NativeBindingMachineValueHandoff

/-! Compose an authentic explicit reference reader, its physical read, close
and both actual continuation bindings. Every intermediate state/result follows
from proved transitions, never a caller's execution/output certificate. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- Eleven actual transitions read through the retained reference, close its
lease, and bind the observed integer and owner to the original continuation.
The same full Lend/resource input constructs its canonical value/size contexts,
original closed result typing, restored loan slots and resource aliases. -/
theorem reachable_reference_reader_completion (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap code meanings)
    (shape : code.term = .lend (.var owner)
      (.lam false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))))
      (.lam false first (.lam false again body)))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (slots : LoanSlots code loans stack) (entered : Loans.Entered code.context.length loans)
    (stored : code.values[owner]? = some (some (.owner object)))
    (returned : (run fuel (initial term)).state.control = .returned
      (.closure false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count)))
        code.context code.origins code.values))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendReader token object (some (code.context.length-owner))
        ((Term.var owner).subst code.origins) readerOrigin
        (code.child (.lam false first (.lam false again body))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let closed := SizedBufferHeap.close heap token
    let readerBody := Term.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
    let readerCode := enter false domain readerBody code.context code.origins code.values
      (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
    let result := Value.integer (decodeInteger (heap.heap.payload object))
    let next := restoredContinuation code first again body ((Term.var owner).subst code.origins) readerCode.origin object result
    let nextMeanings := consValues ((Term.var owner).subst meanings)
      (consValues (.integer (decodeInteger (heap.heap.payload object))) meanings)
    heap.length object = count ∧ offset < count ∧
      run 11 (run fuel (initial term)).state =
        ⟨⟨closed,.evaluate next,stack⟩,
          [.activate false readerBody (.borrow ((Term.var owner).subst code.origins)),
            .heap (.read token offset (heap.heap.payload object)),.heap (.close token),
            .activate false (.lam false again body) readerCode.origin,
            .activate false body ((Term.var owner).subst code.origins)],11⟩ ∧
      ValueContext env next nextMeanings ∧ OwnerSizes env closed next nextMeanings ∧
      LoanTyping.HasType env [] [] true (next.term.subst nextMeanings) type ∧
      LoanSlots next loans stack ∧ ReaderInventory closed (readerFrames stack) ∧
      closed.heap.live object = true ∧
      (freeGuard closed object = true ↔ ¬ ObjectReader object stack) ∧
      (∀ index, next.values[index]? = (some result :: code.values)[Jihoo.Quantity.openOwner (owner+1) index]?) ∧
      ∃ reader mode rest,
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env (Loans.enter code.context.length owner loans)
          code.context (Lending.read (.var owner) readerBody) = some reader ∧
        LoanTyping.ResourceQuantity.projectRaw resourceFuel env loans (⟨first,false⟩ :: code.context)
          (body.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
        reader.demand owner = some 0 ∧ (Jihoo.Quantity.Control.scope mode rest).demand owner = some 1 ∧
        control = .seq reader (.scope mode rest) := by
  obtain ⟨valueType,outlived,length,ordered,referenceTyped,valueTyped,bodyContext,bodySizes,bodySlots,inventory,readExecuted⟩ :=
    reachable_reference_index_reader term fuel code history typed context sizes shape slots entered stored returned stackShape
  have reached := run_add fuel 6 (initial term)
  dsimp only at reached
  rw [readExecuted] at reached
  have reachedState : (run (fuel+6) (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,
        .returned (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))),
        .lendFinish token object (some (code.context.length-owner)) ((Term.var owner).subst code.origins)
          (enter false domain (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count)))
            code.context code.origins code.values (.borrow ((Term.var owner).subst code.origins))
            (some (.reference token))).origin (code.child (.lam false first (.lam false again body))) :: stack⟩ :=
    congrArg (fun result => result.state) reached
  have reachedHeap := congrArg State.heap reachedState
  have laterSizes : OwnerSizes env (run (fuel+6) (initial term)).state.heap code meanings := by
    rw [reachedHeap]
    exact sizes
  have handoff := reachable_value_lend_handoff term (fuel+6) code history typed context laterSizes shape checked stored
    slots entered (congrArg State.control reachedState) (congrArg State.stack reachedState)
  dsimp only at handoff
  rw [reachedHeap] at handoff
  obtain ⟨handed,nextContext,nextSizes,nextTyped,nextSlots,remaining,live,guard,aliases,resource⟩ := handoff
  have composed := run_add 6 5 (run fuel (initial term)).state
  dsimp only at composed
  rw [readExecuted] at composed
  dsimp only at composed
  rw [reachedState] at handed
  rw [handed] at composed
  exact ⟨length,ordered,composed,nextContext,nextSizes,nextTyped,nextSlots,remaining,live,guard,aliases,resource⟩

end Jihoo.NativeKernel.Environment.BindingMachine
