import Jihoo.NativeBindingMachineOwnedReader

/-! Constructed allocating-reader/continuation execution with two distinct
owned values. The source checker supplies both resource obligations; actual
allocation supplies the new value and its guards. Arbitrary continuation-tail
resource simulation and closed-admission fundamental preservation remain open. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity CodeKinds
variable {control : Control}

/-- After the two actual source owner uses, neither distinct source capability
has residual demand. No tail demand/linearity certificate is supplied. -/
theorem checked_two_owner_tail_zero
    (checked : project (fuel+4) env loans ctx
      (.lend (.var owner) (.lam false domain readerBody)
        (.lam false (.buffer size) (.lam false again (.free (.var 1) (.free (.var 0) tail))))) = some control) :
    ∃ rest,
      projectRaw (fuel+1) env loans (⟨.buffer size,false⟩ :: ctx)
        (tail.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
      rest.demand 0 = some 0 ∧ rest.demand (owner+1) = some 0 ∧
      (∀ events, Prefix rest events → events.count 0 = 0 ∧ events.count (owner+1) = 0) := by
  obtain ⟨reader,rest,readProjected,restProjected,readZero,firstOne,ownerOne,finished,bounded⟩ :=
    dependent_buffer_first_contract checked
  rw [subst_free,subst_free,restored_first_result,restored_returned_owner] at restProjected
  obtain ⟨firstBinding,second,firstFound,firstRelevant,secondProjected,rfl⟩ := projectRaw_free_variable restProjected
  obtain ⟨ownerBinding,tailControl,ownerFound,ownerRelevant,tailProjected,rfl⟩ := projectRaw_free_variable secondProjected
  have zeroFirst : tailControl.demand 0 = some 0 := by
    cases demand : tailControl.demand 0 with
    | none => simp [Control.demand,demand] at firstOne
    | some count =>
        have zero : count = 0 := by
          simp [Control.demand,demand] at firstOne
          omega
        exact congrArg some zero
  have zeroOwner : tailControl.demand (owner+1) = some 0 := by
    cases demand : tailControl.demand (owner+1) with
    | none => simp [Control.demand,demand] at ownerOne
    | some count =>
        have zero : count = 0 := by
          simp [Control.demand,demand] at ownerOne
          omega
        exact congrArg some zero
  refine ⟨tailControl,tailProjected,zeroFirst,zeroOwner,?_⟩
  intro events run
  have firstBound := run.count_le zeroFirst
  have ownerBound := run.count_le zeroOwner
  constructor <;> omega

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

theorem unborrowed_close (unborrowed : HeapLeases.Unborrowed heap.heap object) (token : Nat) :
    HeapLeases.Unborrowed (SizedBufferHeap.close heap token).heap object := by
  intro queried leased
  by_cases same : queried = token
  · simp [SizedBufferHeap.close,HeapLeases.put,same] at leased
  · exact unborrowed queried (by simpa only [SizedBufferHeap.close,HeapLeases.put,same,↓reduceIte] using leased)

private theorem close_live (heap : SizedBufferHeap.State) (token : Nat) :
    (SizedBufferHeap.close heap token).heap.live = heap.heap.live := rfl

private theorem release_guard (heap : SizedBufferHeap.State) (released object : Nat) :
    freeGuard (SizedBufferHeap.release heap released) object = freeGuard heap object := rfl

set_option linter.unusedSimpArgs false in
private theorem allocate_reader_suffix (heap : SizedBufferHeap.State) (code : Code)
    (shape : code.term = .alloc (.natural count) (.integer fill))
    (countBound : count < 2^64) (fillBound : ValueReduction.signed64 fill)
    (fits : count*8+8 < 2^64) (stack : List Frame) (fuel : Nat) :
    run (fuel+5) ⟨heap,.evaluate code,stack⟩ =
      let result := run fuel ⟨SizedBufferHeap.allocate heap count (encodeInteger fill),
        .returned (.owner heap.heap.nextObject),stack⟩
      ⟨result.state,.heap (.alloc heap.heap.nextObject count (encodeInteger fill)) :: result.events,result.steps+5⟩ := by
  simp only [run,step,action,evaluateAction,shape,returnAction,execute,Code.child,
    countBound,fillBound,fits,↓reduceIte,Option.map_some]
  rfl

set_option linter.unusedSimpArgs false in
private theorem close_free_two_eleven_steps (heap : SizedBufferHeap.State) (code : Code)
    (leased : heap.heap.lease token = some object)
    (live : heap.heap.live object = true) (freshLive : heap.heap.live fresh = true)
    (different : fresh ≠ object) (freshUnborrowed : HeapLeases.Unborrowed heap.heap fresh)
    (first again tail ownerOrigin resultOrigin : Term) (name : Option Nat) (stack : List Frame) :
    let body := Term.free (.var 1) (.free (.var 0) tail)
    let closed := SizedBufferHeap.close heap token
    let freed := SizedBufferHeap.release closed fresh
    let bodyCode := restoredContinuation code first again body ownerOrigin resultOrigin object (.owner fresh)
    run 11 ⟨heap,.returned (.owner fresh),
      .lendFinish token object name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack⟩ =
      if freeGuard closed object then
        ⟨⟨SizedBufferHeap.release freed object,.evaluate (bodyCode.child tail),stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ownerOrigin,.heap (.free fresh),.heap (.free object)],11⟩
      else
        ⟨⟨freed,.fault .borrowedOwner,stack⟩,
          [.heap (.close token),.activate false (.lam false again body) resultOrigin,
            .activate false body ownerOrigin,.heap (.free fresh)],11⟩ := by
  have firstGuard := freeGuard_of_unborrowed (unborrowed_close freshUnborrowed token)
  have ownerLive : (SizedBufferHeap.release (SizedBufferHeap.close heap token) fresh).heap.live object = true := by
    simp only [SizedBufferHeap.release,HeapLeases.put,Ne.symm different,↓reduceIte,close_live,live]
  simp only [run,step,action,returnAction,execute,evaluateAction,Code.child,restoredContinuation,
    applyValue,enter,Option.map_some,List.getElem?_cons_zero,List.getElem?_cons_succ,
    leased,close_live,freshLive,firstGuard,ownerLive,release_guard,↓reduceIte]
  split <;> simp_all only [↓reduceIte] <;> rfl

/-- A checked fresh owned reader constructs its actual result, then releases
the two distinct objects through real retained bindings. The fresh result's
guard is automatic; only a remaining reader of the old owner can block its
release. Both byte overflow and that conflict are explicit outcomes. -/
theorem reachable_owned_reader_release (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .lend (.var owner) (.lam false domain (.alloc (.natural count) (.integer fill)))
      (.lam false (.buffer size) (.lam false again (.free (.var 1) (.free (.var 0) tail)))))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+4) env loans code.context code.term = some control)
    (evaluating : (run fuel (initial term)).state.control = .evaluate
      (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins)
        (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
        (code.child (.lam false (.buffer size) (.lam false again (.free (.var 1) (.free (.var 0) tail))))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let fresh := heap.heap.nextObject
    let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
    let closed := SizedBufferHeap.close allocated token
    let freed := SizedBufferHeap.release closed fresh
    let body := Term.free (.var 1) (.free (.var 0) tail)
    let ownerOrigin := (Term.var owner).subst code.origins
    let resultOrigin := (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
      (.borrow ownerOrigin) (some (.reference token))).origin
    let bodyCode := restoredContinuation code (.buffer size) again body ownerOrigin resultOrigin object (.owner fresh)
    fresh ≠ object ∧
      LoanTyping.HasType env [] [] true (bodyCode.child tail).origin type ∧
      (∃ rest,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans (⟨.buffer size,false⟩ :: code.context)
          (tail.subst (single ((Term.var owner).rename Nat.succ))) = some rest ∧
        rest.demand 0 = some 0 ∧ rest.demand (owner+1) = some 0 ∧
        (∀ events, Jihoo.Quantity.Prefix rest events → events.count 0 = 0 ∧ events.count (owner+1) = 0)) ∧
      if count*8+8 < 2^64 then
        BufferValue env allocated (.owner fresh) ((Term.buffer size).subst code.origins) ∧
        (freeGuard closed object = true ↔ ¬ ObjectReader object stack) ∧
        run 16 (run fuel (initial term)).state =
          if freeGuard closed object then
            ⟨⟨SizedBufferHeap.release freed object,.evaluate (bodyCode.child tail),stack⟩,
              [.heap (.alloc fresh count (encodeInteger fill)),.heap (.close token),
                .activate false (.lam false again body) resultOrigin,.activate false body ownerOrigin,
                .heap (.free fresh),.heap (.free object)],16⟩
          else
            ⟨⟨freed,.fault .borrowedOwner,stack⟩,
              [.heap (.alloc fresh count (encodeInteger fill)),.heap (.close token),
                .activate false (.lam false again body) resultOrigin,.activate false body ownerOrigin,
                .heap (.free fresh)],16⟩
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,(run fuel (initial term)).state.stack⟩,[],5⟩ := by
  have inputs := typed.allocating_first history shape checked
  have residual := LoanTyping.ResourceQuantity.checked_two_owner_tail_zero (shape ▸ checked)
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have valid := initial_run_heap_valid term fuel
  have live := (valid.leased token object leased).2
  have fresh := allocated_reader_fresh valid leased count (encodeInteger fill)
  have original := typed_explicit_continuation_origin history typed shape
    object (.owner (run fuel (initial term)).state.heap.heap.nextObject)
  have readerOrigin : (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
      (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin =
      (Lending.read (.var owner) (.alloc (.natural count) (.integer fill))).subst code.origins :=
    reader_entry_origin _ _ _ _ _
  change LoanTyping.HasType env [] [] true
    ((Term.free (.var 1) (.free (.var 0) tail)).subst
      (consValues ((Term.var owner).subst code.origins)
        (consValues ((Lending.read (.var owner) (.alloc (.natural count) (.integer fill))).subst code.origins) code.origins))) type at original
  rw [subst_free,subst_free] at original
  have tailTyped := original.free_tail.free_tail
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,
        .evaluate (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))),
        .lendFinish token object name ((Term.var owner).subst code.origins)
          (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
            (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
          (code.child (.lam false (.buffer size) (.lam false again (.free (.var 1) (.free (.var 0) tail))))) :: stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  refine ⟨fresh.1,?_,residual,?_⟩
  · change LoanTyping.HasType env [] [] true
      (tail.subst (consValues ((Term.var owner).subst code.origins)
        (consValues (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin code.origins))) type
    rw [readerOrigin]
    exact tailTyped
  · by_cases fits : count*8+8 < 2^64
    · simp only [fits,↓reduceIte]
      have allocatedLive : (SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill)).heap.live object = true := by
        simpa only [SizedBufferHeap.allocate,HeapLeases.put,Ne.symm fresh.1,↓reduceIte] using live
      have newLive : (SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill)).heap.live
          (run fuel (initial term)).state.heap.heap.nextObject = true := by simp [SizedBufferHeap.allocate,HeapLeases.put]
      have remaining := inventory.finish.2
      have closedValid := SizedBufferHeap.step_valid valid (.close leased)
      have guard := remaining.free_guard_iff (object := object) closedValid
      refine ⟨BufferValue.allocate inputs.2.2,guard,?_⟩
      have eleven := close_free_two_eleven_steps
        (SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill)) code
        leased allocatedLive newLive fresh.1 fresh.2.1 (.buffer size) again tail
        ((Term.var owner).subst code.origins)
        (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin name stack
      have executed := allocate_reader_suffix (run fuel (initial term)).state.heap
        (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))) rfl inputs.1 inputs.2.1 fits
        ((run fuel (initial term)).state.stack) 11
      rw [stackShape,eleven] at executed
      dsimp only at executed
      rw [← stateShape] at executed
      by_cases canFree : freeGuard (SizedBufferHeap.close
          (SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill)) token) object = true
      all_goals simpa only [canFree,Bool.false_eq_true,↓reduceIte] using executed
    · simp only [fits,↓reduceIte]
      obtain ⟨readerType,outlived,countBound,fillBound,different,executed⟩ :=
        reachable_allocating_reader term fuel code history typed shape evaluating stackShape
      simpa only [fits,↓reduceIte] using executed

end Jihoo.NativeKernel.Environment.BindingMachine
