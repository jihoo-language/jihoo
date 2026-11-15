import Jihoo.NativeBindingMachineCallDynamicRelease
import Jihoo.NativeBindingMachineAllocatedLiteralRelease

/-! One original full call judgment composes allocation with both original
literal-fallback outcomes, at its exact original closed result type. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

theorem reachable_raw_call_literal_release (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (typed : LoanClosingTyped env loans false code meanings type)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+5) env loans code.context code.term = some control)
    (shape : code.term = .app
      (.lam false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex))
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
      let argumentOrigin := (code.child (.alloc (.var countIndex) (.var fillIndex))).origin
      let sourceBody := allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex
      let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
      let lent := SizedBufferHeap.lend allocated object
      let released := SizedBufferHeap.release (SizedBufferHeap.close lent token) object
      let bodyMeanings := consValues (.alloc (.natural count) (.integer fill)) meanings
      if count*8+8 < 2^64 then
        ∃ offset, bodyMeanings index = .natural offset ∧ bodyMeanings length = .natural count ∧
          let value := if offset < count then fill else fallback
          let ticks := if offset < count then 33 else 29
          LoanTyping.HasType env [] [] true (.integer value) type ∧
          released.heap.live object = false ∧ SizedBufferHeap.Valid released ∧ ReaderInventory released (readerFrames stack) ∧
          (run ticks (run fuel (initial term)).state).state = ⟨released,.returned (.integer value),stack⟩ ∧
          eventsHeap (run ticks (run fuel (initial term)).state).events =
            [.alloc object count (encodeInteger fill),.beginLease token object] ++
              (if offset < count then [.read token offset (encodeInteger fill)] else []) ++ [.close token,.free object]
      else run 8 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,
          .argument (.closure false ownerDomain sourceBody code.context code.origins code.values) argumentOrigin :: stack⟩,[],8⟩ := by
  obtain ⟨argumentType,result,functionTyped,argumentTyped,resultConverted⟩ := typed.lambda_call_inputs history shape
  obtain ⟨bodyControl,bodyProjected⟩ := LoanTyping.ResourceQuantity.projectRaw_single_lambda_call_body
    (shape ▸ checked)
  have stateShape : (run fuel (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate code,(run fuel (initial term)).state.stack⟩ := by
    cases state : (run fuel (initial term)).state
    simp_all
  have three := literal_call_three_steps (run fuel (initial term)).state.heap code ownerDomain
    (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex) (.alloc (.var countIndex) (.var fillIndex))
    (run fuel (initial term)).state.stack shape
  rw [← stateShape] at three
  have globalPrefix := run_add fuel 3 (initial term)
  dsimp only at globalPrefix
  rw [three] at globalPrefix
  have reachedState : (run (fuel+3) (initial term)).state =
      ⟨(run fuel (initial term)).state.heap,.evaluate (code.child (.alloc (.var countIndex) (.var fillIndex))),
        .argument (.closure false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex)
          code.context code.origins code.values) (code.child (.alloc (.var countIndex) (.var fillIndex))).origin ::
          (run fuel (initial term)).state.stack⟩ := congrArg (fun result => result.state) globalPrefix
  have reachedHeap := congrArg State.heap reachedState
  have laterSizes : OwnerSizes env (run (fuel+3) (initial term)).state.heap
      (code.child (.lam false ownerDomain (allocatedDynamicBody readerDomain first again (.integer fallback) index length releaseIndex))) meanings := by
    rw [reachedHeap]
    exact sizes.child _
  have result := reachable_allocated_literal_release term (fuel+3) history (congrArg State.control reachedState)
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
    obtain ⟨offset,indexMeaning,lengthMeaning,valueTyped,dead,valid,inventory,executed,events⟩ := result
    refine ⟨offset,indexMeaning,lengthMeaning,valueTyped.convert resultConverted,dead,valid,inventory,?_,?_⟩
    all_goals
      have composed := run_add 3 (if offset < count then 30 else 26) (run fuel (initial term)).state
      have stateResult := congrArg (fun result => result.state) composed
      dsimp only at stateResult
      rw [three] at stateResult
      dsimp only at stateResult
      rw [reachedState] at executed
      rw [executed] at stateResult
      have eventResult := congrArg (fun result => eventsHeap result.events) composed
      dsimp only at eventResult
      rw [three] at eventResult
      dsimp only at eventResult
      rw [eventsHeap_append] at eventResult
      change eventsHeap (run (3+(if offset < count then 30 else 26)) (run fuel (initial term)).state).events =
        [] ++ eventsHeap (run (if offset < count then 30 else 26) _).events at eventResult
      rw [reachedState] at events
      rw [events,List.nil_append] at eventResult
      by_cases compared : offset < count
      · first
        | simpa only [compared,↓reduceIte] using stateResult
        | simpa only [compared,↓reduceIte] using eventResult
      · first
        | simpa only [compared,↓reduceIte] using stateResult
        | simpa only [compared,↓reduceIte] using eventResult
  · simp only [fits,↓reduceIte] at result ⊢
    have composed := run_add 3 5 (run fuel (initial term)).state
    dsimp only at composed
    rw [three] at composed
    dsimp only at composed
    rw [reachedState] at result
    rw [result] at composed
    exact composed

end Jihoo.NativeKernel.Environment.BindingMachine
