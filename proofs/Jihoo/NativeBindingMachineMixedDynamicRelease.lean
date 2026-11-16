import Jihoo.NativeBindingMachineMixedScalarEntry

/-! An authentic mixed declaration check supplies every intermediate context
for this dependent allocation/reader call. Literal argument ranges are the only
scalar premises; byte-size and index outcomes remain explicit alternatives. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.ScalarCalls
open CodeKinds

def dynamicCall (ownerDomain readerDomain first again no : Term) (releaseIndex : Nat) : Term :=
  .app (.lam false ownerDomain (allocatedDynamicBody readerDomain first again no 2 3 releaseIndex))
    (.alloc (.var 2) (.var 0))

variable {ownerDomain readerDomain first again no : Term}

/-- One original mixed admission constructs scalar entry, allocation, named
lease, reference read, close and alias release. No local call typing, contexts,
body check, pending frame, heap snapshot or output/success oracle is supplied.
The false branch retains a live lease at the original typed else body. -/
theorem admitted_dynamic_release
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration 128 (resourceFuel+8) env source =
      some ⟨signature,function (dynamicCall ownerDomain readerDomain first again no releaseIndex)⟩)
    (countBound : count < 2^64) (offsetBound : offset < 2^64)
    (fillBound : ValueReduction.signed64 fill)
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = 2) :
    let input := program (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill
    if count*8+8 < 2^64 then
      if offset < count then
        LoanTyping.HasType env [] [] true (.integer fill) .i64 ∧
        observe (run 48 (initial input)) = .integer fill ∧
        (run 48 (initial input)).state.heap.heap.live 0 = false ∧
        (run 48 (initial input)).state.heap.heap.lease 0 = none ∧
        SizedBufferHeap.Valid (run 48 (initial input)).state.heap ∧
        ReaderInventory (run 48 (initial input)).state.heap [] ∧
        eventsHeap (run 48 (initial input)).events =
          [.alloc 0 count (encodeInteger fill),.beginLease 0 0,.read 0 offset (encodeInteger fill),.close 0,.free 0]
      else
        (run 34 (initial input)).state.heap.heap.live 0 = true ∧
        (run 34 (initial input)).state.heap.heap.lease 0 = some 0 ∧
        ∃ code meanings result,
          (run 34 (initial input)).state.control = .evaluate code ∧
          LoanTyping.HasType env [] [] true (code.term.subst meanings) result ∧
          ValueContext env code meanings ∧ OwnerSizes env (run 34 (initial input)).state.heap code meanings ∧
          ReaderInventory (run 34 (initial input)).state.heap (readerFrames (run 34 (initial input)).state.stack) ∧
          eventsHeap (run 34 (initial input)).events = [.alloc 0 count (encodeInteger fill),.beginLease 0 0]
    else
      observe (run 23 (initial input)) = .fault .allocationOverflow ∧
      (run 23 (initial input)).state.heap = SizedBufferHeap.empty ∧
      eventsHeap (run 23 (initial input)).events = [] := by
  obtain ⟨entryRun,entryEvents,typed,context,sizes,slots,entered,control,checked⟩ :=
    admitted_entry history accepted countBound offsetBound fillBound
  have reached := congrArg State.control entryRun
  have actualSizes : OwnerSizes env
      (run 15 (initial (program (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill))).state.heap
      (entry (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill)
      (entry (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill).origins := by
    rw [entryRun]
    exact sizes
  have actualSlots : LoanSlots
      (entry (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill) []
      (run 15 (initial (program (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill))).state.stack := by
    rw [entryRun]
    exact slots
  have result := reachable_raw_call_dynamic_release (resourceFuel := resourceFuel)
    (index := 2) (length := 3) (countIndex := 2) (fillIndex := 0)
    (program (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill) 15
    (entry (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill)
    history reached typed checked rfl context actualSizes actualSlots entered selectedAlias
  dsimp only at result ⊢
  rw [entryRun] at result
  obtain ⟨actualCount,actualFill,countMeaning,fillMeaning,result⟩ := result
  have countSame : actualCount = count := by cases countMeaning; rfl
  have fillSame : actualFill = fill := by cases fillMeaning; rfl
  subst actualCount
  subst actualFill
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte] at result ⊢
    obtain ⟨actualOffset,indexMeaning,lengthMeaning,result⟩ := result
    have offsetSame : actualOffset = offset := by cases indexMeaning; rfl
    subst actualOffset
    by_cases compared : offset < count
    · simp only [compared,↓reduceIte] at result ⊢
      obtain ⟨valueTyped,dead,valid,inventory,executed,events⟩ := result
      have combined := run_add 15 33 (initial (program (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill))
      have stateResult := congrArg (fun result => result.state) combined
      dsimp only at stateResult
      rw [entryRun,executed] at stateResult
      have eventResult := congrArg (fun result => eventsHeap result.events) combined
      dsimp only at eventResult
      rw [eventsHeap_append,entryEvents,entryRun,events,List.nil_append] at eventResult
      refine ⟨valueTyped,?_,?_,?_,?_,?_,eventResult⟩
      · simp only [observe,stateResult]
      · rw [stateResult]
        exact dead
      · rw [stateResult]
        rfl
      · rw [stateResult]
        exact valid
      · rw [stateResult]
        exact inventory
    · simp only [compared,↓reduceIte] at result ⊢
      obtain ⟨noTyped,noContext,noSizes,inventory,executed,events⟩ := result
      have combined := run_add 15 19 (initial (program (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill))
      have stateResult := congrArg (fun result => result.state) combined
      dsimp only at stateResult
      rw [entryRun,executed] at stateResult
      have eventResult := congrArg (fun result => eventsHeap result.events) combined
      dsimp only at eventResult
      rw [eventsHeap_append,entryEvents,entryRun,events,List.nil_append] at eventResult
      refine ⟨?_,?_,_,_,_,?_,noTyped,noContext,?_,?_,eventResult⟩
      · rw [stateResult]
        rfl
      · rw [stateResult]
        rfl
      · exact congrArg State.control stateResult
      · rw [stateResult]
        exact noSizes
      · rw [stateResult]
        exact inventory
  · simp only [fits,↓reduceIte] at result ⊢
    have combined := run_add 15 8 (initial (program (dynamicCall ownerDomain readerDomain first again no releaseIndex) count offset fill))
    dsimp only at combined
    rw [entryRun,result] at combined
    refine ⟨?_,?_,?_⟩
    · simp only [observe,combined]
    · exact congrArg (fun result => result.state.heap) combined
    · simpa only [eventsHeap_append,entryEvents,List.append_nil] using
        congrArg (fun result => eventsHeap result.events) combined

end Jihoo.NativeKernel.Environment.BindingMachine.ScalarCalls
