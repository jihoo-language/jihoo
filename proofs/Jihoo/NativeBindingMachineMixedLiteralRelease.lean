import Jihoo.NativeBindingMachineMixedDynamicRelease
import Jihoo.NativeBindingMachineCallLiteralRelease

/-! Original mixed admission derives complete release and original I64 result
for both index outcomes of this literal-fallback dependent call. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.ScalarCalls
open CodeKinds
variable {ownerDomain readerDomain first again : Term}

theorem admitted_literal_release
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (accepted : LoanTyping.MixedProgram.checkDeclaration 128 (resourceFuel+8) env source =
      some ⟨signature,function (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex)⟩)
    (countBound : count < 2^64) (offsetBound : offset < 2^64)
    (fillBound : ValueReduction.signed64 fill)
    (selectedAlias : releaseIndex = 0 ∨ releaseIndex = 2) :
    let input := program (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill
    LoanTyping.HasType env [] [] false input .i64 ∧
    if count*8+8 < 2^64 then
      let value := if offset < count then fill else fallback
      let ticks := if offset < count then 48 else 44
      LoanTyping.HasType env [] [] false (.integer value) .i64 ∧
      observe (run ticks (initial input)) = .integer value ∧
      (run ticks (initial input)).state.heap.heap.live 0 = false ∧
      (run ticks (initial input)).state.heap.heap.lease 0 = none ∧
      SizedBufferHeap.Valid (run ticks (initial input)).state.heap ∧
      ReaderInventory (run ticks (initial input)).state.heap [] ∧
      eventsHeap (run ticks (initial input)).events =
        [.alloc 0 count (encodeInteger fill),.beginLease 0 0] ++
          (if offset < count then [.read 0 offset (encodeInteger fill)] else []) ++ [.close 0,.free 0]
    else
      observe (run 23 (initial input)) = .fault .allocationOverflow ∧
      (run 23 (initial input)).state.heap = SizedBufferHeap.empty ∧
      eventsHeap (run 23 (initial input)).events = [] := by
  refine ⟨admitted_program_typed accepted countBound offsetBound fillBound,?_⟩
  obtain ⟨entryRun,entryEvents,typed,context,sizes,slots,entered,control,checked⟩ :=
    admitted_entry history accepted countBound offsetBound fillBound
  have reached := congrArg State.control entryRun
  have actualSizes : OwnerSizes env
      (run 15 (initial (program (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill))).state.heap
      (entry (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill)
      (entry (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill).origins := by
    rw [entryRun]
    exact sizes
  have actualSlots : LoanSlots
      (entry (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill) []
      (run 15 (initial (program (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill))).state.stack := by
    rw [entryRun]
    exact slots
  have result := reachable_raw_call_literal_release (resourceFuel := resourceFuel)
    (index := 2) (length := 3) (countIndex := 2) (fillIndex := 0)
    (program (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill) 15
    (entry (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill)
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
    obtain ⟨actualOffset,indexMeaning,lengthMeaning,valueTyped,dead,valid,inventory,executed,events⟩ := result
    have offsetSame : actualOffset = offset := by cases indexMeaning; rfl
    subst actualOffset
    have combined := run_add 15 (if offset < count then 33 else 29)
      (initial (program (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill))
    have stateResult := congrArg (fun result => result.state) combined
    dsimp only at stateResult
    rw [entryRun,executed] at stateResult
    have eventResult := congrArg (fun result => eventsHeap result.events) combined
    dsimp only at eventResult
    rw [eventsHeap_append,entryEvents,entryRun,events,List.nil_append] at eventResult
    have ticksAdd : 15+(if offset < count then 33 else 29) = (if offset < count then 48 else 44) := by
      split <;> rfl
    rw [ticksAdd] at stateResult eventResult
    have valueBound := valueTyped.integer_bound
    refine ⟨.integer valueBound.1 valueBound.2,?_,?_,?_,?_,?_,eventResult⟩
    · simp only [observe,stateResult]
    · rw [stateResult]
      exact dead
    · rw [stateResult]
      rfl
    · rw [stateResult]
      exact valid
    · rw [stateResult]
      exact inventory
  · simp only [fits,↓reduceIte] at result ⊢
    have combined := run_add 15 8
      (initial (program (dynamicCall ownerDomain readerDomain first again (.integer fallback) releaseIndex) count offset fill))
    dsimp only at combined
    rw [entryRun,result] at combined
    refine ⟨?_,?_,?_⟩
    · simp only [observe,combined]
    · exact congrArg (fun result => result.state.heap) combined
    · simpa only [eventsHeap_append,entryEvents,List.append_nil] using
        congrArg (fun result => eventsHeap result.events) combined

end Jihoo.NativeKernel.Environment.BindingMachine.ScalarCalls
