import Jihoo.NativeBindingMachineMutableLoad
import Jihoo.NativeBindingMachineMutableHeapHistory

/-! A closed checked Store→Load expression transfers one allocated Buffer
through the write, read and release. The indexed read observes the stored
value rather than the allocation's uniform fill. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

private def storeArgument (count offset : Nat) (fill value : Int) : Term :=
  .store (.alloc (.natural count) (.integer fill)) (.natural offset) (.integer value)
    (.decide (.natural offset) (.natural count))

private def releaseBody : Term := .free (.var 0) (.var 1)

private def readCallback (count : Nat) : Term :=
  .lam false .i64 (.lam false (.buffer (.natural count)) releaseBody)

def storeLoadProgram (count offset : Nat) (fill value : Int) : Term :=
  .load (storeArgument count offset fill value) (.natural offset) (.decide (.natural offset) (.natural count))
    (readCallback count)

private def allocatedBuffer (count : Nat) (fill : Int) : SizedBufferHeap.IndexedState :=
  ⟨SizedBufferHeap.allocate SizedBufferHeap.empty count (encodeInteger fill),
    HeapLeases.put (fun object _ => SizedBufferHeap.empty.heap.payload object) 0 (fun _ => encodeInteger fill)⟩

private def writtenBuffer (count offset : Nat) (fill value : Int) : SizedBufferHeap.IndexedState :=
  let allocated := allocatedBuffer count fill
  { allocated with cell := HeapLeases.put allocated.cell 0 (HeapLeases.put (allocated.cell 0) offset (encodeInteger value)) }

private def pendingLoad (count offset : Nat) (fill value : Int) : BufferFrame × List Frame :=
  (.loadOwner (storeArgument count offset fill value) (Code.initial (.natural offset))
    (Code.initial (readCallback count)),[])

private theorem allocate_steps (count offset : Nat) (fill value : Int)
    (countWidth : count < 2^64) (fillWidth : ValueReduction.signed64 fill) (fits : count*8+8 < 2^64) :
    run 7 (initial (storeLoadProgram count offset fill value)) =
      ⟨⟨allocatedBuffer count fill,.returned (.owner 0),[],
        (.owner (Code.initial (.natural offset)) (Code.initial (.integer value)),[]) ::
          [pendingLoad count offset fill value]⟩,
        [.legacy (.heap (.alloc 0 count (encodeInteger fill)))],7⟩ := by
  simp only [storeLoadProgram,storeArgument,run,initial,Code.initial,step,evaluateAction,Code.child,
    executeLegacy,execute,returnAction,Code.origin,Term.subst_id,countWidth,fillWidth,fits,ite_true,Option.map_none]
  rfl

private theorem write_steps (count offset : Nat) (fill value : Int)
    (offsetWidth : offset < 2^64) (valueWidth : ValueReduction.signed64 value) (within : offset < count) :
    run 5 ⟨allocatedBuffer count fill,.returned (.owner 0),[],
      (.owner (Code.initial (.natural offset)) (Code.initial (.integer value)),[]) ::
        [pendingLoad count offset fill value]⟩ =
      ⟨⟨writtenBuffer count offset fill value,.returned (.owner 0),[],[pendingLoad count offset fill value]⟩,
        [.store 0 offset (encodeInteger value)],5⟩ := by
  let pre := allocatedBuffer count fill
  have live : pre.metadata.heap.live 0 = true := rfl
  have unborrowed : freeGuard pre.metadata 0 = true := rfl
  have length : pre.metadata.length 0 = count := SizedBufferHeap.allocation_length
  have store : pre.store 0 offset (encodeInteger value) = some (writtenBuffer count offset fill value) := by
    simp only [SizedBufferHeap.IndexedState.store,live,unborrowed,length,within,true_and,ite_true]
    rfl
  change (allocatedBuffer count fill).store 0 offset (encodeInteger value) = _ at store
  simp only [run,step,returnAction,resumeBuffer,executeLegacy,execute,evaluateAction,Code.initial,
    offsetWidth,valueWidth,ite_true,Option.map_none,store]
  rfl

private theorem read_steps (count offset : Nat) (fill value : Int)
    (offsetWidth : offset < 2^64) (valueWidth : ValueReduction.signed64 value) (within : offset < count) :
    run 3 ⟨writtenBuffer count offset fill value,.returned (.owner 0),[],[pendingLoad count offset fill value]⟩ =
      ⟨⟨writtenBuffer count offset fill value,.evaluate (Code.initial (readCallback count)),[],
        [(.loadContinuation 0 (storeArgument count offset fill value) value,[])]⟩,
        [.load 0 offset (encodeInteger value)],3⟩ := by
  let written := writtenBuffer count offset fill value
  have live : written.metadata.heap.live 0 = true := rfl
  have unborrowed : freeGuard written.metadata 0 = true := rfl
  have length : written.metadata.length 0 = count := SizedBufferHeap.allocation_length
  have load : written.load 0 offset = some (encodeInteger value) := by
    unfold SizedBufferHeap.IndexedState.load
    rw [ite_eq_left ⟨live,unborrowed,length.symm ▸ within⟩]
    simp only [written,writtenBuffer,HeapLeases.put,↓reduceIte]
  change (writtenBuffer count offset fill value).load 0 offset = _ at load
  simp only [pendingLoad,run,step,returnAction,resumeBuffer,executeLegacy,execute,evaluateAction,Code.initial,
    offsetWidth,ite_true,Option.map_none,load,encode_decode_integer valueWidth]
  rfl

private theorem release_steps (count offset : Nat) (fill value : Int) :
    let written := writtenBuffer count offset fill value
    run 8 ⟨written,.evaluate (Code.initial (readCallback count)),[],
      [(.loadContinuation 0 (storeArgument count offset fill value) value,[])]⟩ =
      ⟨⟨⟨SizedBufferHeap.release written.metadata 0,written.cell⟩,.returned (.integer value),[],[]⟩,
        [.legacy (.activate false (.lam false (.buffer (.natural count)) releaseBody) (.integer value)),
          .legacy (.activate false releaseBody (storeArgument count offset fill value)),
          .legacy (.heap (.free 0))],8⟩ := by
  let written := writtenBuffer count offset fill value
  have live : (writtenBuffer count offset fill value).metadata.heap.live 0 = true := rfl
  have unborrowed : freeGuard (writtenBuffer count offset fill value).metadata 0 = true := rfl
  simp only [readCallback,releaseBody,run,step,Code.initial,evaluateAction,executeLegacy,execute,returnAction,
    resumeBuffer,applyValue,enter,Code.child,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.map_none,Option.map_some,live,unborrowed,ite_true]
  rfl

private theorem run_append (first second : Nat) (state : State) :
    run (first+second) state =
      let before := run first state
      let after := run second before.state
      ⟨after.state,before.events ++ after.events,before.steps+after.steps⟩ := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,run,List.nil_append]
  | succ first ih =>
      simp only [Nat.succ_add,run]
      cases stepped : step state with
      | none =>
          have stopped (fuel : Nat) : run fuel state = ⟨state,[],0⟩ := by
            cases fuel <;> simp only [run,stepped]
          simp only [stopped,List.nil_append,Nat.zero_add]
      | some result =>
          obtain ⟨next,event⟩ := result
          simp only
          rw [ih]
          simp only [List.append_assoc,Nat.add_assoc,Nat.add_comm]

private theorem storeLoadProgram_steps (count offset : Nat) (fill value : Int)
    (countWidth : count < 2^64) (offsetWidth : offset < 2^64)
    (fillWidth : ValueReduction.signed64 fill) (valueWidth : ValueReduction.signed64 value)
    (within : offset < count) (fits : count*8+8 < 2^64) :
    let written := writtenBuffer count offset fill value
    run 23 (initial (storeLoadProgram count offset fill value)) =
      ⟨⟨⟨SizedBufferHeap.release written.metadata 0,written.cell⟩,.returned (.integer value),[],[]⟩,
        [.legacy (.heap (.alloc 0 count (encodeInteger fill))), .store 0 offset (encodeInteger value),
          .load 0 offset (encodeInteger value),
          .legacy (.activate false (.lam false (.buffer (.natural count)) (.free (.var 0) (.var 1))) (.integer value)),
          .legacy (.activate false (.free (.var 0) (.var 1)) (storeArgument count offset fill value)),
          .legacy (.heap (.free 0))],23⟩ := by
  dsimp only
  rw [run_append 7 (5+(3+8)),allocate_steps _ _ _ _ countWidth fillWidth fits]
  dsimp only
  rw [run_append 5 (3+8),write_steps _ _ _ _ offsetWidth valueWidth within]
  dsimp only
  rw [run_append 3 8,read_steps _ _ _ _ offsetWidth valueWidth within]
  dsimp only
  rw [release_steps]
  rfl

/-- Checked typing supplies all primitive input ranges and the continuation's
exact result type. The actual evaluator writes, reads, and releases the same
physical owner with the same offset, and returns precisely the written integer. -/
theorem checked_closed_store_load (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env
      ⟨type,storeLoadProgram count offset fill value⟩ = some ⟨type,storeLoadProgram count offset fill value⟩)
    (fits : count*8+8 < 2^64) :
    let written := writtenBuffer count offset fill value
    run 23 (initial (storeLoadProgram count offset fill value)) =
      ⟨⟨⟨SizedBufferHeap.release written.metadata 0,written.cell⟩,.returned (.integer value),[],[]⟩,
        [.legacy (.heap (.alloc 0 count (encodeInteger fill))), .store 0 offset (encodeInteger value),
          .load 0 offset (encodeInteger value),
          .legacy (.activate false (.lam false (.buffer (.natural count)) (.free (.var 0) (.var 1))) (.integer value)),
          .legacy (.activate false (.free (.var 0) (.var 1)) (storeArgument count offset fill value)),
          .legacy (.heap (.free 0))],23⟩ ∧
    LoanTyping.HasType env [] [] false (.integer value) type := by
  obtain ⟨_,_,typed,_⟩ := (LoanTyping.MixedProgram.checkDeclaration_sound checked).valid.typing
  unfold storeLoadProgram storeArgument readCallback releaseBody at typed
  obtain ⟨_,storeTyped,offsetTyped,bound⟩ := typed.load_inputs
  obtain ⟨_,allocTyped,_,valueTyped,_,_⟩ := storeTyped.store_inputs
  obtain ⟨countTyped,fillTyped⟩ := allocTyped.alloc_inputs
  have valueWidth := valueTyped.integer_bound
  have limits := bound.literal_decide_limits history.wellFormed
  have finished := LoanTyping.load_ghost_finish history.wellFormed typed valueWidth
  have activated : LoanTyping.HasType env [] [] true
      (.free (storeArgument count offset fill value) (.integer value)) type := by
    simpa only [storeArgument,Term.subst,substArgs,Op.binders,liftSub,liftSubOne,single,
      Term.rename,renameArgs,liftRenaming,Term.subst_id] using finished
  exact ⟨storeLoadProgram_steps count offset fill value countTyped.natural_bound offsetTyped.natural_bound
    fillTyped.integer_bound valueWidth limits.2.2 fits,
    (LoanTyping.HasType.integer valueWidth.1 valueWidth.2).convert activated.free_tail.principalView⟩

/-- The public result records the written observation, the retired owner's
original length, and the actual allocation followed by exactly one release. -/
theorem checked_closed_store_load_observation
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (checked : LoanTyping.MixedProgram.checkDeclaration fuel quantityFuel env
      ⟨type,storeLoadProgram count offset fill value⟩ = some ⟨type,storeLoadProgram count offset fill value⟩)
    (fits : count*8+8 < 2^64) :
    let evaluated := run 23 (initial (storeLoadProgram count offset fill value))
    observe evaluated = .integer value ∧
      evaluated.state.heap.metadata.heap.live 0 = false ∧
      evaluated.state.heap.metadata.length 0 = count ∧
      evaluated.state.heap.cell 0 offset = encodeInteger value ∧
      evaluated.events.filterMap Event.lifecycle? = [.alloc 0 count (encodeInteger fill),.free 0] ∧
      LoanTyping.HasType env [] [] false (.integer value) type := by
  obtain ⟨executed,typed⟩ := checked_closed_store_load history checked fits
  dsimp only
  rw [executed]
  refine ⟨rfl,rfl,?_,?_,rfl,typed⟩
  · change (SizedBufferHeap.allocate SizedBufferHeap.empty count (encodeInteger fill)).length 0 = count
    exact SizedBufferHeap.allocation_length
  · simp only [writtenBuffer,HeapLeases.put,↓reduceIte]

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
