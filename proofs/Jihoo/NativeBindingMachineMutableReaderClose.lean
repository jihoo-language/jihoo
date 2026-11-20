import Jihoo.NativeBindingMachineMutableHeapHistory

/-! Close an indexed reader using the lease inventory of the whole machine,
including readers held in suspended continuations. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

/-- The actual close removes exactly the finishing reader. Its result is
retained for the original continuation, and all indexed cells, suspended
frames and other leases survive the transition. -/
theorem lend_close_step (inventory : ReaderInventory state.heap.metadata (readerFrames state.activeStack))
    (returned : state.control = .returned value)
    (stackShape : state.stack = .lendFinish token object name origin resultOrigin continuation :: stack) :
    let closed := SizedBufferHeap.close state.heap.metadata token
    let next : State := ⟨⟨closed,state.heap.cell⟩,.evaluate continuation,
      .lendContinuation object origin resultOrigin value :: stack,state.pending⟩
    step state = some (next,some (.legacy (.heap (.close token)))) ∧
      closed.heap.lease token = none ∧
      (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
      ReaderInventory closed (readerFrames next.activeStack) := by
  have entries : ReaderInventory state.heap.metadata
      ((token,object,name) :: readerFrames (stack ++ state.pending.flatMap Prod.snd)) := by
    simpa only [State.activeStack,stackShape,List.cons_append,readerFrames,List.filterMap_cons,Frame.reader?]
      using inventory
  obtain ⟨leased,remaining⟩ := entries.finish
  refine ⟨?_,?_,?_,?_⟩
  · simp only [step,returned,stackShape,returnAction,executeLegacy,execute,leased,ite_true,Option.map_some]
  · simp [SizedBufferHeap.close,HeapLeases.put]
  · intro other different
    simp [SizedBufferHeap.close,HeapLeases.put,different]
  · simpa only [State.activeStack,List.cons_append,readerFrames,List.filterMap_cons,Frame.reader?] using remaining

/-- The real variable return and reader close leave the indexed cells and
suspended continuations untouched. The initial run supplies all heap and
lease premises of the close. -/
theorem reachable_lend_variable_close (term : Term) (fuel : Nat)
    (evaluating : (run fuel (initial term)).state.control = .evaluate code)
    (shape : code.term = .var index) (stored : code.values[index]? = some (some value))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin continuation :: stack) :
    let state := (run fuel (initial term)).state
    let closed := SizedBufferHeap.close state.heap.metadata token
    run 2 state = ⟨⟨⟨closed,state.heap.cell⟩,.evaluate continuation,
      .lendContinuation object origin resultOrigin value :: stack,state.pending⟩,
      [.legacy (.heap (.close token))],2⟩ ∧
      closed.heap.lease token = none ∧
      (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
      ReaderInventory closed (readerFrames (stack ++ state.pending.flatMap Prod.snd)) := by
  let state := (run fuel (initial term)).state
  let returned : State := { state with control := .returned value }
  have lookup : step state = some (returned,none) := by
    simp only [state,returned,step,evaluating,shape,evaluateAction,stored,executeLegacy,execute,Option.map_none]
  have inventory : ReaderInventory returned.heap.metadata (readerFrames returned.activeStack) :=
    (initial_run_invariant term fuel).2
  obtain ⟨closed,absent,others,remaining⟩ := lend_close_step (state := returned) inventory rfl stackShape
  refine ⟨?_,absent,others,?_⟩
  · change run 2 state = _
    rw [run,lookup]
    change Result.mk (run 1 returned).state (run 1 returned).events ((run 1 returned).steps+1) = _
    rw [run,closed]
    rfl
  · simpa only [State.activeStack,List.cons_append,readerFrames,List.filterMap_cons,Frame.reader?] using remaining

/-- Once an issued reader token is retired, no suffix of indexed execution
can restore it, including after later allocations or new readers. -/
theorem reachable_run_closed_lease (term : Term) (prefixFuel suffixFuel : Nat)
    (old : token < (run prefixFuel (initial term)).state.heap.metadata.heap.nextLease)
    (closed : (run prefixFuel (initial term)).state.heap.metadata.heap.lease token = none) :
    let after := (run suffixFuel (run prefixFuel (initial term)).state).state.heap.metadata.heap
    token < after.nextLease ∧ after.lease token = none :=
  HeapLeases.expired_steps old closed
    (SizedBufferHeap.steps_project (run_lifecycle (initial_run_invariant term prefixFuel).1 suffixFuel))

namespace Examples

private def bufferOne := Term.buffer (.natural 1)
private def firstCell := Term.decide (.natural 0) (.natural 1)
private def releaseOne : Term := .lam false .i64 (.lam false bufferOne (.free (.var 0) (.var 1)))

private def closeInsideStore : Term :=
  let inner := Term.lend (.alloc (.natural 1) (.integer 0))
    (.lam false (.ref bufferOne) (.app (.lam false .i64 (.var 0)) (.integer 9))) releaseOne
  let write := Term.store (.alloc (.natural 1) (.integer 0)) (.natural 0) inner firstCell
  let outer := Term.lend (.var 0) (.lam false (.ref bufferOne) (.free write (.integer 5))) releaseOne
  .app (.lam false bufferOne outer) (.alloc (.natural 1) (.integer 7))

/-- The reader inside a Store fill returns a variable and closes token 1
while the outer reader's token 0 remains active in the suspended Store stack. -/
theorem close_inside_store_preserves_suspended_reader :
    LoanTyping.MixedProgram.checkDeclaration 32 64 .empty ⟨.i64,closeInsideStore⟩ =
      some ⟨.i64,closeInsideStore⟩ ∧
    let result := run 2 (run 38 (initial closeInsideStore)).state
    result.events = [.legacy (.heap (.close 1))] ∧
      result.state.heap.metadata.heap.lease 1 = none ∧
      result.state.heap.metadata.heap.lease 0 = some 0 ∧
      result.state.stack.length = 1 ∧
      readerFrames (result.state.pending.flatMap Prod.snd) = [(0,0,some 1)] := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
