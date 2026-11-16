import Jihoo.NativeBindingMachineComputedAllocation
import Jihoo.NativeBindingMachineRunAlgebra

/-! A closed Loan64/resource-admitted call computes its count by Free and
addition before entering the dependent allocation body. Allocation/result
interpretation uses the general value-closing theorem, not a supplied output.
The source application type and its actual-value instance are kept distinct. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.ComputedAllocationExamples
open CodeKinds

def function : Term := .lam false .u64 (.alloc (.var 0) (.integer 7))
def countEffect : Term := .free (.alloc (.natural 1) (.integer (-2)))
  (.uadd (.natural 1) (.natural 1))
def program : Term := .app function countEffect
def sourceType : Term := .buffer countEffect

theorem program_admitted : LoanTyping.ResourceQuantity.checkClosed 128 256 .empty program sourceType = true := by cbv

private theorem functionTyped : LoanClosingTyped .empty [] false (.initial function) Term.var
    (.pi false .u64 (.buffer (.var 0))) :=
  LoanClosingTyped.initial (LoanTyping.Checker.check_sound
    (show LoanTyping.Checker.check 64 .empty [] [] false function (.pi false .u64 (.buffer (.var 0))) = true by cbv))

private theorem reached : (run 15 (initial program)).state.control = .returned (.natural 2) := by cbv

private theorem saved : (run 15 (initial program)).state.stack =
    [.argument (.closure false .u64 (.alloc (.var 0) (.integer 7)) [] Term.var []) countEffect] := by cbv

private theorem counter : (run 15 (initial program)).state.heap.heap.nextObject = 1 := by cbv

/-- The count was computed with an allocation/release effect and retained as
source provenance. The new Buffer is interpreted at the actual argument 2;
no conversion of `countEffect` to 2 is a premise. -/
theorem program_allocates_by_value :
    observe (run 21 (initial program)) = .owner 1 ∧
      BufferValue .empty (run 21 (initial program)).state.heap (.owner 1) (.buffer (.natural 2)) := by
  have result := reachable_computed_allocation (domain := .u64) (context := []) (origins := Term.var)
    (captured := []) (meanings := Term.var) (stack := []) program 15 .empty functionTyped reached saved
  have fits : 2*8+8 < 2^64 := by decide
  simp only [fits,↓reduceIte] at result
  obtain ⟨entryTyped,provenance,freshCaptures,buffer,executed⟩ := result
  have composed := run_add 15 6 (initial program)
  dsimp only at composed
  rw [executed] at composed
  constructor
  · simpa only [observe,counter] using congrArg observe composed
  · have heapSame := congrArg (fun result => result.state.heap) composed
    change (run 21 (initial program)).state.heap =
      SizedBufferHeap.allocate (run 15 (initial program)).state.heap 2 (encodeInteger 7) at heapSame
    rw [heapSame]
    simpa only [counter] using buffer

def curriedFunction : Term := .lam false .u64 (.lam false .i64 (.alloc (.var 1) (.var 0)))
def fillEffect : Term := .free (.alloc (.natural 1) (.integer 0))
  (.arith .add (.integer (-2)) (.integer (-3)))
def curriedProgram : Term := .app (.app curriedFunction countEffect) fillEffect

theorem curried_program_admitted :
    LoanTyping.ResourceQuantity.checkClosed 128 256 .empty curriedProgram sourceType = true := by cbv

private theorem curriedTyped : LoanClosingTyped .empty [] false (.initial curriedFunction) Term.var
    (.pi false .u64 (.pi false .i64 (.buffer (.var 1)))) :=
  LoanClosingTyped.initial (LoanTyping.Checker.check_sound
    (show LoanTyping.Checker.check 64 .empty [] [] false curriedFunction
      (.pi false .u64 (.pi false .i64 (.buffer (.var 1)))) = true by cbv))

private theorem secondTyped : LoanClosingTyped .empty [] false
    ⟨.lam false .i64 (.alloc (.var 1) (.var 0)),[⟨.u64,false⟩],consValues countEffect Term.var,[some (.natural 2)]⟩
    (consValues (.natural 2) Term.var) (.pi false .i64 (.buffer (.natural 2))) :=
  two_scalar_second_entry_typing .empty curriedTyped (by decide) countEffect

private theorem integerReached : (run 31 (initial curriedProgram)).state.control = .returned (.integer (-5)) := by cbv

private theorem secondSaved : (run 31 (initial curriedProgram)).state.stack =
    [.argument (.closure false .i64 (.alloc (.var 1) (.var 0)) [⟨.u64,false⟩]
      (consValues countEffect Term.var) [some (.natural 2)]) fillEffect] := by cbv

private theorem secondCounter : (run 31 (initial curriedProgram)).state.heap.heap.nextObject = 2 := by cbv

/-- A computed callee captures the effectfully computed size, then receives
an effectfully computed signed fill. Both source origins remain intact. -/
theorem curried_program_allocates_by_value :
    observe (run 37 (initial curriedProgram)) = .owner 2 ∧
      BufferValue .empty (run 37 (initial curriedProgram)).state.heap (.owner 2) (.buffer (.natural 2)) ∧
      (run 37 (initial curriedProgram)).state.heap.heap.payload 2 = encodeInteger (-5) := by
  have result := reachable_two_scalar_allocation (domain := .i64) (context := [⟨.u64,false⟩])
    (origins := consValues countEffect Term.var) (captured := []) (meanings := Term.var) (stack := [])
    curriedProgram 31 .empty secondTyped integerReached secondSaved
  have fits : 2*8+8 < 2^64 := by decide
  simp only [fits,↓reduceIte] at result
  obtain ⟨entryTyped,provenance,buffer,executed⟩ := result
  have composed := run_add 31 6 (initial curriedProgram)
  dsimp only at composed
  rw [executed] at composed
  have heapSame := congrArg (fun result => result.state.heap) composed
  change (run 37 (initial curriedProgram)).state.heap =
    SizedBufferHeap.allocate (run 31 (initial curriedProgram)).state.heap 2 (encodeInteger (-5)) at heapSame
  refine ⟨?_,?_,?_⟩
  · simpa only [observe,secondCounter] using congrArg observe composed
  · rw [heapSame]
    simpa only [secondCounter] using buffer
  · rw [heapSame]
    simp only [SizedBufferHeap.allocate,HeapLeases.put,secondCounter,ite_true]

end Jihoo.NativeKernel.Environment.BindingMachine.ComputedAllocationExamples
