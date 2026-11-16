import Jihoo.NativeBindingMachineDynamicIndex
import Jihoo.NativeBindingMachineRunAlgebra

namespace Jihoo.NativeKernel.Environment.BindingMachine.DynamicIndexExamples
open LoanTyping

def reader : Term := .lam false (.ref (.buffer (.var 2)))
  (.ifLt (.var 2) (.var 3) (dynamicRead 1 2) (.integer 0))
def continuation : Term := .lam false .i64
  (.lam false (.buffer (.var 3)) (.free (.var 0) (.var 1)))
def function : Term := .lam false .u64 (.lam false .u64
  (.app (.lam false (.buffer (.var 1)) (.lend (.var 0) reader continuation))
    (.alloc (.var 1) (.integer 7))))
def signature : Term := .pi false .u64 (.pi false .u64 .i64)
def program (count index : Nat) : Term := .app (.app function (.natural count)) (.natural index)

theorem source_checked : ResourceQuantity.checkClosed 128 256 .empty function signature = true := by cbv

theorem source_typed : LoanTyping.HasType .empty [] [] false function signature :=
  (ResourceQuantity.checkClosed_sound source_checked).2.2.1

/-- Full source typing for all bounded runtime scalar arguments, rather than
checking one closed count/index fixture. -/
theorem program_typed (count index : Nat) (countBound : count < 2^64) (indexBound : index < 2^64) :
    LoanTyping.HasType .empty [] [] false (program count index) .i64 := by
  have first : LoanTyping.HasType .empty [] [] false (.app function (.natural count)) (.pi false .u64 .i64) := by
    simpa only [signature,Term.subst,substArgs,Op.binders,liftSub] using
      (LoanTyping.HasType.app source_typed (LoanTyping.HasType.natural countBound)
        (Or.inr ⟨.u64,.refl _,by cbv,Or.inl (by cbv)⟩))
  have next := LoanTyping.HasType.app first (LoanTyping.HasType.natural indexBound) (Or.inr ⟨.u64,.refl _,by cbv,Or.inl (by cbv)⟩)
  simpa only [program,signature,Term.subst,substArgs,Op.binders,liftSub] using next

set_option linter.unusedSimpArgs false in
theorem all_bounded_inputs_compute (count index : Nat) (countBound : count < 2^64) (indexBound : index < 2^64)
    (allocationFits : count * 8 + 8 < 2^64) :
    observe (run 128 (initial (program count index))) = .integer (if index < count then 7 else 0) := by
  have seven : ValueReduction.signed64 7 := by decide
  have zero : ValueReduction.signed64 0 := by decide
  by_cases compared : index < count
  all_goals simp only [program,function,reader,continuation,dynamicRead,initial]
  all_goals repeat' (
    rw [observe_run_succ]
    simp only [step,action,evaluateAction,returnAction,applyValue,enter,Code.initial,Code.child,Code.origin,
      branchCode,execute,countBound,indexBound,allocationFits,compared,freeGuard,activeLease,readerFor,Frame.reader?,
      SizedBufferHeap.empty,HeapLeases.empty,SizedBufferHeap.allocate,SizedBufferHeap.lend,
      SizedBufferHeap.close,SizedBufferHeap.release,HeapLeases.put,seven,zero,encode_decode_integer seven,
      List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,List.length_cons,List.length_nil,
      Option.map_some,Option.map_none,Option.orElse_none,Option.orElse_some,bind,Option.bind,
      and_true,true_and,and_self,ite_true,
      Bool.false_eq_true,Bool.true_eq_false,decide_true,decide_false,↓reduceIte]
  )
  all_goals rfl

set_option linter.unusedSimpArgs false in
theorem all_bounded_inputs_events (count index : Nat) (countBound : count < 2^64) (indexBound : index < 2^64)
    (allocationFits : count * 8 + 8 < 2^64) :
    eventsHeap (run 128 (initial (program count index))).events =
      [.alloc 0 count (encodeInteger 7),.beginLease 0 0] ++
      (if index < count then [.read 0 index (encodeInteger 7)] else []) ++ [.close 0,.free 0] := by
  have seven : ValueReduction.signed64 7 := by decide
  have zero : ValueReduction.signed64 0 := by decide
  by_cases compared : index < count
  all_goals simp only [program,function,reader,continuation,dynamicRead,initial]
  all_goals repeat' (
    rw [heap_events_run_succ]
    simp only [step,action,evaluateAction,returnAction,applyValue,enter,Code.initial,Code.child,Code.origin,
      branchCode,execute,eventHeap,countBound,indexBound,allocationFits,compared,freeGuard,activeLease,readerFor,Frame.reader?,
      SizedBufferHeap.empty,HeapLeases.empty,SizedBufferHeap.allocate,SizedBufferHeap.lend,
      SizedBufferHeap.close,SizedBufferHeap.release,HeapLeases.put,seven,zero,encode_decode_integer seven,
      List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,List.length_cons,List.length_nil,
      Option.map_some,Option.map_none,Option.orElse_none,Option.orElse_some,bind,Option.bind,
      and_true,true_and,and_self,ite_true,List.nil_append,List.append_nil,List.cons_append,Option.toList,
      Bool.false_eq_true,Bool.true_eq_false,decide_true,decide_false,↓reduceIte]
  )
  all_goals rfl


private theorem read_step_unchanged (step : SizedBufferHeap.Step before (.read token index value) after) :
    after = before := by cases step; rfl

/-- The computed exact trace and the machine's general heap-step theorem
leave no live allocation or outstanding lease, for every bounded input. -/
theorem all_bounded_inputs_no_leak (count index : Nat) (countBound : count < 2^64) (indexBound : index < 2^64)
    (allocationFits : count * 8 + 8 < 2^64) :
    (∀ object, (run 128 (initial (program count index))).state.heap.heap.live object = false) ∧
      (∀ token, (run 128 (initial (program count index))).state.heap.heap.lease token = none) := by
  have trace := run_heap_steps (state := initial (program count index)) SizedBufferHeap.empty_valid 128
  rw [all_bounded_inputs_events count index countBound indexBound allocationFits] at trace
  generalize finalShape : (run 128 (initial (program count index))).state.heap = finalHeap at trace ⊢
  by_cases compared : index < count
  all_goals simp only [compared,↓reduceIte,List.cons_append,List.nil_append,List.append_nil] at trace
  case pos =>
    cases trace with
    | cons first rest =>
      cases first
      cases rest with
      | cons second rest =>
        cases second
        cases rest with
        | cons read rest =>
          cases (read_step_unchanged read)
          cases rest with
          | cons close rest =>
            cases close
            cases rest with
            | cons release rest =>
              cases release
              cases rest
              constructor <;> intro queried <;>
                  simp [initial,SizedBufferHeap.empty,HeapLeases.empty,SizedBufferHeap.allocate,SizedBufferHeap.lend,
                    SizedBufferHeap.close,SizedBufferHeap.release,HeapLeases.put]
  case neg =>
    cases trace with
    | cons first rest =>
      cases first
      cases rest with
      | cons second rest =>
        cases second
        cases rest with
        | cons close rest =>
          cases close
          cases rest with
          | cons release rest =>
            cases release
            cases rest
            constructor <;> intro queried <;>
              simp [initial,SizedBufferHeap.empty,HeapLeases.empty,SizedBufferHeap.allocate,SizedBufferHeap.lend,
                SizedBufferHeap.close,SizedBufferHeap.release,HeapLeases.put]

end Jihoo.NativeKernel.Environment.BindingMachine.DynamicIndexExamples
