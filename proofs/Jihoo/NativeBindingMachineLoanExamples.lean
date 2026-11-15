import Jihoo.NativeBindingMachineLoans
import Jihoo.NativeLoanMixedPreservationExamples

namespace Jihoo.NativeKernel.Environment.BindingMachine.LoanExamples
open LoanTyping CheckerExamples

def explicitCall : Term := .app MixedPreservationExamples.function allocatedOwner

theorem explicit_named_borrow_admitted : ResourceQuantity.checkClosed 64 128 .empty explicitCall .i64 = true := by cbv

theorem explicit_named_borrow_computes : observe (run 128 (initial explicitCall)) = .integer 0 := by cbv

theorem explicit_named_borrow_events : eventsHeap (run 128 (initial explicitCall)).events =
    [.alloc 0 2 (encodeInteger 0),.beginLease 0 0,.read 0 0 (encodeInteger 0),.close 0,.free 0] := by cbv

def innerReader : Term := .lam false (.ref buffer)
  (.arith .add (.index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 2)))
    (.index (.borrow (.var 2)) (.natural 0) (.decide (.natural 0) (.natural 2))))
def nestedReader : Term := .lam false (.ref buffer)
  (.lend (.alloc (.natural 2) (.integer 7)) innerReader continuation)
def nestedCall : Term := .app (.lam false buffer (.lend (.var 0) nestedReader continuation)) allocatedOwner

theorem nested_active_readers_admitted :
    ResourceQuantity.checkClosed 96 128 .empty nestedCall .i64 = true := by cbv

theorem nested_active_readers_compute : observe (run 256 (initial nestedCall)) = .integer 7 := by cbv

/-- The second read uses the outer named owner while the inner reader is
still active; both leases close before their respective owner is released. -/
theorem nested_active_readers_events : eventsHeap (run 256 (initial nestedCall)).events =
    [.alloc 0 2 (encodeInteger 0),.beginLease 0 0,
      .alloc 1 2 (encodeInteger 7),.beginLease 1 1,
      .read 1 0 (encodeInteger 7),.read 0 0 (encodeInteger 0),
      .close 1,.free 1,.close 0,.free 0] := by cbv

def freshReader : Term := .lam false (.ref buffer)
  (.alloc (.natural 1) (.index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 2))))
def twoOwnerContinuation : Term := .lam false (.buffer (.natural 1))
  (.lam false buffer (.free (.var 1) (.free (.var 0) (.natural 7))))
def ownedResultCall : Term := .app (.lam false buffer
  (.lend (.var 0) freshReader twoOwnerContinuation)) allocatedOwner

theorem fresh_owned_reader_result_admitted :
    ResourceQuantity.checkClosed 96 128 .empty ownedResultCall .u64 = true := by cbv

theorem fresh_owned_reader_result_computes : observe (run 256 (initial ownedResultCall)) = .natural 7 := by cbv

theorem fresh_owned_result_has_separate_identity : eventsHeap (run 256 (initial ownedResultCall)).events =
    [.alloc 0 2 (encodeInteger 0),.beginLease 0 0,.read 0 0 (encodeInteger 0),
      .alloc 1 1 (encodeInteger 0),.close 0,.free 1,.free 0] := by cbv

def escapedReference : Term := .lend allocatedOwner (.lam false (.ref buffer) (.var 0))
  (.lam false (.ref buffer) (.lam false buffer
    (.strict (.index (.var 1) (.natural 0) (.decide (.natural 0) (.natural 2)))
      (.free (.var 0) (.integer 0)))))

theorem escaping_reference_rejected :
    (LoanTyping.Checker.infer 96 .empty [] [] false escapedReference).isSome = false := by cbv

theorem untyped_escape_reports_closed_lease :
    observe (run 256 (initial escapedReference)) = .fault .closedLease := by cbv

theorem all_nested_prefixes_have_valid_heap (fuel : Nat) :
    SizedBufferHeap.Valid (run fuel (initial nestedCall)).state.heap := initial_run_heap_valid _ _

end Jihoo.NativeKernel.Environment.BindingMachine.LoanExamples
