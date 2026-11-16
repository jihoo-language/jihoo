import Jihoo.NativeBindingMachineLendOrigins
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

/-- The erased equality is valid only after the reader parameter has been
specialized to Borrow of the original owner. Runtime skips this evidence. -/
def ghostCount (owner : Term) : Term := .free owner (.natural 0)
def specializedBody : Term := .app
  (.lam true (.eq (ghostCount (.deref (.var 0))) (ghostCount (.var 1))) (.integer 7))
  (.refl (ghostCount (.var 1)))
def specializedReader : Term := .lam false (.ref buffer) specializedBody
def specializedSource : Term := .lend (.var 0) specializedReader continuation
def specializedCall : Term := .app (.lam false buffer specializedSource) allocatedOwner

theorem specialized_callback_admitted :
    ResourceQuantity.checkClosed 128 192 .empty specializedCall .i64 = true := by cbv

theorem unspecialized_callback_rejected :
    (LoanTyping.Checker.infer 96 .empty [] ownerContext false specializedReader).isSome = false := by cbv

theorem specialized_callback_computes : observe (run 192 (initial specializedCall)) = .integer 7 := by cbv

/-- The continuation receives the actual specialized body origin, whose
source typing can be derived; no arbitrary-argument callback typing is used. -/
theorem specialized_callback_result_origin : activationOrigins (run 192 (initial specializedCall)).events =
    [allocatedOwner,.borrow allocatedOwner,.refl (ghostCount allocatedOwner),
      (Lending.read (.var 0) specializedBody).subst (CodeKinds.consValues allocatedOwner Term.var),allocatedOwner] := by cbv

def specializedCode : Code := enter false buffer specializedSource [] Term.var []
  allocatedOwner (some (.owner 0))

theorem specialized_original_body_source_typed :
    LoanSourceTyped .empty [] false specializedCode .i64 := by
  have function : LoanTyping.HasType .empty [] [] false
      (.lam false buffer specializedSource) (.pi false buffer .i64) :=
    LoanTyping.Checker.check_sound (by cbv : LoanTyping.Checker.check 128 .empty [] [] false
      (.lam false buffer specializedSource) (.pi false buffer .i64) = true)
  have argument : LoanTyping.HasType .empty [] [] false allocatedOwner buffer :=
    .alloc (.natural (by decide)) (.integer (by decide) (by decide))
  have entered := enter_loan_source_typed (LoanTyping.MixedProgram.History.empty)
    (LoanSourceTyped.initial function) (LoanSourceTyped.initial argument) (some (.owner 0))
  simpa only [specializedCode,Code.initial,Code.origin,Term.subst_id,Term.subst,substArgs] using entered.2

/-- The general source-to-actual-binding theorem derives this endpoint type
for a callback which the standalone checker rejects before specialization. -/
theorem specialized_continuation_original_type (result : Value) :
    LoanTyping.HasType .empty [] [] true
      (enter false buffer (.free (.var 0) (.var 1)) (⟨.i64,false⟩ :: specializedCode.context)
        (CodeKinds.consValues ((Lending.read (.var 0) specializedBody).subst specializedCode.origins)
          specializedCode.origins)
        (some result :: specializedCode.values) ((Term.var 0).subst specializedCode.origins)
        (some (.owner 0))).origin .i64 :=
  typed_explicit_continuation_origin LoanTyping.MixedProgram.History.empty
    specialized_original_body_source_typed rfl 0 result

end Jihoo.NativeKernel.Environment.BindingMachine.LoanExamples
