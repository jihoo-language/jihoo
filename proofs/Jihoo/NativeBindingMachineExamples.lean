import Jihoo.NativeBindingMachineTyping
import Jihoo.NativeCallBindingStoreExamples

namespace Jihoo.NativeKernel.Environment.BindingMachine.Examples
open CodeKinds ContextQuantity CallReplay Jihoo.Quantity
open CallResourceContractExamples ContextReplayExamples ClosingTelescopeExamples

theorem owned_call_computes : observe (run 64 (initial ownedCall)) = .natural 7 := by cbv

/-- The actual owner argument allocates once and is freed once; source beta
substitution never copies its allocation into the retained function body. -/
theorem owned_call_exact_heap_events : eventsHeap (run 64 (initial ownedCall)).events =
    [.alloc 0 2 (encodeInteger 0),.free 0] := by cbv

theorem owned_call_original_bodies : activationBodies (run 64 (initial ownedCall)).events =
    [.lam false .u64 ownedBody,ownedBody] := by cbv

theorem owned_call_original_argument_origins : activationOrigins (run 64 (initial ownedCall)).events =
    [allocated,.natural 7] := by cbv

theorem owned_call_heap_released :
    (run 64 (initial ownedCall)).state.heap.heap.nextObject = 1 ∧
      (run 64 (initial ownedCall)).state.heap.heap.live 0 = false := by cbv

/-- The exact source slots from the original accepted call type the entered
body's provenance. Actual runtime values remain separate from source typing. -/
theorem owned_body_source_store_typed :
    ∃ bodyType : Term, SourceTyped .empty false
      ⟨ownedBody,ownedOpened.context,pushValues Term.var [allocated,.natural 7],
        [some (.natural 7),some (.owner 0)]⟩
      (bodyType.subst (pushValues Term.var [allocated,.natural 7])) := by
  obtain ⟨bodyType,typed⟩ := CodeRetentionExamples.actual_owned_body_code_typed
  refine ⟨bodyType,?_,CallBindingStoreExamples.actual_owned_exact_store,bodyType,typed,.refl _⟩
  exact .cons (.cons .nil (Checker.binder_sound (by cbv : Checker.binder 64 .empty [] false owner = some (.type 0))))
    (Checker.binder_sound (by cbv : Checker.binder 64 .empty [⟨owner,false⟩] false .u64 = some (.type 0)))

theorem owned_call_all_prefixes_heap_valid (fuel : Nat) :
    SizedBufferHeap.Valid (run fuel (initial ownedCall)).state.heap := initial_run_heap_valid _ _

theorem computed_callee_computes :
    observe (run 64 (initial CallBindingStoreExamples.computedCall)) = .natural 7 := by cbv

/-- Its source head has no opened lambda; the machine creates the chosen
closure from the actual conditional branch and then invokes that closure. -/
theorem computed_callee_actual_body :
    activationBodies (run 64 (initial CallBindingStoreExamples.computedCall)).events = [.var 0] := by cbv

/-- The erased ghost-only Borrow expression is never evaluated, so it causes
neither an unsupported-operation fault nor an allocation event. -/
theorem ghost_only_erased_argument_skipped :
    observe (run 128 (initial erasedCall)) = .natural 7 ∧
      eventsHeap (run 128 (initial erasedCall)).events = [] := by cbv

def unusedEffectfulFunction : Term := .lam false .u64 (.free allocated (.var 0))
def functionArgumentCall : Term := .app (.lam false (.pi false .u64 .u64) (.natural 7)) unusedEffectfulFunction

theorem function_argument_source_admitted : checkResource 128 .empty functionArgumentCall = true := by cbv

/-- Lambda bodies run when invoked, so allocating/freeing code inside a
function-valued argument does not execute when the argument value is passed. -/
theorem function_argument_body_not_run :
    observe (run 64 (initial functionArgumentCall)) = .natural 7 ∧
      eventsHeap (run 64 (initial functionArgumentCall)).events = [] := by cbv

def doubleFree : Term := .app (.lam false owner (.free (.var 0) (.free (.var 0) (.natural 0)))) allocated

theorem double_free_source_rejected : checkResource 128 .empty doubleFree = false := by cbv

/-- Faulting executions still emit only valid heap events. The second free
reports the dead owner and emits no invalid free event. -/
theorem double_free_explicit_fault :
    observe (run 64 (initial doubleFree)) = .fault .deadOwner ∧
      eventsHeap (run 64 (initial doubleFree)).events = [.alloc 0 2 (encodeInteger 0),.free 0] := by cbv

theorem signed_minimum_payload : encodeInteger (-(2^63)) = 0 := by decide
theorem signed_maximum_payload : encodeInteger (2^63-1) = 2^64-1 := by decide

end Jihoo.NativeKernel.Environment.BindingMachine.Examples
