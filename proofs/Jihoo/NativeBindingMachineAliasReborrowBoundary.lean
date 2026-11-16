import Jihoo.NativeBindingMachineCanonicalView

/-! A regression for returned-owner aliases. The checker canonically identifies
both aliases. A subsequent Lend through the new alias and Borrow through the
old alias must select a reader of the same concrete object despite different
lexical keys. This checks the source machine, not native implementation fidelity. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.AliasReborrowBoundary

def buffer : Term := .buffer (.natural 1)
def referenceReader : Term := .index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 1))
def oldAliasReader : Term := .index (.borrow (.var 3)) (.natural 0) (.decide (.natural 0) (.natural 1))
def release : Term := .lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
def again : Term := .lend (.var 0) (.lam false (.ref buffer) oldAliasReader) release
def source : Term := .lend (.var 0) (.lam false (.ref buffer) referenceReader)
  (.lam false .i64 (.lam false buffer again))
def program : Term := .app (.lam false buffer source) (.alloc (.natural 1) (.integer 7))

theorem source_admitted : LoanTyping.MixedProgram.checkDeclaration 256 512 .empty
    ⟨.i64,program⟩ = some ⟨.i64,program⟩ := by cbv

theorem runtime_alias_return : observe (run 100 (initial program)) = .integer 7 := by cbv

theorem runtime_alias_events : eventsHeap (run 100 (initial program)).events =
    [.alloc 0 1 (encodeInteger 7),.beginLease 0 0,.read 0 0 (encodeInteger 7),.close 0,
      .beginLease 1 0,.read 1 0 (encodeInteger 7),.close 1,.free 0] := by cbv

theorem runtime_alias_released : (run 100 (initial program)).state.heap.heap.live 0 = false := by cbv

theorem runtime_alias_no_leases (token : Nat) :
    (run 100 (initial program)).state.heap.heap.lease token = none :=
  initial_run_empty_stack_no_leases program 100 (by cbv) token

end Jihoo.NativeKernel.Environment.BindingMachine.AliasReborrowBoundary
