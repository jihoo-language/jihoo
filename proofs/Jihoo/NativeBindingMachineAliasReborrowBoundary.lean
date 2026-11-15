import Jihoo.NativeBindingMachineCanonicalView

/-! A concrete boundary of the current named-Borrow runtime. After an owner is
returned, the checker canonically identifies both aliases. A subsequent Lend
through the new alias records a new lexical key; Borrow through the old alias
still asks for the earlier key. This must be repaired before full progress can
be claimed for the binding-retaining model. It is not a native-execution claim. -/
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

theorem runtime_alias_fault : observe (run 100 (initial program)) = .fault .inactiveBorrow := by cbv

end Jihoo.NativeKernel.Environment.BindingMachine.AliasReborrowBoundary
