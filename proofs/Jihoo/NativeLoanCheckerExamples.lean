import Jihoo.NativeLoanCheckerSoundness

namespace Jihoo.NativeKernel.Environment.LoanTyping.CheckerExamples

def buffer : Term := .buffer (.natural 2)
def ownerContext : Context := [⟨buffer,false⟩]
def readerBody : Term := .index (.var 0) (.natural 0) (.decide (.natural 0) (.natural 2))
def reader : Term := .lam false (.ref buffer) readerBody
def continuation : Term := .lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
def source : Term := .lend (.var 0) reader continuation
def allocatedOwner : Term := .alloc (.natural 2) (.integer 0)
def closedFunction : Term := .lam false buffer source
def closedCall : Term := .app closedFunction allocatedOwner

theorem dependent_code_checked : Checker.check 48 empty [] ownerContext false source .i64 = true := by cbv

theorem dependent_code_typed : HasType empty [] ownerContext false source .i64 :=
  Checker.check_sound dependent_code_checked

theorem closed_function_checked :
    Checker.check 64 empty [] [] false closedFunction (.pi false buffer .i64) = true := by cbv

theorem closed_call_checked : Checker.check 64 empty [] [] false closedCall .i64 = true := by cbv

theorem closed_call_typed : HasType empty [] [] false closedCall .i64 :=
  Checker.check_sound closed_call_checked

theorem generic_allocated_owner_checked :
    Checker.check 48 empty [] [] false (.lend allocatedOwner reader continuation) .i64 = true := by cbv

theorem standalone_code_borrow_rejected :
    Checker.infer 32 empty [] ownerContext false (.borrow (.var 0)) = none := by cbv

theorem entered_reader_code_borrow_checked :
    Checker.check 32 empty (Loans.enter ownerContext.length 0 []) ownerContext false
      (.borrow (.var 0)) (.ref buffer) = true := by cbv

theorem reader_exit_revokes_borrow :
    Checker.infer 32 empty (Loans.exit (Loans.enter ownerContext.length 0 []))
      ownerContext false (.borrow (.var 0)) = none := by cbv

theorem ghost_value_borrow_checked :
    Checker.check 32 empty [] [] true (.borrow allocatedOwner) (.ref buffer) = true := by cbv

theorem reader_reference_cannot_outlive :
    Checker.infer 48 empty [] ownerContext false
      (.lend (.var 0) (.lam false (.ref buffer) (.var 0)) continuation) = none := by cbv

theorem returned_owner_cannot_borrow_after_exit :
    Checker.infer 48 empty [] ownerContext false
      (.lend (.var 0) reader
        (.lam false .i64 (.lam false buffer (.index (.borrow (.var 0)) (.natural 0)
          (.decide (.natural 0) (.natural 2)))))) = none := by cbv

end Jihoo.NativeKernel.Environment.LoanTyping.CheckerExamples
