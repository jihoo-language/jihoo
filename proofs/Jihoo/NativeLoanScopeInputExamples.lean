import Jihoo.NativeLoanCheckerExamples
import Jihoo.NativeLoanTypingInput

/-! Scope is checked independently of conversion, including arguments erased
while comparing the returned-owner annotation. Raw typing is not used as a
replacement for the source parser's complete lexical scope validation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ScopeInputExamples
open CheckerExamples

def unscopedAgain : Term := .app (.lam false .u64 buffer) (.var 99)
def unscopedSource : Term := .lam false buffer
  (.lend (.var 0) reader
    (.lam false .i64 (.lam false unscopedAgain (.free (.var 0) (.var 1)))))
def unscopedDeclaration : GlobalDeclaration := ⟨.pi false buffer .i64,unscopedSource⟩

theorem raw_typing_does_not_replace_scope_validation :
    Checker.check 64 empty [] [] false unscopedSource unscopedDeclaration.type = true := by cbv

theorem complete_source_scope_rejects : ¬ unscopedSource.Scoped 0 := by
  intro scopeWitness
  have checked := scopeCheck_complete scopeWitness
  have rejected : scopeCheck 0 unscopedSource = false := by cbv
  rw [rejected] at checked
  cases checked

theorem exact_input_checks_erased_annotation_scope :
    NativeLoanTypingInput.checkDeclaration 64 unscopedDeclaration = false := by cbv

end Jihoo.NativeKernel.Environment.LoanTyping.ScopeInputExamples
