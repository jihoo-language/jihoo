import Jihoo.NativeLoanGlobalChecking
import Jihoo.NativeLoanTypeUniqueness
import Jihoo.NativeLoanCheckerExamples
import Jihoo.NativeLoanScopeInputExamples

namespace Jihoo.NativeKernel.Environment.LoanTyping.GlobalExamples
open CheckerExamples

def functionDeclaration : GlobalDeclaration := ⟨.pi false buffer .i64,closedFunction⟩
def callDeclaration : GlobalDeclaration := ⟨.i64,.app (.node (.global 0) []) allocatedOwner⟩
def expandedCall : GlobalDeclaration := ⟨.i64,closedCall⟩
def sources : List GlobalDeclaration := [functionDeclaration,callDeclaration]
def result : Environment := ⟨#[functionDeclaration,expandedCall],#[]⟩

theorem actual_sequential_loan_program_checked : Program.checkProgram 64 sources = some result := by cbv

theorem actual_sequential_loan_program_sound : Program.ProgramChecked sources result :=
  Program.checkProgram_sound actual_sequential_loan_program_checked

theorem actual_sequential_loan_program_world : UnifiedProgram.EnvWellFormed result :=
  actual_sequential_loan_program_sound.wellFormed

theorem actual_global_call_checked_in_prefix :
    Program.checkDeclaration 64 ⟨#[functionDeclaration],#[]⟩ callDeclaration = some expandedCall := by cbv

theorem actual_global_call_has_original_result_type : HasType ⟨#[functionDeclaration],#[]⟩ [] [] false
    closedCall .i64 := by
  have checked := Program.checkDeclaration_sound actual_global_call_checked_in_prefix
  obtain ⟨sort,typeTyped,valueTyped⟩ := checked.valid.typing
  have exactSort : sort = .type 0 := by
    have principal : HasType ⟨#[functionDeclaration],#[]⟩ [] [] true .i64 (.univ 0) := .i64
    have prior : Program.ProgramChecked [functionDeclaration] ⟨#[functionDeclaration],#[]⟩ :=
      Program.checkProgram_sound (by cbv : Program.checkProgram 64 [functionDeclaration] = some ⟨#[functionDeclaration],#[]⟩)
    exact (typeTyped.unique prior.wellFormed principal).sort_injective prior.wellFormed.admissible
  subst sort
  exact valueTyped

theorem forward_reference_rejected : Program.checkProgram 64
    [⟨.i64,.node (.global 1) []⟩,⟨.i64,.integer 0⟩] = none := by cbv

theorem wrong_global_argument_rejected : Program.checkProgram 64
    [functionDeclaration,⟨.i64,.app (.node (.global 0) []) (.natural 0)⟩] = none := by cbv

theorem unscoped_converted_annotation_rejected : Program.checkProgram 64
    [ScopeInputExamples.unscopedDeclaration] = none := by cbv

theorem malformed_discarded_annotation_rejected : Program.checkProgram 64
    [⟨.pi false buffer .i64,.lam false buffer
      (.lend (.var 0) reader (.lam false .i64 (.lam false
        (.app (.lam false .u64 buffer) (.node .u64 [.natural 0]))
        (.free (.var 0) (.var 1)))))⟩] = none := by cbv

end Jihoo.NativeKernel.Environment.LoanTyping.GlobalExamples
