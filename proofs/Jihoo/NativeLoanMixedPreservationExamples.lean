import Jihoo.NativeLoanMixedPreservation
import Jihoo.NativeLoanGlobalExamples

namespace Jihoo.NativeKernel.Environment.LoanTyping.MixedPreservationExamples
open NativeKernel.Environment.FamilyIota

def bit : FamilyDeclaration := ⟨true,0,0,[.node (.ind 0 0) []],1⟩
def bitEntry : CheckedFamily := ⟨bit,[⟨[],[]⟩],false⟩
def reader : Term := .lam false (.ref CheckerExamples.buffer)
  (.index (.borrow (.var 1)) (.natural 0) (.decide (.natural 0) (.natural 2)))
def function : Term := .lam false CheckerExamples.buffer
  (.lend (.var 0) reader CheckerExamples.continuation)
def functionDeclaration : GlobalDeclaration := ⟨.pi false CheckerExamples.buffer .i64,function⟩
def definitions : List GlobalDeclaration := [functionDeclaration,
  ⟨.i64,.app (.node (.global 0) []) CheckerExamples.allocatedOwner⟩]
def env : Environment :=
  ⟨#[functionDeclaration,⟨.i64,.app function CheckerExamples.allocatedOwner⟩],#[bitEntry]⟩

theorem actual_mixed_program_checked :
    MixedProgram.checkProgram 64 128 definitions [bit] = some env := by cbv

theorem actual_mixed_history : MixedProgram.History definitions [bit] env :=
  MixedProgram.checkProgram_sound actual_mixed_program_checked

theorem legacy_global_history_is_insufficient :
    UnifiedProgram.checkProgram 64 128 definitions [bit] = none := by cbv

def input : Term := elimTerm 0 (.lam false (.node (.ind 0 0) []) .u64)
  [.natural 7] (.node (.con 0 0 0) [])

theorem input_checked_by_loan_kernel : Checker.check 64 env [] [] true input .u64 = true := by cbv

theorem actual_family_contraction : contract env input = some (.natural 7) := by cbv

/-- The original result type follows from input checking and contraction,
using a program history that genuinely contains code Lend declarations. -/
theorem original_type_after_family_contraction : HasType env [] [] true (.natural 7) .u64 :=
  actual_mixed_history.family_contract_preserves actual_family_contraction
    (Checker.check_sound input_checked_by_loan_kernel)

theorem contextual_path_and_original_type :
    RawLend.Forward env input (.natural 7) ∧ HasType env [] [] true (.natural 7) .u64 :=
  actual_mixed_history.contextual_preservation
    (FamilyEvaluation.contract_steps actual_family_contraction)
    (Checker.check_sound input_checked_by_loan_kernel)

end Jihoo.NativeKernel.Environment.LoanTyping.MixedPreservationExamples
