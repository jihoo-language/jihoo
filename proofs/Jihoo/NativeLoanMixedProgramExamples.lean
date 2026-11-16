import Jihoo.NativeLoanMixedAdmission
import Jihoo.NativeLoanGlobalInputExamples
import Jihoo.NativeLoanCheckerExamples

namespace Jihoo.NativeKernel.NativeLoanMixedAdmission.Examples
open NativeFamilyWire Environment Environment.LoanTyping

/-- A checked family occurs between the Lend function and its actual caller. -/
def snapshot : Snapshot :=
  { NativeLoanGlobalInput.Examples.snapshot with
    families := [⟨true,0,0,1,[20]⟩]
    arena := NativeLoanGlobalInput.Examples.snapshot.arena.push (.node (.ind 0 0) []) }

theorem mixed_loan_family_program_accepted :
    checkBytes 64 128 (encodeSnapshot snapshot) = true := by
  rw [checkBytes_encode]
  cbv

theorem mixed_history_and_world_constructed :
    ∃ definitions families env, decodeProgram snapshot = some (definitions,families) ∧
      MixedProgram.History definitions (families.map declaration) env ∧
      UnifiedProgram.EnvWellFormed env :=
  checkSnapshot_sound (by simpa only [checkBytes_encode] using mixed_loan_family_program_accepted)

def duplicateFunction : Term := .lam false CheckerExamples.buffer
  (.lend (.var 0) CheckerExamples.reader
    (.lam false .i64 (.lam false CheckerExamples.buffer
      (.free (.var 0) (.free (.var 0) (.var 1))))))

def duplicateDeclaration : GlobalDeclaration :=
  ⟨.pi false CheckerExamples.buffer .i64,duplicateFunction⟩

theorem duplicate_owner_is_still_well_typed :
    Program.checkDeclaration 64 empty duplicateDeclaration = some duplicateDeclaration := by cbv

theorem same_program_gate_rejects_duplicate_owner :
    MixedProgram.checkProgram 64 128 [duplicateDeclaration] [] = none := by cbv

theorem real_family_prefix_is_required : checkBytes 64 128 (encodeSnapshot
    { snapshot with families := [⟨true,0,0,3,[20]⟩] }) = false := by
  rw [checkBytes_encode]
  cbv

theorem exhausted_resource_budget_rejects :
    checkBytes 64 0 (encodeSnapshot snapshot) = false := by
  rw [checkBytes_encode]
  cbv

theorem source_scope_checked_before_conversion :
    MixedProgram.checkProgram 64 128 [ScopeInputExamples.unscopedDeclaration] [] = none := by cbv

end Jihoo.NativeKernel.NativeLoanMixedAdmission.Examples
