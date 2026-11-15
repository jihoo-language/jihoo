import Jihoo.NativeLoanContextualEvaluation
import Jihoo.NativeLoanLendConversionExamples

namespace Jihoo.NativeKernel.Environment.LoanTyping.ContextualEvaluationExamples
open LendConversionExamples

 theorem index_steps : Evaluation.Steps index (.natural 2) := by
  have computed : Lending.finish owner (.var 1) (Lending.read owner (.natural 2)) = .natural 2 := by cbv
  rw [← computed]
  exact .atomic (.lend owner (.ref buffer) (.natural 2) .u64 buffer (.var 1))

 theorem allocation_steps : Evaluation.Steps (.alloc index (.integer 0)) owner :=
  .node .alloc (by decide) (.cons index_steps (.cons .refl .nil))

 theorem allocation_original_type :
    HasType empty [] [] true owner (.buffer index) := by
  have typed : HasType empty [] [] true (.alloc index (.integer 0)) (.buffer index) :=
    .alloc index_typed (.integer (by decide) (by decide))
  exact allocation_steps.preserves UnifiedProgram.EnvWellFormed.empty typed

 theorem buffer_index_steps : Evaluation.Steps indexedBuffer buffer :=
  .node .buffer (by decide) (.cons index_steps .nil)

 theorem buffer_original_sort : HasType empty [] [] true buffer (.univ 0) :=
  buffer_index_steps.preserves UnifiedProgram.EnvWellFormed.empty (HasType.buffer (ghost := true) index_typed)

 def genericSource : Term := .lend owner
  (.strict (.natural 0) (.lam false (.ref buffer) (.natural 2)))
  (.lam false .u64 (.lam false buffer (.var 1)))

 theorem generic_checked : Checker.check 48 empty [] [] true genericSource .u64 = true := by cbv

 theorem nonexplicit_generic_steps : Evaluation.Steps genericSource
    (RawLend.desugar owner (.strict (.natural 0) (.lam false (.ref buffer) (.natural 2)))
      (.lam false .u64 (.lam false buffer (.var 1)))) :=
  .generic _ _ _ rfl

 theorem nonexplicit_generic_original_type : HasType empty [] [] true
    (RawLend.desugar owner (.strict (.natural 0) (.lam false (.ref buffer) (.natural 2)))
      (.lam false .u64 (.lam false buffer (.var 1)))) .u64 :=
  nonexplicit_generic_steps.preserves UnifiedProgram.EnvWellFormed.empty (Checker.check_sound generic_checked)

end Jihoo.NativeKernel.Environment.LoanTyping.ContextualEvaluationExamples
