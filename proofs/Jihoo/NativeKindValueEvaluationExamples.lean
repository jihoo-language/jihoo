import Jihoo.NativeKindValueEvaluation
import Jihoo.NativeInferredKindExamples

namespace Jihoo.NativeKernel.Environment.KindValueEvaluationExamples
open CodeKinds ClosingTelescopeExamples ContextReplayExamples

def freeType : Term := .free allocated .u64
def familyKind : Kind := .index false (.type 0)
def familyValue : Term := .lam false .u64 .u64
def freeFamily : Term := .free allocated familyValue
def computedFamily : Term := .app (.lam false .u64 freeFamily) (.natural 0)

theorem actual_effectful_type_argument_safe_after_value :
    Realizes .empty (.type 0) .u64 ∧ ¬ Owned .empty .u64 ∧ PiSeparated .empty .u64 := by
  apply inferred_argument_evaluation_safe (fuel := 64) empty_history
    (input := freeType) (actual := .univ 0) (domain := .univ 0)
    (by cbv) rfl (by cbv) (by cbv) (EnvironmentDelta.Basis.Conv.refl _)
  exact .value (.free allocated .u64)

theorem computed_family_observed_value_steps : KindValueSteps .empty computedFamily familyValue := by
  apply KindValueSteps.trans (middle := freeFamily)
  · apply KindValueSteps.forward
    apply EnvironmentDelta.Forward.acu
    apply ACU.MixedRed.compute
    simpa [computedFamily,freeFamily,familyValue,allocated,owner,
      Term.subst,substArgs,Op.binders,liftSub,liftSubOne,single,Term.rename,renameArgs] using
      ACU.Computes.beta false .u64 freeFamily (.natural 0)
  · exact .value (.free allocated familyValue)

/-- The source performs a memory computation before producing a family value.
Its original check and kind gate determine the evaluated value contract. -/
theorem computed_effectful_family_value_safe :
    Realizes .empty familyKind familyValue ∧ ¬ Owned .empty familyValue ∧ PiSeparated .empty familyValue := by
  apply inferred_argument_evaluation_safe (fuel := 64) empty_history
    (input := computedFamily) (actual := familyKind.term) (domain := familyKind.term)
    (by cbv) rfl (by cbv) (by cbv) (EnvironmentDelta.Basis.Conv.refl _)
    computed_family_observed_value_steps

/-- Evaluated family values apply safely to every ghost-typed U64 code tree;
no numeral, word bound, raw plainness, or repeated code check is supplied. -/
theorem computed_effectful_family_all_typed_indices
    (typed : HasType .empty [] true index .u64) :
    Realizes .empty (.type 0) (.app familyValue index) ∧
      ¬ Owned .empty (.app familyValue index) ∧ PiSeparated .empty (.app familyValue index) := by
  have represented := computed_effectful_family_value_safe.1.index typed
  exact ⟨represented,represented.not_owned empty_history,represented.nonFunction empty_history⟩

theorem same_unified_computed_effectful_family :
    (UnifiedProgram.checkProgram 64 128 [⟨familyKind.term,computedFamily⟩] []).isSome = true := by cbv

end Jihoo.NativeKernel.Environment.KindValueEvaluationExamples
