import Jihoo.NativeExactClosing
import Jihoo.NativeInferredKindExamples
import Jihoo.NativeSmallTelescopeExamples

namespace Jihoo.NativeKernel.Environment.ExactClosingExamples
open CodeKinds InferredKindExamples ClosingTelescopeExamples ContextReplayExamples ContextModes Jihoo.Quantity
open SmallTelescopeExamples

def computedTypeArgument : Term := .app (.lam false .u64 .u64) (.natural 0)
def actualArguments : List Term := [computedTypeArgument,.i64,.natural 7,.integer 3]
def actualEntries : List CallReplay.Argument :=
  [⟨false,.univ 0,computedTypeArgument⟩,⟨false,.univ 0,.i64⟩,
    ⟨false,.u64,.natural 7⟩,⟨false,.i64,.integer 3⟩]

theorem actual_input_observations : twoKindTelescope.Inputs 64 actualArguments := by
  refine ⟨⟨.univ 0,by cbv,rfl⟩,⟨⟨.univ 0,by cbv,rfl⟩,?_⟩⟩
  rfl

theorem exact_actual_argument_slots :
    pushValues Term.var actualArguments 0 = .integer 3 ∧
    pushValues Term.var actualArguments 1 = .natural 7 ∧
    pushValues Term.var actualArguments 2 = .i64 ∧
    pushValues Term.var actualArguments 3 = computedTypeArgument := ⟨rfl,rfl,rfl,rfl⟩

/-- The closing values themselves, rather than an existential replacement,
are fixed by the four real source arguments. -/
theorem actual_four_binder_exact_closing :
    RealizedInterpretation .empty twoKindContext (pushValues Term.var actualArguments) ∧
      Conversion.Conv .empty .i64 ((Term.var 2).subst (pushValues Term.var actualArguments)) := by
  apply twoKindTelescope.close_checkedCall_exact (fuel := 64) empty_history (RealizedInterpretation.nil Term.var)
    (Checker.check_sound (by cbv : Checker.check 64 .empty [] false twoKindFunction twoKindSignature = true))
    (entries := actualEntries) (arguments := actualArguments)
  · cbv
  · exact actual_input_observations

/-- The computed type argument is actually normalized while the dependent
ordinary argument retains its typed slot under the new annotation. -/
theorem actual_four_binder_exact_normalized_closing :
    RealizedInterpretation .empty twoKindContext
      (normalizedValues .empty 64 (pushValues Term.var actualArguments)) ∧
      Conversion.Conv .empty .i64 ((Term.var 2).subst
        (normalizedValues .empty 64 (pushValues Term.var actualArguments))) :=
  twoKindTelescope.close_checkedCall_exact_normalized (fuel := 64) empty_history
    (RealizedInterpretation.nil Term.var)
    (Checker.check_sound (by cbv : Checker.check 64 .empty [] false twoKindFunction twoKindSignature = true))
    (by cbv : CallReplay.checked 64 .empty [] false (twoKindFunction.subst Term.var) actualArguments =
      some (actualEntries,.i64)) actual_input_observations 64

theorem dependent_ordinary_value_retyped_after_actual_type_computation :
    HasType .empty [] true (.natural 7) .u64 := by
  have typed := actual_four_binder_exact_normalized_closing.1.typed 1 ⟨.var 3,false⟩
    (by cbv : lookup twoKindContext 1 = some ⟨.var 3,false⟩)
  simp only [Term.subst] at typed
  have first : normalizedValues .empty 64 (pushValues Term.var actualArguments) 1 = .natural 7 := by cbv
  have second : normalizedValues .empty 64 (pushValues Term.var actualArguments) 3 = .u64 := by cbv
  simpa only [first,second] using typed

def abstractValues : Nat → Term := fun _ => computedTypeArgument

theorem authentic_abstract_type_closing : RealizedInterpretation .empty [⟨.univ 0,false⟩] abstractValues :=
  (TraceInterpretation.single (kind := .type 0) empty_history
    (by cbv : Checker.binder 64 .empty [] false (.univ 0) = some (.type 1))
    (by cbv : Checker.check 64 .empty [] false computedTypeArgument (.univ 0) = true)
    (by cbv : Conversion.normalize? .empty 64 (.univ 0) = some (.univ 0))
    (by cbv : Checker.applicationOK 64 .empty false (.univ 0) computedTypeArgument = true)).realized empty_history

/-- An actual source lambda's abstract binder stays semantically unrestricted
after the outer type value computes. Its exact original scope is retained. -/
theorem actual_lambda_evaluated_abstract_mode :
    ∃ mode body sort, ContextFormed .empty [⟨.univ 0,false⟩] ∧
      Binder .empty [⟨.univ 0,false⟩] false (.var 0) sort ∧
      ModeContract .empty ((Term.var 0).subst (normalizedValues .empty 64 abstractValues)) mode ∧
      ContextQuantity.projectRaw 64 .empty [⟨.var 0,false⟩,⟨.univ 0,false⟩] (.var 0) = some body ∧
      Control.closure (.scope .unrestricted (.use 0)) =
        .closure (.scope mode (NativeQuantity.functionTail (.var 0) body)) :=
  ContextQuantity.lam_evaluated_modeContract (fuel := 64)
    (by cbv : ContextQuantity.projectRaw 65 .empty [⟨.univ 0,false⟩] (.lam false (.var 0) (.var 0)) =
      some (.closure (.scope .unrestricted (.use 0))))
    (Extends.refl _) empty_history authentic_abstract_type_closing (ForwardValues.normalized _)

/-- The ordinary dependent suffix needs no positive-kind input observations;
its exact erased-index and ordinary slots remain typed after value computation. -/
theorem actual_dependent_suffix_exact_normalized :
    RealizedInterpretation .empty indexedIdentityContext
      (normalizedValues .empty 64 (pushValues familyValues [.strict owner (.natural 0),.natural 7])) ∧
      Conversion.Conv .empty .u64 ((Term.app (.var 2) (.var 1)).subst
        (normalizedValues .empty 64 (pushValues familyValues [.strict owner (.natural 0),.natural 7]))) := by
  apply arbitrary_family_small_telescope.close_checkedCall_exact_normalized (fuel := 64)
    empty_history computed_family_closing
    (Checker.check_sound (by cbv : Checker.check 64 .empty [⟨.pi false .u64 (.univ 0),false⟩]
      false suffixFunction suffixSignature = true))
    (entries := [⟨true,.u64,.strict owner (.natural 0)⟩,⟨false,.u64,.natural 7⟩])
  · cbv
  · rfl

end Jihoo.NativeKernel.Environment.ExactClosingExamples
