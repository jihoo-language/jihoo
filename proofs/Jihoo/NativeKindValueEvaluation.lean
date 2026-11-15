import Jihoo.NativeInferredKindArguments
import Jihoo.NativeEnvironmentOperationalRoots

/-! Kind representation survives actual forward computation and pure value
contractions in the evaluation direction. Runtime code need not be rechecked
after unrestricted syntactic substitution. This is a value/type interpretation
result; memory events and native evaluator refinement are separate obligations. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
open Representation
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
variable {kind : Kind} {index : Nat}

private theorem related_at (related : NativeKernel.Conversion.ListRel R xs ys)
    (selected : xs[index]? = some value) : ∃ result, ys[index]? = some result ∧ R value result := by
  induction related generalizing index with
  | nil => simp at selected
  | cons first rest ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
                subst value
                exact ⟨_,rfl,first⟩
      | succ index => exact ih selected

/-- A rigid value frame exposes its actually typed kind-valued child. Typed U64
holes cannot stand for the whole kind-valued frame; no index canonicity is used. -/
theorem Realizes.rigid_child
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind (.node op children))
    (rigid : FamilyIota.Extended.rigid op = true)
    (noBinders : ∀ index, op.binders index = 0)
    (selected : children[index]? = some child)
    (typed : HasType env [] true child kind.term) : Realizes env kind child := by
  obtain ⟨normal,forward,plain⟩ := realized.representation
  obtain ⟨normalizedChildren,shape,changes⟩ := FamilyIota.Extended.Forward.rigid_shape forward rigid rfl
  subst normal
  obtain ⟨normalChild,selectedNormal,childForward⟩ := related_at changes selected
  have normalizedTyped := realized.typed.ghostFamilyForward history forward
  have notIndex : ¬ HasType env [] true (.node op normalizedChildren) .u64 := by
    intro indexTyped
    exact kind.not_u64 history.wellFormed.admissible
      (normalizedTyped.unique history.wellFormed indexTyped)
  have childPlain := plain.children noBinders notIndex normalChild (List.mem_of_getElem? selectedNormal)
  exact ⟨typed,normalChild,childForward,childPlain⟩

/-- The realization relation is stable along every genuine finite family-iota/delta/ACU
forward path. Confluence is used only to join actual forward representation
paths; it supplies no bounded normalizer completeness or normality claim. -/
theorem Realizes.forward
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind input)
    (step : FamilyIota.Extended.Forward env input output) : Realizes env kind output := by
  obtain ⟨normal,represented,plain⟩ := realized.representation
  have converted : Conversion.Conv env output normal :=
    (FamilyIota.Extended.Forward.toConv step).symm.trans
      (FamilyIota.Extended.Forward.toConv represented)
  obtain ⟨common,outputForward,normalForward⟩ := converted.church_rosser history.wellFormed.admissible
  have normalTyped := realized.typed.ghostFamilyForward history represented
  have commonPlain := (forward_plain_transform history normalForward).preserves normalTyped plain
  exact ⟨realized.typed.ghostFamilyForward history step,common,outputForward,commonPlain⟩

/-- Strict/Free and zero-iteration values preserve the semantic kind contract
at their original type even when raw CODE rechecking is conservative. Free's
heap event is not erased by a runtime theorem here: this proves the result's
kind interpretation once the corresponding value contraction is observed. -/
theorem Realizes.valueRoot
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind input)
    (step : ValueReduction.Root input output) : Realizes env kind output := by
  have typed := step.preserves realized.typed
  cases step with
  | arithmetic op a b bound =>
      have integerTyped : HasType env [] true (.integer (ValueReduction.arithmetic op a b)) .i64 :=
        .integer bound.1 bound.2
      have converted := typed.unique history.wellFormed integerTyped
      cases kind with
      | type level =>
          exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) converted history.wellFormed.admissible)
      | index erased rest =>
          exact False.elim (FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
            (by intro same; cases same) converted history.wellFormed.admissible)
  | strict first rest => exact realized.rigid_child history rfl (by intro index; rfl) (index := 1) rfl typed
  | free owner rest => exact realized.rigid_child history rfl (by intro index; rfl) (index := 1) rfl typed
  | foldZero init body => exact realized.rigid_child history rfl (by intro index; rfl) (index := 1) rfl typed
  | loopZero motive init body => exact realized.rigid_child history rfl (by intro index; rfl) (index := 2) rfl typed

/-- Finite observed value computations. The constructors use actual installed
forward/root relations, rather than a supplied output representation flag. -/
inductive KindValueSteps (env : Environment) : Term → Term → Prop where
  | refl : KindValueSteps env term term
  | forward : FamilyIota.Extended.Forward env input output → KindValueSteps env input output
  | value : ValueReduction.Root input output → KindValueSteps env input output
  | trans : KindValueSteps env input middle → KindValueSteps env middle output → KindValueSteps env input output

theorem Realizes.valueSteps
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (realized : Realizes env kind input)
    (steps : KindValueSteps env input output) : Realizes env kind output := by
  induction steps with
  | refl => exact realized
  | forward step => exact realized.forward history step
  | value step => exact realized.valueRoot history step
  | trans first second ihfirst ihsecond => exact ihsecond (ihfirst realized)

/-- Actual input inference/check/gate plus an observed value computation yield
safe output representation without a closed CODE checker rerun. -/
theorem inferred_argument_evaluation_safe
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (inferred : Checker.infer fuel env [] false input = some actual)
    (kinded : Jihoo.NativeKernel.kindOf actual = true)
    (checked : Checker.check fuel env [] false input domain = true)
    (application : Checker.applicationOK fuel env false domain input = true)
    (converted : Conversion.Conv env domain kind.term)
    (steps : KindValueSteps env input output) :
    Realizes env kind output ∧ ¬ Owned env output ∧ PiSeparated env output := by
  have source := (ArgumentAtKind.of_inferred_kind history inferred kinded checked application converted).realizes history
  have result := source.valueSteps history steps
  exact ⟨result,result.not_owned history,result.nonFunction history⟩

end Jihoo.NativeKernel.Environment.CodeKinds
