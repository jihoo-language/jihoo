import Jihoo.NativeFamilyIotaViewArguments
import Jihoo.NativeFamilyIotaParameterAlignment

/-! Parameter congruence for actual computed borrowed View telescopes. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem related_refl (xs : List Term) : Conversion.ListRel (Conversion.Conv env) xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl x) ih

private theorem related_length (related : Conversion.ListRel (Conversion.Conv env) xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem related_append (first : Conversion.ListRel (Conversion.Conv env) xs ys)
    (second : Conversion.ListRel (Conversion.Conv env) rest rest') :
    Conversion.ListRel (Conversion.Conv env) (xs ++ rest) (ys ++ rest') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem related_rename (closed : Conversion.Closed env)
    (related : Conversion.ListRel (Conversion.Conv env) xs ys) (ρ : Nat → Nat) :
    Conversion.ListRel (Conversion.Conv env) (xs.map (Term.rename ρ)) (ys.map (Term.rename ρ)) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.renaming ρ closed) ih

theorem viewCaseResult_parameters_congr (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs) :
    Conversion.Conv env (viewCaseResult family constructor fields hypotheses ps motive borrowed dependent)
      (viewCaseResult family constructor fields hypotheses qs motive borrowed dependent) := by
  unfold viewCaseResult
  split
  · apply FamilyIota.Extended.Conv.node .app
    refine .cons (.refl _) (.cons (.node .borrow (.cons ?_ .nil)) .nil)
    simp only [List.length_append,List.length_map,List.length_range]
    rw [← related_length parameters]
    apply FamilyIota.Extended.Conv.node _
    exact related_append (related_rename closed parameters _) (related_refl _)
  · exact .refl _

theorem view_telescope_parameters_congr (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs) (plans : List ViewFieldPlan)
    (body : Conversion.Conv env result result') (previous : List Bool) :
    Conversion.Conv env (closeDataFields (viewInstFields depth ps previous plans) result)
      (closeDataFields (viewInstFields depth qs previous plans) result') := by
  induction plans generalizing previous with
  | nil => exact body
  | cons plan plans ih =>
    have domain := (parameter_term_congr closed parameters depth previous.length plan.field.domain).substitution
      (viewReadAt previous) closed
    apply FamilyIota.Extended.Conv.node (.pi (if plan.borrowed then false else plan.field.erased))
    refine .cons ?_ (.cons (ih (previous ++ [plan.borrowed])) .nil)
    cases plan.borrowed with
    | false => exact domain
    | true => exact .node .ref (.cons domain .nil)

private theorem hypotheses_congr (body : Conversion.Conv env result result') (positions : List Nat) :
    Conversion.Conv env (viewHypothesisTelescope fields offset positions motive dependent result)
      (viewHypothesisTelescope fields offset positions motive dependent result') := by
  unfold viewHypothesisTelescope
  generalize positions.zipIdx offset = pairs
  induction pairs with
  | nil => exact body
  | cons pair pairs ih => exact .node (.pi false) (.cons (.refl _) (.cons ih .nil))

/-- Both Option generation and the full type conversion follow from the
actual computed plan and pointwise parameter conversion. -/
theorem viewCaseType_parameters_congr (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs)
    (generated : viewCaseType env family constructor params depth signature ps motive recursion dependent = some type) :
    ∃ type',viewCaseType env family constructor params depth signature qs motive recursion dependent = some type' ∧
      Conversion.Conv env type type' := by
  have length := related_length parameters
  unfold viewCaseType at generated ⊢
  split at generated
  · contradiction
  · rename_i valid
    simp only [← length,valid,ite_false] at generated ⊢
    cases planned : viewPlan env family (signature.fields.drop params) with
    | none => simp [planned] at generated
    | some plans =>
      simp only [planned,Bind.bind,Option.bind,pure,Option.some.injEq] at generated ⊢
      subst type
      exact ⟨_,rfl,view_telescope_parameters_congr closed parameters plans
        (hypotheses_congr (viewCaseResult_parameters_congr closed parameters) _) []⟩

end Jihoo.NativeKernel.Environment.FamilyIota
