import Jihoo.NativeFamilyIotaViewCongruence

/-! The dependent View result reconstructs the original constructor by real
Deref/Borrow conversion, for arbitrary fields and leading parameter values. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

theorem viewArguments_length (size : values.length = plans.length) :
    (viewArguments plans values).length = values.length := by
  simp only [viewArguments,List.length_map,List.length_zip,size,Nat.min_self]

theorem viewArguments_selected {plans : List ViewFieldPlan} {plan : ViewFieldPlan} {values : List Term} {j : Nat} {value : Term} (selected : plans[j]? = some plan) (valueFound : values[j]? = some value) :
    (viewArguments plans values)[j]? = some (if plan.borrowed then .borrow value else value) := by
  have paired : (plans.zip values)[j]? = some (plan,value) := List.getElem?_zip_eq_some.mpr ⟨selected,valueFound⟩
  simp only [viewArguments,List.getElem?_map,paired,Option.map_some]

private theorem fieldSubstitution_above (values : List Term) (above : values.length ≤ x) :
    fieldSubstitution values x = .var (x-values.length) := by
  have natural := fieldSubstitution_shift values (.var (x-values.length))
  simp only [Term.rename,Term.subst] at natural
  simpa only [Nat.sub_add_cancel above] using natural

/-- The substitutions produced by actual application read back exactly the
constructor fields, including free variables above the full telescope. -/
theorem viewArguments_reads (size : values.length = plans.length) :
    ReadsAs env (plans.map ViewFieldPlan.borrowed) (fieldSubstitution values)
      (fieldSubstitution (viewArguments plans values)) := by
  intro x
  have length := viewArguments_length size
  by_cases inside : x < plans.length
  · let j := plans.length-1-x
    have jInside : j < plans.length := by dsimp [j];omega
    have vInside : j < values.length := by omega
    have pFound := List.getElem?_eq_getElem jInside
    have vFound := List.getElem?_eq_getElem vInside
    have borrowedFound := viewArguments_selected pFound vFound
    have reverse : values.length-1-j = x := by dsimp [j];omega
    have borrowedReverse : (viewArguments plans values).length-1-j = x := by omega
    have original := fieldSubstitution_selected vFound
    have transformed := fieldSubstitution_selected borrowedFound
    rw [reverse] at original
    rw [borrowedReverse] at transformed
    have flagFound : (plans.map ViewFieldPlan.borrowed)[j]? = some (plans[j].borrowed) := by
      simp only [List.getElem?_map,pFound,Option.map_some]
    simp only [viewReadAt,List.length_map,inside,true_and]
    change Conversion.Conv env
      ((if (plans.map ViewFieldPlan.borrowed)[j]?.getD false then Term.deref (.var x) else Term.var x).subst
        (fieldSubstitution (viewArguments plans values))) (fieldSubstitution values x)
    rw [flagFound]
    simp only [Option.getD_some]
    cases flag : plans[j].borrowed with
    | false => simp only [flag,Bool.false_eq_true,ite_false,Term.subst,transformed,original];exact .refl _
    | true => simp only [flag,ite_true,subst_deref,Term.subst,transformed,original];exact .legacy (.derefBorrow _)
  · have above : values.length ≤ x := by omega
    have borrowedAbove : (viewArguments plans values).length ≤ x := by omega
    simp only [viewReadAt,List.length_map,inside,false_and,ite_false,Term.subst,
      fieldSubstitution_above values above,fieldSubstitution_above _ borrowedAbove,length]
    exact .refl _

private theorem related_map_substitution (reading : ReadsAs env previous original borrowed)
    (closed : Conversion.Closed env) (terms : List Term) :
    Conversion.ListRel (Conversion.Conv env)
      (terms.map (fun term => (viewRead previous term).subst borrowed))
      (terms.map (Term.subst original)) := by
  induction terms with
  | nil => exact .nil
  | cons term terms ih => exact .cons (reading.term closed term) ih

private theorem viewReadAt_field (borrowed : List Bool) (inside : j < borrowed.length) :
    viewReadAt borrowed (borrowed.length-1-j) =
      if borrowed[j]?.getD false then .deref (.var (borrowed.length-1-j)) else .var (borrowed.length-1-j) := by
  have reverseInside : borrowed.length-1-j < borrowed.length := by omega
  have reverse : borrowed.length-1-(borrowed.length-1-j) = j := by omega
  simp only [viewReadAt,reverseInside,true_and,reverse]

private theorem read_fields_form (borrowed : List Bool) :
    (List.range borrowed.length).map (fun j =>
      if borrowed[j]?.getD false then .deref (.var (borrowed.length-1-j)) else .var (borrowed.length-1-j)) =
      (fieldVariables borrowed.length).map (viewRead borrowed) := by
  simp only [fieldVariables,List.map_map]
  apply List.map_congr_left
  intro j member
  simp only [Function.comp_apply,viewRead,Term.subst]
  exact (viewReadAt_field borrowed (List.mem_range.mp member)).symm

private theorem related_append (first : Conversion.ListRel (Conversion.Conv env) xs ys)
    (second : Conversion.ListRel (Conversion.Conv env) rest rest') :
    Conversion.ListRel (Conversion.Conv env) (xs ++ rest) (ys ++ rest') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem related_refl (xs : List Term) : Conversion.ListRel (Conversion.Conv env) xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl _) ih

private theorem shifted_parameters (ps values : List Term) :
    (ps.map (Term.rename (fun x => x+values.length))).map (Term.subst (fieldSubstitution values)) = ps := by
  rw [List.map_map]
  calc
    _ = ps.map id := by
      apply List.map_congr_left
      intro term member
      exact fieldSubstitution_shift values term
    _ = _ := List.map_id ps

/-- Consuming the generated borrowed field telescope leaves a result converted
to the actual source motive application; dependent constructors are rebuilt
from their actual original fields. -/
theorem viewCaseResult_instantiation (closed : Conversion.Closed env)
    (size : values.length = plans.length) :
    Conversion.Conv env
      ((viewCaseResult family constructor plans.length 0 ps motive (plans.map ViewFieldPlan.borrowed) dependent).subst
        (fieldSubstitution (viewArguments plans values)))
      (viewResult dependent motive (.borrow (.node (.con family constructor (ps ++ values).length) (ps ++ values)))) := by
  have length := viewArguments_length size
  have fields := related_map_substitution (viewArguments_reads (env := env) size) closed (fieldVariables values.length)
  rw [fieldVariables_substitution] at fields
  unfold viewCaseResult viewResult
  cases dependent with
  | false =>
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
    rw [← size,← length,fieldSubstitution_shift]
    exact .refl _
  | true =>
    simp only [ite_true,Nat.add_zero,Term.subst,substArgs,Op.binders,liftSub,List.map_append]
    have motiveSame := fieldSubstitution_shift (viewArguments plans values) motive
    rw [length,size] at motiveSame
    rw [motiveSame]
    apply FamilyIota.Extended.Conv.node .app
    refine .cons (.refl _) (.cons (.node .borrow (.cons ?_ .nil)) .nil)
    have flagsLength : (plans.map ViewFieldPlan.borrowed).length = plans.length := List.length_map ..
    have form := read_fields_form (plans.map ViewFieldPlan.borrowed)
    simp only [flagsLength] at form
    rw [form]
    simp only [substArgs_con,List.map_append,List.map_map]
    have leading := shifted_parameters ps (viewArguments plans values)
    rw [length,size] at leading
    simp only [List.map_map] at leading
    rw [leading]
    simp only [List.length_append,List.length_map,List.length_range]
    rw [← size]
    simp only [fieldVariables_length]
    exact .node _ (related_append (related_refl ps) fields)

end Jihoo.NativeKernel.Environment.FamilyIota
