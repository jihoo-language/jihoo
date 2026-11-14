import Jihoo.NativeFamilyIotaViewHypotheses

/-! Ordered recursive positions coincide with the real executable recursive
View argument list, preserving multiplicity and all field positions. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem filterMap_congr (xs : List α) (same : ∀ x ∈ xs,f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons,same x (by simp)]
    rw [ih (fun y hy => same y (by simp [hy]))]

private theorem zip_indexed {values : List Term} {plans : List ViewFieldPlan} (size : values.length = plans.length) :
    plans.zip values = plans.zipIdx.map (fun (plan,j) => (plan,(values[j]?).getD (Term.natural 0))) := by
  apply List.ext_getElem
  · simp only [List.length_zip,size,Nat.min_self,List.length_map,List.length_zipIdx]
  · intro j leftBound rightBound
    have planBound : j < plans.length := by simpa only [List.length_map,List.length_zipIdx] using rightBound
    have valueBound : j < values.length := by omega
    simp only [List.getElem_zip,List.getElem_map,List.getElem_zipIdx,Nat.zero_add,
      List.getElem?_eq_getElem valueBound,Option.getD_some]

theorem viewPositions_selected (member : position ∈ viewPositions plans) :
    ∃ plan,plans[position]? = some plan ∧ plan.self = true := by
  obtain ⟨⟨plan,j⟩,inPlans,chosen⟩ := List.mem_filterMap.mp member
  have found := List.mk_mem_zipIdx_iff_getElem?.mp inPlans
  change (if plan.self then some j else none) = some position at chosen
  by_cases flag : plan.self = true
  · simp only [flag,ite_true,Option.some.injEq] at chosen
    subst position
    exact ⟨plan,found,flag⟩
  · simp only [flag,ite_false] at chosen
    contradiction

private theorem plan_self_borrowed (planned : viewFieldPlan env family field = some plan) (self : plan.self = true) :
    plan.borrowed = true := by
  unfold viewFieldPlan at planned
  simp only [Option.map] at planned
  repeat' first | split at planned | contradiction
  all_goals cases planned
  all_goals simp_all

/-- The positional generated telescope and executable recursive View list
select exactly the same calls in exactly the same declaration order. -/
theorem viewHypotheses_positions (planned : viewPlan env family fields = some plans)
    (size : values.length = plans.length) :
    hypothesisArguments (viewPositions plans) (viewArguments plans values) (viewTerm true family motive cases) =
      viewHypotheses true family motive cases plans values := by
  unfold hypothesisArguments viewPositions viewHypotheses
  simp only [ite_true,List.filterMap_filterMap]
  rw [zip_indexed size,List.filterMap_map]
  apply filterMap_congr
  intro pair member
  rcases pair with ⟨plan,j⟩
  have planFound := List.mk_mem_zipIdx_iff_getElem?.mp member
  have planBound := (List.getElem?_eq_some_iff.mp planFound).1
  have valueBound : j < values.length := by omega
  have valueFound := List.getElem?_eq_getElem valueBound
  by_cases self : plan.self = true
  · have borrowed := plan_self_borrowed (viewPlan_valid planned plan (List.mem_of_getElem? planFound)) self
    have argumentFound := viewArguments_selected planFound valueFound
    simp only [borrowed,ite_true] at argumentFound
    simp only [self,ite_true,Option.bind_some,argumentFound,Option.map_some,Function.comp_apply,
      valueFound,Option.getD_some]
  · simp only [self,Bool.false_eq_true,ite_false,Option.bind_none,Function.comp_apply]

theorem hypothesisArguments_length
    (bounds : ∀ position ∈ positions,∃ argument,fields[position]? = some argument) :
    (hypothesisArguments positions fields make).length = positions.length := by
  induction positions with
  | nil => rfl
  | cons position positions ih =>
    obtain ⟨argument,found⟩ := bounds position (by simp)
    have tailBounds : ∀ p ∈ positions,∃ a,fields[p]? = some a := fun p hp => bounds p (by simp [hp])
    simp only [hypothesisArguments,List.filterMap_cons,found,Option.map_some,List.length_cons]
    exact congrArg Nat.succ (ih tailBounds)

end Jihoo.NativeKernel.Environment.FamilyIota
