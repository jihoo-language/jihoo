import Jihoo.NativeCoreForwardScope
import Jihoo.NativeFamilyIotaConversion

/-! Raw family/delta/ACU forward scope preservation. Arbitrary forged family
metadata is allowed: the genuine builders use source motives, cases and fields
and never insert metadata terms. Only global bodies require closedness. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota

private theorem inputs (scope : (Term.node op children).Scoped depth) (nonbinding : ∀ index,op.binders index = 0) :
    ∀ child ∈ children,child.Scoped depth := by
  intro child member
  obtain ⟨index,selected⟩ := List.getElem?_of_mem member
  simpa only [nonbinding,Nat.add_zero] using scope.child selected

private theorem borrowed (scope : value.Scoped depth) : (Term.borrow value).Scoped depth := by
  apply Term.Scoped.nonbinding (by intro index; rfl)
  intro child member
  have same := List.mem_singleton.mp member
  subst child
  exact scope

private theorem applications_scope (function : f.Scoped depth) (arguments : ∀ value ∈ values,value.Scoped depth) :
    (applications f values).Scoped depth := by
  induction values generalizing f with
  | nil => exact function
  | cons argument rest ih =>
    simpa only [Environment.applications,List.foldl_cons] using
      ih (function.application (arguments argument (by simp)))
        (fun value member => arguments value (List.mem_cons_of_mem _ member))

private theorem eliminator_scope {motive scrutinee : Term} {branches : List Term}
    (nonbinding : ∀ index,op.binders index = 0)
    (motiveScope : motive.Scoped depth) (cases : ∀ branch ∈ branches,branch.Scoped depth) (scrutineeScope : scrutinee.Scoped depth) :
    (Term.node op (motive :: (branches ++ [scrutinee]))).Scoped depth := by
  apply Term.Scoped.nonbinding nonbinding
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact motiveScope
  · rcases List.mem_append.mp member with member | member
    · exact cases _ member
    · have same := List.mem_singleton.mp member
      subst child
      exact scrutineeScope

private theorem parts (nonbinding : ∀ index,op.binders index = 0)
    (scope : (Term.node op (motive :: (cases ++ [scrutinee]))).Scoped depth) :
    motive.Scoped depth ∧ (∀ branch ∈ cases,branch.Scoped depth) ∧ scrutinee.Scoped depth := by
  have all := inputs scope nonbinding
  exact ⟨all _ (by simp),fun branch member => all _ (by simp [member]),all _ (by simp)⟩

private theorem elim_hypotheses_scope {motive : Term} (motiveScope : motive.Scoped depth)
    (cases : ∀ branch ∈ branches,branch.Scoped depth) (values : ∀ value ∈ arguments,value.Scoped depth) :
    ∀ hypothesis ∈ elimHypotheses family motive branches fields arguments,hypothesis.Scoped depth := by
  intro hypothesis member
  obtain ⟨⟨field,value⟩,selected,equation⟩ := List.mem_filterMap.mp member
  simp only at equation
  split at equation
  · cases equation
    exact eliminator_scope (by intro index; rfl) motiveScope cases (values _ (List.of_mem_zip selected).2)
  · cases equation

private theorem view_arguments_scope (values : ∀ value ∈ arguments,value.Scoped depth) :
    ∀ argument ∈ viewArguments plans arguments,argument.Scoped depth := by
  intro argument member
  unfold viewArguments at member
  obtain ⟨⟨plan,value⟩,selected,equation⟩ := List.mem_map.mp member
  simp only at equation
  rw [←equation]
  have scope := values _ (List.of_mem_zip selected).2
  by_cases flag : plan.borrowed = true
  · simpa only [flag,ite_true] using borrowed scope
  · simpa only [flag,Bool.false_eq_true,ite_false] using scope

private theorem view_hypotheses_scope {motive : Term} (motiveScope : motive.Scoped depth)
    (cases : ∀ branch ∈ branches,branch.Scoped depth) (values : ∀ value ∈ arguments,value.Scoped depth) :
    ∀ hypothesis ∈ viewHypotheses recursion family motive branches plans arguments,hypothesis.Scoped depth := by
  intro hypothesis member
  unfold viewHypotheses at member
  split at member
  · obtain ⟨⟨plan,value⟩,selected,equation⟩ := List.mem_filterMap.mp member
    simp only at equation
    split at equation
    · cases equation
      exact eliminator_scope (by intro index; rfl) motiveScope cases (borrowed (values _ (List.of_mem_zip selected).2))
    · cases equation
  · cases member

theorem Root.scope (step : Root env term result) : ∀ depth,term.Scoped depth → result.Scoped depth := by
  cases step with
  | elim found signature selected count fields =>
    intro depth scope
    obtain ⟨motiveScope,casesScope,scrutineeScope⟩ := parts (by intro index; rfl) scope
    have valuesScope := inputs scrutineeScope (by intro index; rfl)
    apply applications_scope
    · exact applications_scope (casesScope _ (List.mem_of_getElem? selected))
        (fun value member => valuesScope _ (List.mem_of_mem_drop member))
    · exact elim_hypotheses_scope motiveScope casesScope valuesScope
  | caseOf found data signature selected count fields =>
    intro depth scope
    obtain ⟨motiveScope,casesScope,scrutineeScope⟩ := parts (by intro index; rfl) scope
    have valuesScope := inputs scrutineeScope (by intro index; rfl)
    exact applications_scope (casesScope _ (List.mem_of_getElem? selected))
      (fun value member => valuesScope _ (List.mem_of_mem_drop member))
  | view found boxed signature selected count fields params planned =>
    intro depth scope
    obtain ⟨motiveScope,casesScope,scrutineeScope⟩ := parts (by intro index; rfl) scope
    have constructorScope := scrutineeScope.child (index := 0) rfl
    have valuesScope := inputs constructorScope (by intro index; rfl)
    have dropped (count : Nat) := fun value member => valuesScope value (List.mem_of_mem_drop (i := count) member)
    apply applications_scope
    · exact applications_scope (casesScope _ (List.mem_of_getElem? selected)) (view_arguments_scope (dropped _))
    · exact view_hypotheses_scope motiveScope casesScope (dropped _)
  | drop family owner rest => intro depth scope; simpa only [Op.binders,Nat.add_zero] using scope.child (index := 1) rfl

end Jihoo.NativeKernel.Environment.FamilyIota

namespace Jihoo.NativeKernel.EnvironmentDelta

theorem Forward.scope (closed : Basis.Closed env) (step : Forward env term result) :
    ∀ depth,term.Scoped depth → result.Scoped depth := by
  induction step using Forward.rec
    (motive_2 := fun first second _ => NativeKernel.Conversion.ListRel
      (fun first second => ∀ depth,first.Scoped depth → second.Scoped depth) first second) with
  | refl => intro depth scope; exact scope
  | trans _ _ first second => intro depth scope; exact second depth (first depth scope)
  | node op related ih => intro depth scope; exact scope.node_transport ih
  | acu step => exact step.scope
  | delta found => intro depth scope; exact (closed _ _ found).monotone (Nat.zero_le _)
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

end Jihoo.NativeKernel.EnvironmentDelta

namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended

theorem Forward.scope (closed : EnvironmentDelta.Basis.Closed env) (step : Forward env term result) :
    ∀ depth,term.Scoped depth → result.Scoped depth := by
  induction step using Forward.rec
    (motive_2 := fun first second _ => NativeKernel.Conversion.ListRel
      (fun first second => ∀ depth,first.Scoped depth → second.Scoped depth) first second) with
  | old step => exact step.scope closed
  | iota step => exact step.scope
  | refl => intro depth scope; exact scope
  | trans _ _ first second => intro depth scope; exact second depth (first depth scope)
  | node op related ih => intro depth scope; exact scope.node_transport ih
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
