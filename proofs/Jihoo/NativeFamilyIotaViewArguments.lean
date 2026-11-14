import Jihoo.NativeFamilyIotaViewAlgebra

/-! Applying real borrowed-view field arguments from actual constructor Args.
Domains are transported through proved read/deref conversion and computed
metadata; no reflected branch typing or source-preservation callback appears. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

theorem viewPlan_valid (planned : viewPlan env family fields = some plans) :
    ∀ plan ∈ plans,viewFieldPlan env family plan.field = some plan := by
  unfold viewPlan at planned
  induction fields generalizing plans with
  | nil => simp only [List.mapM_nil,pure,Option.some.injEq] at planned;subst plans;simp
  | cons field fields ih =>
    simp only [List.mapM_cons] at planned
    cases head : viewFieldPlan env family field with
    | none => simp [head] at planned
    | some plan =>
      simp only [head,Bind.bind,Option.bind] at planned
      cases tail : fields.mapM (viewFieldPlan env family) with
      | none => simp [tail] at planned
      | some rest =>
        simp only [tail,Bind.bind,Option.bind,pure,Option.some.injEq] at planned
        subst plans
        intro selected member
        rcases List.mem_cons.mp member with rfl | member
        · rw [viewFieldPlan_source head]
          exact head
        · exact ih tail selected member

/-- The successful computed field plan transforms each actual field once.
The returned type is the actual consumption of the borrowed telescope. -/
theorem apply_view_arguments (wf : UnifiedProgram.EnvWellFormed env)
    (found : env.families[family]? = some entry) (boxed : entry.boxed = true)
    (plans : List ViewFieldPlan)
    (planned : ∀ plan ∈ plans,viewFieldPlan env family plan.field = some plan)
    (reading : ReadsAs env previous original borrowed)
    (arguments : Arguments env ctx true data
      ((closeDataFields (instantiatedFields depth ps false previous.length (plans.map ViewFieldPlan.field)) sourceBody).subst original)
      values sourceResult)
    (branch : HasType env ctx true function
      ((closeDataFields (viewInstFields depth ps previous plans) targetBody).subst borrowed))
    (size : values.length = plans.length) :
    ∃ output,consume ((closeDataFields (viewInstFields depth ps previous plans) targetBody).subst borrowed)
        (viewArguments plans values) = some output ∧
      HasType env ctx true (applications function (viewArguments plans values)) output := by
  induction plans generalizing previous original borrowed values function with
  | nil =>
    have empty : values = [] := List.length_eq_zero_iff.mp size
    subst values
    exact ⟨_,rfl,branch⟩
  | cons plan plans ih =>
    cases values with
    | nil => simp at size
    | cons value values =>
      have tailSize : values.length = plans.length := Nat.succ.inj size
      have headPlan := planned plan (by simp)
      have tailPlan : ∀ plan ∈ plans,viewFieldPlan env family plan.field = some plan :=
        fun p hp => planned p (by simp [hp])
      let domain := plan.field.domain.subst (parameterAt depth previous.length ps)
      have typed := arguments
      simp only [List.map_cons,instantiatedFields,Bool.false_and,Bool.false_eq_true,↓reduceIte,
        closeDataFields,List.foldr_cons,Term.subst,substArgs,Op.binders,liftSub] at typed
      obtain ⟨valueTyped,remaining⟩ := arguments_pi_view wf typed
      have domainRelated := reading.term wf.closed domain
      have argumentTyped : HasType env ctx true (if plan.borrowed then .borrow value else value)
          ((if plan.borrowed then Term.ref (viewRead previous domain) else viewRead previous domain).subst borrowed) := by
        cases flag : plan.borrowed with
        | false =>
          simp only [flag,Bool.false_eq_true,ite_false]
          exact .convert valueTyped domainRelated.symm
        | true =>
          simp only [flag,ite_true,subst_ref]
          have owned := view_plan_borrowed_owned found boxed headPlan flag
            (fun x => (parameterAt depth previous.length ps x).subst original)
          have owned' : Owned env (domain.subst original) := by
            simpa only [domain,Term.subst_comp] using owned
          exact .convert (.ghostBorrowOwned valueTyped owned')
            (.node .ref (.cons domainRelated.symm .nil))
      have branchPi := branch
      simp only [viewInstFields,closeDataFields,List.foldr_cons,Term.subst,substArgs,Op.binders,liftSub] at branchPi
      have applied := HasType.app branchPi (by simpa only [Bool.true_or] using argumentTyped) (Or.inl rfl)
      rw [Term.subst_comp] at applied remaining
      change HasType env ctx true _
        ((closeDataFields (viewInstFields depth ps (previous ++ [plan.borrowed]) plans) targetBody).subst
          (fun x => (liftSubOne borrowed x).subst
            (single (if plan.borrowed then .borrow value else value)))) at applied
      rw [lift_single_extend] at applied remaining
      have next := ih tailPlan (reading.extend plan.borrowed value)
        (by simpa only [List.length_append,List.length_singleton,closeDataFields] using remaining) applied tailSize
      obtain ⟨output,computed,typedOutput⟩ := next
      refine ⟨output,?_,?_⟩
      · simpa only [viewInstFields,closeDataFields,List.foldr_cons,Term.subst,substArgs,Op.binders,liftSub,
          viewArguments,List.zip_cons_cons,List.map_cons,consume,Term.subst_comp,lift_single_extend] using computed
      · simpa only [viewArguments,List.zip_cons_cons,List.map_cons,applications,List.foldl_cons] using typedOutput

end Jihoo.NativeKernel.Environment.FamilyIota
