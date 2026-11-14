import Jihoo.NativeFamilyIotaRecursiveArguments

/-! The real View rule types each recursive call from recovered self-field
metadata and actual constructor arguments, without assuming iota preservation. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem plan_self_domain (planned : viewFieldPlan env family field = some plan)
    (self : plan.self = true) :
    ∃ count indices,field.domain = .node (.ind family count) indices ∧ plan.borrowed = true := by
  unfold viewFieldPlan at planned
  simp only [Option.map] at planned
  repeat' first | split at planned | contradiction
  all_goals cases planned
  all_goals simp_all only [Bool.false_eq_true]
  exact ⟨_,_,rfl,trivial⟩

private theorem related_symm (related : Conversion.ListRel (Conversion.Conv env) xs ys) :
    Conversion.ListRel (Conversion.Conv env) ys xs := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.symm ih

/-- A recursive View hypothesis is typed by an actual View rule at the
independently observed outer parameter instance. -/
theorem recursive_view_hypothesis {family constructor position : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (dataIs : entry.declaration.data = true) (boxed : entry.boxed = true)
    (arity : entry.declaration.arity = entry.declaration.params) (indexSize : indices.length = entry.declaration.params)
    (motiveTyped : HasType env ctx true motive (viewMotiveType dependent (.node (.ind family entry.declaration.arity) indices)))
    (generated : viewCaseTypes env family entry.declaration.params ctx.length entry.signatures indices motive true dependent = some types)
    (branches : BranchTypes env ctx true types cases)
    (arguments : Arguments env ctx true entry.declaration.data (signatureTerm family signature) values result)
    (size : values.length = signature.fields.length)
    (parameters : Conversion.ListRel (Conversion.Conv env) indices (values.take entry.declaration.params))
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans)
    (planFound : plans[position]? = some plan)
    (valueFound : (values.drop entry.declaration.params)[position]? = some value)
    (self : plan.self = true) :
    HasType env ctx true (viewTerm true family motive cases (.borrow value))
      (viewResult dependent motive (.borrow value)) := by
  have fieldSource := viewPlan_source planned
  have storedField : signature.fields[entry.declaration.params+position]? = some plan.field := by
    rw [← List.getElem?_drop,← fieldSource]
    simp only [List.getElem?_map,planFound,Option.map_some]
  obtain ⟨count,fieldIndices,domain,borrowed⟩ := plan_self_domain
    (viewPlan_valid planned plan (List.mem_of_getElem? planFound)) self
  have shape := signature_recursive_metadata history found sigFound _ _ storedField
  have recursive := shape.1 count fieldIndices domain
  have actual := recursive_view_argument history found sigFound dataIs arity arguments size storedField
    (by simpa only [List.getElem?_drop] using valueFound) recursive
  have observed := HasType.convert actual (.node _ (related_symm parameters))
  have borrowedTyped := HasType.ghostBorrowOwned observed (Owned.family found boxed (.refl _))
  exact HasType.view found dataIs boxed arity indexSize borrowedTyped motiveTyped
    (Or.inl rfl) generated branches

end Jihoo.NativeKernel.Environment.FamilyIota
