import Jihoo.NativeCoreConstructorTelescopeAlignment
import Jihoo.NativeViewBindingAlgebra

/-! Every constructor of a checked data family has a View plan. The
classification uses the earlier-prefix field check and looks up external
families in the current environment. -/
namespace Jihoo.NativeKernel.NativeCoreViewCheckedPlan

open Environment UnifiedProgram.Families

private theorem checked_field_plan
    {before after : Environment} (extension : before.Extends after) (data : declaration.data = true)
    (checked : FieldChecked before family declaration ctx erased domain field) :
    ∃ plan, viewFieldPlan after family field = some plan := by
  cases checked with
  | recursive arity _ _ erasedData _ =>
    simp only [data,Bool.not_true] at erasedData
    subst erased
    unfold viewFieldPlan
    simp only [Bool.false_eq_true,ite_false]
    exact ⟨_,rfl⟩
  | ordinary selfFree expansion binder conversion normalized runtime =>
    rename_i expanded sourceSort normal normalSort
    cases erased with
    | true => exact ⟨_,rfl⟩
    | false =>
      cases normal with
      | var => simp [runtimeFieldOK,data] at runtime
      | node op args =>
        cases op <;> simp [runtimeFieldOK,data] at runtime
        case ind actual arity =>
          by_cases own : actual = family
          · simp only [viewFieldPlan,Bool.false_eq_true,ite_false,ite_eq_left own]
            exact ⟨_,rfl⟩
          · cases read : before.families[actual]? with
            | none => simp [read] at runtime
            | some found =>
              have kept := extension.families actual found read
              simp only [viewFieldPlan,Bool.false_eq_true,ite_false,ite_eq_right own,kept,Option.map_some]
              exact ⟨_,rfl⟩
        all_goals
          rcases args with _ | ⟨_,_ | ⟨_,_⟩⟩
          all_goals simp at runtime
          all_goals exact ⟨_,rfl⟩

private theorem checked_fields_have_plans
    {before after : Environment} (extension : before.Extends after) (data : declaration.data = true)
    (checked : TelescopeChecked before family declaration previous source signature)
    (earlier : ∀ field ∈ previous, ∃ plan, viewFieldPlan after family field = some plan) :
    ∀ field ∈ signature.fields, ∃ plan, viewFieldPlan after family field = some plan := by
  induction checked with
  | result => exact earlier
  | field checked _ ih =>
    apply ih
    intro field member
    rcases List.mem_append.mp member with fromEarlier | fromCurrent
    · exact earlier field fromEarlier
    · have same := List.mem_singleton.mp fromCurrent
      subst field
      exact checked_field_plan extension data checked

private theorem collect_view_plans
    (checked : ∀ field ∈ fields, ∃ plan, viewFieldPlan env family field = some plan) :
    ∃ plans, viewPlan env family fields = some plans := by
  induction fields with
  | nil => exact ⟨[],rfl⟩
  | cons field fields ih =>
    obtain ⟨plan,planned⟩ := checked field (by simp)
    obtain ⟨plans,tail⟩ := ih (fun field member => checked field (List.mem_cons_of_mem _ member))
    refine ⟨plan :: plans,?_⟩
    unfold viewPlan at tail ⊢
    simp only [List.mapM_cons,planned,Bind.bind,Option.bind,tail,Pure.pure]

/-- The actual checked constructor yields its complete View plan after the
declared parameter prefix. -/
theorem checked_constructor_plan
    {entry : CheckedFamily} {constructor : Nat} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (signatureFound : entry.signatures[constructor]? = some signature)
    (data : entry.declaration.data = true) :
    ∃ plans, viewPlan env family (signature.fields.drop entry.declaration.params) = some plans := by
  obtain ⟨_,_,prior,declaration,_,index,familyChecked,extension⟩ := history.family_prefix found
  obtain ⟨_,_,telescope⟩ := familyChecked.signatures.right signatureFound
  rw [index] at telescope
  have checkedData : declaration.data = true := by
    simpa only [familyChecked.declaration] using data
  have fields := checked_fields_have_plans extension checkedData telescope
    (fun _ absent => False.elim (List.not_mem_nil absent))
  apply collect_view_plans
  intro field member
  exact fields field (List.mem_of_mem_drop member)

end Jihoo.NativeKernel.NativeCoreViewCheckedPlan
