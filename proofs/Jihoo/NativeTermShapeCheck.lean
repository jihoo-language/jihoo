import Jihoo.NativeSchema

/-! Computable native payload and arity validation, independently of typing.
All annotations and discarded subterms participate in the traversal. -/
namespace Jihoo.NativeKernel

mutual
  def shapeCheck : Term → Bool
    | .var index => decide (index < 2^32)
    | .node op children => NativeSchema.payloadBounded op &&
        decide (children.length = op.arity) && shapeCheckArgs children
  termination_by term => sizeOf term
  decreasing_by all_goals simp_wf; all_goals omega

  def shapeCheckArgs : List Term → Bool
    | [] => true
    | term :: rest => shapeCheck term && shapeCheckArgs rest
  termination_by children => sizeOf children
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem shapeCheck_wellFormed (checked : shapeCheck term = true) : term.WellFormed := by
  induction term using Term.rec
    (motive_2 := fun children => shapeCheckArgs children = true → ∀ term ∈ children, term.WellFormed) with
  | var => simp only [Term.WellFormed]
  | node op children ih =>
      simp only [shapeCheck] at checked
      have fields := Bool.and_eq_true_iff.mp checked
      have arity := (Bool.and_eq_true_iff.mp fields.1).2
      simp only [Term.WellFormed]
      exact ⟨of_decide_eq_true arity,ih fields.2⟩
  | nil => rename_i checked term member; cases member
  | cons first rest firstIH restIH =>
      rename_i both term member
      simp only [shapeCheckArgs] at both
      obtain ⟨firstChecked,restChecked⟩ := Bool.and_eq_true_iff.mp both
      rcases List.mem_cons.mp member with rfl | member
      · exact firstIH firstChecked
      · exact restIH restChecked term member

theorem shapeCheck_node (checked : shapeCheck (.node op children) = true) :
    NativeSchema.payloadBounded op = true ∧ children.length = op.arity ∧
      ∀ term ∈ children, shapeCheck term = true := by
  simp only [shapeCheck] at checked
  have fields := Bool.and_eq_true_iff.mp checked
  obtain ⟨payload,arity⟩ := Bool.and_eq_true_iff.mp fields.1
  refine ⟨payload,of_decide_eq_true arity,?_⟩
  have allChecked : ∀ terms, shapeCheckArgs terms = true → ∀ term ∈ terms, shapeCheck term = true := by
    intro terms
    induction terms with
    | nil => intro _ term member; cases member
    | cons first rest ih =>
        intro both term member
        simp only [shapeCheckArgs] at both
        obtain ⟨firstChecked,restChecked⟩ := Bool.and_eq_true_iff.mp both
        rcases List.mem_cons.mp member with rfl | member
        · exact firstChecked
        · exact ih restChecked term member
  exact allChecked children fields.2

end Jihoo.NativeKernel
