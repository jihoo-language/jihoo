import Jihoo.NativeBindingMachineBudgetedRelease

/-! The actual complete mixed definition admission constructs the initial
source/value/size/loan authority. These are starting invariants; arbitrary
runtime-control preservation is not supplied as a caller certificate. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- Same original checked declaration initializes both directions of the loan
association and its exact original resource receipt, across the full syntax. -/
theorem checked_mixed_loan_authority
    (checked : LoanTyping.MixedProgram.DeclarationChecked env source expanded) :
    ∃ sort : SortTag,
      LoanClosingTyped env [] (Definitions.bodyMode sort) (.initial expanded.value) Term.var expanded.type ∧
      ValueContext env (.initial expanded.value) Term.var ∧
      OwnerSizes env SizedBufferHeap.empty (.initial expanded.value) Term.var ∧
      LoanSlots (.initial expanded.value) [] [] ∧ LoanCoverage (.initial expanded.value) [] [] ∧
      OwnerSlotsDistinct (.initial expanded.value) ∧
      (Definitions.bodyMode sort = false →
        LoanTyping.ResourceQuantity.ResourceSafe env expanded.value ∧
        ∃ fuel control, LoanTyping.ResourceQuantity.project fuel env [] [] expanded.value = some control ∧
          control.demand 0 = some 0 ∧ LoanTyping.ResourceQuantity.LoanBudget 0 [] control) := by
  obtain ⟨sort,typed,context,resource⟩ := checked_mixed_value_context_entry checked
  refine ⟨sort,typed,context,OwnerSizes.initial _ _ _,?_,LoanCoverage.empty _,OwnerSlotsDistinct.initial _,?_⟩
  · intro index active
    cases active
  · intro mode
    have safe := resource mode
    obtain ⟨scope,table,fuel,control,projected,zero,localScopes,controlScoped⟩ := resource mode
    exact ⟨safe,fuel,control,projected,zero,LoanTyping.ResourceQuantity.LoanBudget.empty _ _⟩

end Jihoo.NativeKernel.Environment.BindingMachine
