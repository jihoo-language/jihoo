import Jihoo.NativeFamilyIotaViewPreservation
import Jihoo.NativeEnvironmentContextualPreservation

/-! Actual borrowed View with a converted observed parameter and a dependent
owned Buffer field. The exact dependent original motive application survives. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.ViewExamples
open UnifiedProgram

private def box (n : Term) : Term := .node (.ind 0 1) [n]
private def declaration : FamilyDeclaration :=
  ⟨true,1,1,[.pi true .u64 (.pi false (.buffer (.var 0)) (box (.var 1)))],0⟩
private def signature : Signature :=
  ⟨[⟨true,.u64,none⟩,⟨false,.buffer (.var 0),none⟩],[.var 1]⟩
private def entry : CheckedFamily := ⟨declaration,[signature],true⟩
private def env : Environment := ⟨#[],#[entry]⟩
private def observed : Term := .uadd (.natural 1) (.natural 1)
private def allocation : Term := .alloc (.natural 2) (.integer 0)
private def constructor : Term := .node (.con 0 0 2) [.natural 2,allocation]
private def motive : Term := .lam false (.ref (box observed)) (.buffer observed)
private def branch : Term := .lam false (.ref (.buffer observed)) (.deref (.var 0))
private def cases : List Term := [branch]
private def source : Term := viewTerm false 0 motive cases (.borrow constructor)
private def originalType : Term := .app motive (.borrow constructor)
private def expected : Term :=
  (viewCaseType env 0 0 1 0 signature [observed] motive false true).getD (.natural 0)
private def target : Term := .app branch (.borrow allocation)

private theorem history : UnifiedProgramChecked [] [declaration] env :=
  checkProgram_sound (by cbv : checkProgram 40 64 [] [declaration] = some env)

theorem observed_borrowed_scrutinee_is_genuinely_converted :
    HasType env [] true (.borrow constructor) (.ref (box observed)) :=
  Checker.check_sound (fuel := 40) (by cbv)

theorem authentic_dependent_parameter_view : HasType env [] true source originalType := by
  have motiveTyped : HasType env [] true motive (viewMotiveType true (box observed)) :=
    Checker.check_sound (fuel := 40) (by cbv)
  have branchTyped : HasType env [] true branch expected := Checker.check_sound (fuel := 40) (by cbv)
  exact HasType.view (entry := entry) (indices := [observed]) (dependent := true)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    observed_borrowed_scrutinee_is_genuinely_converted motiveTyped (Or.inl rfl) (by cbv)
    (.cons branchTyped .nil)

theorem real_owned_buffer_is_borrowed_and_parameter_omitted :
    contract env source = some target := by cbv

theorem exact_original_dependent_result_is_preserved : HasType env [] true target originalType :=
  contract_view_one_level_preserves history real_owned_buffer_is_borrowed_and_parameter_omitted authentic_dependent_parameter_view

theorem branch_beta_and_real_deref_borrow_compute :
    Conversion.normalize? env 40 target = some allocation := by cbv

theorem original_dependent_type_survives_actual_beta : HasType env [] true allocation originalType :=
  exact_original_dependent_result_is_preserved.ghostNormalize history branch_beta_and_real_deref_borrow_compute

theorem incompatible_dependent_owned_field_rejected :
    Checker.infer 40 env [] true (.node (.con 0 0 2)
      [.natural 2,.alloc (.natural 3) (.integer 0)]) = none := by cbv

end Jihoo.NativeKernel.Environment.FamilyIota.ViewExamples
