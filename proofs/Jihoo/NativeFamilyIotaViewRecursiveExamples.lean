import Jihoo.NativeFamilyIotaViewRecursivePreservation

/-! Two real recursive hypotheses, a converted leading parameter and the exact
original dependent motive application exercise the generic recursive endpoint. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.ViewRecursiveExamples
open UnifiedProgram

private def box (n : Term) : Term := .node (.ind 0 1) [n]
private def declaration : FamilyDeclaration := ⟨true,1,1,
  [.pi true .u64 (box (.var 0)),
   .pi true .u64 (.pi false (box (.var 0)) (.pi false (box (.var 1)) (box (.var 2))))],0⟩
private def signature0 : Signature := ⟨[⟨true,.u64,none⟩],[.var 0]⟩
private def signature1 : Signature :=
  ⟨[⟨true,.u64,none⟩,⟨false,box (.var 0),some [.var 0]⟩,⟨false,box (.var 1),some [.var 1]⟩],[.var 2]⟩
private def entry : CheckedFamily := ⟨declaration,[signature0,signature1],true⟩
private def env : Environment := ⟨#[],#[entry]⟩
private def observed : Term := .uadd (.natural 2) (.natural 1)
private def zero : Term := .node (.con 0 0 1) [.natural 3]
private def fork : Term := .node (.con 0 1 3) [.natural 3,zero,zero]
private def motive : Term := .lam false (.ref (box observed)) .u64
private def branch : Term := .lam false (.ref (box observed)) (.lam false (.ref (box observed))
  (.lam false .u64 (.lam false .u64 (.uadd (.var 1) (.var 0)))))
private def cases : List Term := [.natural 0,branch]
private def source : Term := viewTerm true 0 motive cases (.borrow fork)
private def originalType : Term := .app motive (.borrow fork)
private def expected : Term :=
  (viewCaseType env 0 1 1 0 signature1 [observed] motive true true).getD (.natural 0)
private def result : Term := applications branch
  [.borrow zero,.borrow zero,viewTerm true 0 motive cases (.borrow zero),viewTerm true 0 motive cases (.borrow zero)]

private theorem history : UnifiedProgramChecked [] [declaration] env :=
  checkProgram_sound (by cbv : checkProgram 48 64 [] [declaration] = some env)

theorem converted_parameter_source_is_authentic : HasType env [] true source originalType := by
  have motiveTyped : HasType env [] true motive (viewMotiveType true (box observed)) :=
    Checker.check_sound (fuel := 48) (by cbv)
  have scrutineeTyped : HasType env [] true (.borrow fork) (.ref (box observed)) :=
    Checker.check_sound (fuel := 48) (by cbv)
  have branchTyped : HasType env [] true branch expected := Checker.check_sound (fuel := 48) (by cbv)
  have zeroTyped : HasType env [] true (.natural 0)
      ((viewCaseType env 0 0 1 0 signature0 [observed] motive true true).getD (.natural 0)) :=
    Checker.check_sound (fuel := 48) (by cbv)
  exact HasType.view (entry := entry) (indices := [observed]) (dependent := true)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) scrutineeTyped motiveTyped (Or.inl rfl) (by cbv)
    (.cons zeroTyped (.cons branchTyped .nil))

theorem real_recursive_contraction_retains_both_hypotheses : contract env source = some result := by cbv

theorem recursive_contraction_preserves_exact_original_type : HasType env [] true result originalType :=
  contract_view_preserves history real_recursive_contraction_retains_both_hypotheses converted_parameter_source_is_authentic

end Jihoo.NativeKernel.Environment.FamilyIota.ViewRecursiveExamples
