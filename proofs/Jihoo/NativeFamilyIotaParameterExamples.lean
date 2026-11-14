import Jihoo.NativeFamilyIotaCasePreservation
import Jihoo.NativeEnvironmentContextualPreservation

/-! Converted observed parameters with a genuinely dependent Buffer field.
The scrutinee derivation retains a converted parameter prefix, so the full
parameter-alignment theorem is exercised, rather than a syntactic special case. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.ParameterExamples
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
private def motive : Term := .lam false (box observed) (.buffer observed)
private def branch : Term := .lam false (.buffer observed) (.var 0)
private def cases : List Term := [branch]
private def source : Term := caseTerm 0 motive cases constructor
private def originalType : Term := .buffer observed
private def expected : Term :=
  (dataCaseType 0 0 1 0 signature [observed] motive false false).getD (.natural 0)

private theorem history : UnifiedProgramChecked [] [declaration] env :=
  checkProgram_sound (by cbv : checkProgram 40 64 [] [declaration] = some env)

theorem observed_scrutinee_parameter_is_genuinely_converted :
    HasType env [] true constructor (box observed) :=
  Checker.check_sound (fuel := 40) (by cbv)

theorem authentic_dependent_parameter_case : HasType env [] true source originalType := by
  have motiveTyped : HasType env [] true motive (dataMotiveType 0 1 1 [observed] false) :=
    Checker.check_sound (fuel := 40) (by cbv)
  have branchTyped : HasType env [] true branch expected := Checker.check_sound (fuel := 40) (by cbv)
  have formed : HasType env [] true source (.app motive constructor) :=
    HasType.dataElim (analysis := true) (entry := entry) (indices := [observed])
      (proof := false) (by rfl) (by rfl) (by intro _;rfl) (by rfl) motiveTyped
      observed_scrutinee_parameter_is_genuinely_converted (by cbv)
      (.cons branchTyped .nil) (Or.inl rfl)
  exact .convert formed (Conversion.equal_sound (by cbv : Conversion.equal env 40 (.app motive constructor) originalType = true))

theorem full_parameter_iota_preserves_original_type :
    HasType env [] true (applications branch [allocation]) originalType := by
  exact case_preserves (family := 0) (constructor := 0) history
    (entry := entry) (signature := signature) (values := [.natural 2,allocation])
    (by rfl) (by rfl) (by rfl) (by rfl) authentic_dependent_parameter_case

theorem actual_beta_returns_original_buffer :
    Conversion.normalize? env 40 (applications branch [allocation]) = some allocation := by cbv

theorem exact_converted_parameter_retained_after_beta : HasType env [] true allocation originalType :=
  full_parameter_iota_preserves_original_type.ghostNormalize history actual_beta_returns_original_buffer

theorem incompatible_dependent_field_rejected :
    Checker.infer 40 env [] true (.node (.con 0 0 2)
      [.natural 2,.alloc (.natural 3) (.integer 0)]) = none := by cbv

private def changingParameter : FamilyDeclaration :=
  ⟨true,1,1,[.pi true .u64 (.pi false (.buffer (.var 0)) (box (.uadd (.var 1) (.natural 1))))],0⟩

theorem scoped_but_changed_constructor_parameter_rejected :
    Families.checkFamily 40 empty changingParameter = none := by cbv

end Jihoo.NativeKernel.Environment.FamilyIota.ParameterExamples
