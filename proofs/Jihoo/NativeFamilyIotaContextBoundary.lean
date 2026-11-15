import Jihoo.NativeFamilyIotaConversion
import Jihoo.NativeEnvironmentContextualPreservation

/-! The installed genuine enlarged conversion preserves the exact dependent
type when an actual family-iota redex changes a lambda annotation. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.ContextBoundary
open UnifiedProgram

private def nat : Term := .node (.ind 0 0) []
private def declaration : FamilyDeclaration := ⟨true,0,0,[nat,.pi false nat nat],0⟩
private def entry : CheckedFamily := ⟨declaration,[⟨[],[]⟩,⟨[⟨false,nat,some []⟩],[]⟩],true⟩
private def env : Environment := ⟨#[],#[entry]⟩
private def zero : Term := .node (.con 0 0 0) []
private def annotation : Term := .node (.drop 0) [zero,.u64]
private def source : Term := .lam false annotation (.var 0)
private def target : Term := .lam false .u64 (.var 0)
private def originalType : Term := .pi false annotation annotation

private theorem history : UnifiedProgramChecked [] [declaration] env :=
  checkProgram_sound (by cbv : checkProgram 32 64 [] [declaration] = some env)

theorem original_lambda_is_typed : HasType env [] true source originalType :=
  Checker.check_sound (fuel := 32) (by cbv)

theorem real_iota_changes_annotation : Extended.Forward env source target :=
  .node (.lam false) (.cons (.iota (.drop 0 zero .u64)) (.cons .refl .nil))

theorem target_keeps_exact_original_type : HasType env [] true target originalType :=
  original_lambda_is_typed.ghostFamilyForward history real_iota_changes_annotation

theorem genuine_enlarged_equation_is_available : Extended.Conv env source target :=
  real_iota_changes_annotation.toConv

end Jihoo.NativeKernel.Environment.FamilyIota.ContextBoundary
