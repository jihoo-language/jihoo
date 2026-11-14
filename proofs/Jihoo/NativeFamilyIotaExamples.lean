import Jihoo.NativeFamilyIotaBinding
import Jihoo.NativeFamilyIotaTyping
import Jihoo.NativeUnifiedProgram

/-! Concrete checked-family contractions, recursive and parameterized output
shapes, original dependent types, and malformed-input boundaries. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Examples
open UnifiedProgram

private def nat : Term := .node (.ind 0 0) []
private def declaration : FamilyDeclaration := ⟨true,0,0,[nat,.pi false nat nat],0⟩
private def entry : CheckedFamily := ⟨declaration,[⟨[],[]⟩,⟨[⟨false,nat,some []⟩],[]⟩],true⟩
private def env : Environment := ⟨#[],#[entry]⟩
private def z : Term := .node (.con 0 0 0) []
private def step : Term := .node (.con 0 1 1) [z]
private def oneCase : Term := .lam false (.ref nat) (.natural 1)
private def oneCases : List Term := [.natural 0,oneCase]
private def recursiveCase : Term := .lam false (.ref nat) (.lam false .u64 (.uadd (.var 0) (.natural 1)))
private def recursiveCases : List Term := [.natural 0,recursiveCase]
private def motive : Term := .lam false (.ref nat) .u64

private theorem history : UnifiedProgramChecked [] [declaration] env :=
  checkProgram_sound (by cbv : checkProgram 32 64 [] [declaration] = some env)

theorem nullary_view_contracts :
    contract env (viewTerm false 0 .u64 oneCases (.borrow z)) = some (.natural 0) := by cbv

theorem nullary_view_has_actual_root :
    Root env (viewTerm false 0 .u64 oneCases (.borrow z)) (.natural 0) :=
  contract_sound nullary_view_contracts

theorem nullary_view_preserves_converted_type :
    HasType env [] true (.natural 0) .u64 := by
  apply nullary_view_preserves (entry := entry) (family := 0) (indices := []) (constructor := 0)
    (recursion := false) (motive := .u64) (cases := oneCases)
    (by rfl) (by rfl) (by rfl) (by rfl)
  exact Checker.check_sound (fuel := 32) (by cbv)

theorem dependent_nullary_view_keeps_original_application :
    HasType env [] true (.natural 0) (.app motive (.borrow z)) := by
  apply nullary_view_preserves (entry := entry) (family := 0) (indices := []) (constructor := 0)
    (recursion := false) (motive := motive) (cases := oneCases)
    (by rfl) (by rfl) (by rfl) (by rfl)
  exact Checker.infer_sound (fuel := 32) (by cbv)

theorem recursive_view_passes_borrow_and_induction :
    contract env (viewTerm true 0 .u64 recursiveCases (.borrow step)) =
      some (.app (.app recursiveCase (.borrow z)) (viewTerm true 0 .u64 recursiveCases (.borrow z))) := by cbv

theorem one_level_view_has_no_recursive_result :
    contract env (viewTerm false 0 .u64 oneCases (.borrow step)) =
      some (.app oneCase (.borrow z)) := by cbv

private def dataMotive : Term := .lam false nat .u64
private def dataCase : Term := .lam true nat (.lam false .u64 (.uadd (.var 0) (.natural 1)))
private def dataCases : List Term := [.natural 0,dataCase]

theorem data_induction_passes_actual_recursive_term :
    contract env (elimTerm 0 dataMotive dataCases step) =
      some (.app (.app dataCase z) (elimTerm 0 dataMotive dataCases z)) := by cbv

theorem data_case_omits_induction :
    contract env (caseTerm 0 dataMotive [.natural 0,.lam false nat (.natural 1)] step) =
      some (.app (.lam false nat (.natural 1)) z) := by cbv

private def param (n : Term) : Term := .node (.ind 0 1) [n]
private def paramDeclaration : FamilyDeclaration :=
  ⟨true,1,1,[.pi true .u64 (param (.var 0)),
    .pi true .u64 (.pi false (param (.var 0)) (param (.var 1)))],0⟩
private def paramEntry : CheckedFamily :=
  ⟨paramDeclaration,[⟨[⟨true,.u64,none⟩],[.var 0]⟩,
    ⟨[⟨true,.u64,none⟩,⟨false,param (.var 0),some [.var 0]⟩],[.var 1]⟩],true⟩
private def paramEnv : Environment := ⟨#[],#[paramEntry]⟩
private def paramZ : Term := .node (.con 0 0 1) [.natural 3]
private def paramS : Term := .node (.con 0 1 2) [.natural 3,paramZ]

theorem parameterized_metadata_is_checked :
    checkProgram 40 64 [] [paramDeclaration] = some paramEnv := by cbv

private def paramRecursiveCase : Term := .lam false (.ref (param (.natural 3)))
  (.lam false .u64 (.uadd (.var 0) (.natural 1)))
private def paramViewCases : List Term := [.natural 0,paramRecursiveCase]
private def paramMotive : Term := .lam false (param (.natural 3)) .u64
private def paramCase : Term := .lam false (param (.natural 3)) (.natural 1)
private def paramCases : List Term := [.natural 0,paramCase]

theorem parameterized_view_source_is_typed :
    Checker.check 32 paramEnv [] true (viewTerm true 0 .u64 paramViewCases (.borrow paramS)) .u64 = true := by cbv

theorem parameterized_view_omits_parameter_argument :
    contract paramEnv (viewTerm true 0 .u64 paramViewCases (.borrow paramS)) =
      some (.app (.app paramRecursiveCase (.borrow paramZ))
        (viewTerm true 0 .u64 paramViewCases (.borrow paramZ))) := by cbv

theorem parameterized_case_omits_parameter_argument :
    contract paramEnv (caseTerm 0 paramMotive paramCases paramS) = some (.app paramCase paramZ) := by cbv

theorem borrowed_view_requires_reference : contract env (viewTerm false 0 .u64 oneCases step) = none := by cbv

theorem unknown_family_does_not_contract :
    contract empty (viewTerm false 0 .u64 oneCases (.borrow z)) = none := by cbv

theorem wrong_constructor_payload_does_not_contract :
    contract env (viewTerm false 0 .u64 oneCases (.borrow (.node (.con 0 1 0) [z]))) = none := by cbv

theorem wrong_case_count_does_not_contract :
    contract env (viewTerm false 0 .u64 [.natural 0] (.borrow z)) = none := by cbv

theorem symbolic_reference_stays_neutral :
    contract env (viewTerm true 0 .u64 recursiveCases (.var 0)) = none := by cbv

private def droppedType : Term := .node (.drop 0) [z,.u64]

theorem pure_drop_is_typed : HasType env [] true droppedType (.univ 0) := by
  exact Checker.check_sound (fuel := 32) (by cbv)

theorem pure_drop_preserves_original_type : HasType env [] true .u64 (.univ 0) :=
  drop_preserves pure_drop_is_typed

theorem pure_drop_is_new_root : Root env droppedType .u64 := .drop _ _ _

theorem pure_drop_is_not_silently_in_installed_conversion : ¬ Conversion.Conv env droppedType .u64 := by
  intro converted
  exact EnvironmentDelta.Basis.Conv.full_rigid_disjoint rfl rfl (by intro same; cases same)
    converted history.wellFormed.admissible

end Jihoo.NativeKernel.Environment.FamilyIota.Examples
