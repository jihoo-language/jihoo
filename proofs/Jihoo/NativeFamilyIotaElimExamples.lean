import Jihoo.NativeFamilyIotaPreservation

/-! Real indexed data and proposition induction exercise the unified actual
contractor endpoint with dependent fields and actual recursive calls. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.ElimExamples
open UnifiedProgram

private def vector (n : Term) : Term := .node (.ind 0 1) [n]
private def dataDeclaration : FamilyDeclaration :=
  ⟨true,0,1,[vector (.natural 0),.pi true .u64 (.pi false (vector (.var 0))
    (vector (.uadd (.var 1) (.natural 1))))],0⟩
private def dataBase : Signature := ⟨[],[.natural 0]⟩
private def dataStep : Signature :=
  ⟨[⟨true,.u64,none⟩,⟨false,vector (.var 0),some [.var 0]⟩],[.uadd (.var 1) (.natural 1)]⟩
private def dataEntry : CheckedFamily := ⟨dataDeclaration,[dataBase,dataStep],true⟩
private def dataEnv : Environment := ⟨#[],#[dataEntry]⟩
private def z : Term := .node (.con 0 0 0) []
private def value : Term := .node (.con 0 1 2) [.natural 0,z]
private def dataMotive : Term := .lam false .u64 (.lam false (vector (.var 0)) (.buffer (.var 1)))
private def dataBranch : Term := .lam true .u64 (.lam true (vector (.var 0))
  (.lam false (.buffer (.var 1)) (.alloc (.uadd (.var 2) (.natural 1)) (.integer 0))))
private def dataCases : List Term := [.alloc (.natural 0) (.integer 0),dataBranch]
private def dataSource : Term := elimTerm 0 dataMotive dataCases value
private def dataResult : Term := applications dataBranch [.natural 0,z,elimTerm 0 dataMotive dataCases z]
private def dataOriginalType : Term := .app (.app dataMotive (.natural 1)) value

private theorem dataHistory : UnifiedProgramChecked [] [dataDeclaration] dataEnv :=
  checkProgram_sound (by cbv : checkProgram 48 64 [] [dataDeclaration] = some dataEnv)

theorem indexed_data_induction_is_authentic : HasType dataEnv [] true dataSource dataOriginalType :=
  Checker.check_sound (fuel := 48) (by cbv)

theorem indexed_data_contractor_passes_actual_ih : contract dataEnv dataSource = some dataResult := by cbv

theorem indexed_data_contractor_preserves_original_dependent_type : HasType dataEnv [] true dataResult dataOriginalType :=
  contract_preserves dataHistory indexed_data_contractor_passes_actual_ih indexed_data_induction_is_authentic

private def propDeclaration : FamilyDeclaration :=
  ⟨false,0,1,[vector (.natural 0),.pi false .u64 (.pi true (vector (.var 0))
    (vector (.uadd (.var 1) (.natural 1))))],0⟩
private def propBase : Signature := ⟨[],[.natural 0]⟩
private def propStep : Signature :=
  ⟨[⟨false,.u64,none⟩,⟨true,vector (.var 0),some [.var 0]⟩],[.uadd (.var 1) (.natural 1)]⟩
private def propEntry : CheckedFamily := ⟨propDeclaration,[propBase,propStep],false⟩
private def propEnv : Environment := ⟨#[],#[propEntry]⟩
private def propMotive : Term := .lam false .u64 (.eq (.var 0) (.var 0))
private def propBranch : Term := .lam false .u64 (.lam true (vector (.var 0))
  (.lam true (.eq (.var 1) (.var 1)) (.refl (.uadd (.var 2) (.natural 1)))))
private def propCases : List Term := [.refl (.natural 0),propBranch]
private def propSource : Term := elimTerm 0 propMotive propCases value
private def propResult : Term := applications propBranch [.natural 0,z,elimTerm 0 propMotive propCases z]
private def propOriginalType : Term := .app propMotive (.natural 1)

private theorem propHistory : UnifiedProgramChecked [] [propDeclaration] propEnv :=
  checkProgram_sound (by cbv : checkProgram 48 64 [] [propDeclaration] = some propEnv)

theorem indexed_proposition_induction_is_authentic : HasType propEnv [] true propSource propOriginalType :=
  Checker.check_sound (fuel := 48) (by cbv)

theorem indexed_proposition_contractor_passes_actual_ih : contract propEnv propSource = some propResult := by cbv

theorem indexed_proposition_contractor_preserves_original_type : HasType propEnv [] true propResult propOriginalType :=
  contract_preserves propHistory indexed_proposition_contractor_passes_actual_ih indexed_proposition_induction_is_authentic

end Jihoo.NativeKernel.Environment.FamilyIota.ElimExamples
