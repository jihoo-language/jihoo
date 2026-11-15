import Jihoo.NativeFamilyIotaCasePreservation
import Jihoo.NativeEnvironmentContextualPreservation

/-! An authentic indexed recursive data family: the nonrecursive Case branch
consumes dependent fields and returns a Buffer whose size is the result index.
The proof keeps the original type through iota, beta and pure Drop separately. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.CaseExamples
open UnifiedProgram

private def vector (n : Term) : Term := .node (.ind 0 1) [n]
private def declaration : FamilyDeclaration :=
  ⟨true,0,1,[vector (.natural 0),.pi true .u64 (.pi false (vector (.var 0))
    (vector (.uadd (.var 1) (.natural 1))))],0⟩
private def baseSignature : Signature := ⟨[],[.natural 0]⟩
private def stepSignature : Signature :=
  ⟨[⟨true,.u64,none⟩,⟨false,vector (.var 0),some [.var 0]⟩],[.uadd (.var 1) (.natural 1)]⟩
private def entry : CheckedFamily := ⟨declaration,[baseSignature,stepSignature],true⟩
private def env : Environment := ⟨#[],#[entry]⟩
private def z : Term := .node (.con 0 0 0) []
private def value : Term := .node (.con 0 1 2) [.natural 0,z]
private def motive : Term := .lam false .u64 (.lam false (vector (.var 0)) (.buffer (.var 1)))
private def branch : Term := .lam true .u64 (.lam false (vector (.var 0))
  (.node (.drop 0) [.var 0,.alloc (.uadd (.var 1) (.natural 1)) (.integer 0)]))
private def cases : List Term := [.alloc (.natural 0) (.integer 0),branch]
private def source : Term := caseTerm 0 motive cases value
private def reduct : Term := applications branch [.natural 0,z]
private def dropped : Term := .node (.drop 0) [z,.alloc (.natural 1) (.integer 0)]

private theorem history : UnifiedProgramChecked [] [declaration] env :=
  checkProgram_sound (by cbv : checkProgram 40 64 [] [declaration] = some env)

theorem authentic_indexed_case_is_checked :
    Checker.check 40 env [] true source (.buffer (.natural 1)) = true := by cbv

theorem indexed_case_has_actual_iota_root : Root env source reduct :=
  contract_sound (by cbv : contract env source = some reduct)

theorem all_dependent_fields_keep_exact_original_type :
    HasType env [] true reduct (.buffer (.natural 1)) := by
  exact case_preserves_no_parameters (family := 0) (constructor := 1) history
    (entry := entry) (signature := stepSignature) (values := [.natural 0,z])
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (Checker.check_sound authentic_indexed_case_is_checked)

theorem actual_converter_completes_case :
    Conversion.normalize? env 40 source = some (.alloc (.natural 1) (.integer 0)) := by cbv

theorem full_search_keeps_original_buffer_index :
    HasType env [] true (.alloc (.natural 1) (.integer 0)) (.buffer (.natural 1)) :=
  (Checker.check_sound authentic_indexed_case_is_checked).ghostNormalize history actual_converter_completes_case

/-- The explicit beta/drop derivation remains available independently of search. -/
theorem pure_drop_completes_typed_case :
    HasType env [] true (.alloc (.natural 1) (.integer 0)) (.buffer (.natural 1)) :=
  all_dependent_fields_keep_exact_original_type.ghostNormalize history
    (by cbv : Conversion.normalize? env 40 reduct = some (.alloc (.natural 1) (.integer 0)))

end Jihoo.NativeKernel.Environment.FamilyIota.CaseExamples
