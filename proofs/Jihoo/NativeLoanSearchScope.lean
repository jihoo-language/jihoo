import Jihoo.NativeLoanForwardScope
import Jihoo.NativeLoanConversion

/-! The actual loan-aware bounded converter preserves an explicitly checked
input scope through genuine raw Lend/family/delta/ACU forward witnesses. The
total fallback result is covered too; no scope regularity of HasType is used. -/
namespace Jihoo.NativeKernel.Environment.RawLend.Search

theorem normalize?_scope (closed : EnvironmentDelta.Basis.Closed env)
    (accepted : normalize? env fuel term = some result) (scope : term.Scoped depth) : result.Scoped depth :=
  (normalize?_forward accepted).scope closed depth scope

theorem normalize?_scopeCheck (closed : EnvironmentDelta.Basis.Closed env)
    (accepted : normalize? env fuel term = some result) (checked : NativeKernel.scopeCheck depth term = true) :
    NativeKernel.scopeCheck depth result = true := scopeCheck_complete (normalize?_scope closed accepted (scopeCheck_sound checked))

theorem normalize_scope (closed : EnvironmentDelta.Basis.Closed env) (scope : term.Scoped depth) :
    (normalize env fuel term).Scoped depth := by
  unfold normalize
  cases accepted : normalize? env fuel term with
  | none => exact scope
  | some result => exact normalize?_scope closed accepted scope

theorem normalize_scopeCheck (closed : EnvironmentDelta.Basis.Closed env) (checked : NativeKernel.scopeCheck depth term = true) :
    NativeKernel.scopeCheck depth (normalize env fuel term) = true :=
  scopeCheck_complete (normalize_scope closed (scopeCheck_sound checked))

end Jihoo.NativeKernel.Environment.RawLend.Search

namespace Jihoo.NativeKernel.Environment.LoanTyping.Conversion

theorem normalize?_scope (closed : Closed env)
    (accepted : normalize? env fuel term = some result) (scope : term.Scoped depth) : result.Scoped depth :=
  RawLend.Search.normalize?_scope closed accepted scope

theorem normalize?_scopeCheck (closed : Closed env)
    (accepted : normalize? env fuel term = some result) (checked : NativeKernel.scopeCheck depth term = true) :
    NativeKernel.scopeCheck depth result = true := RawLend.Search.normalize?_scopeCheck closed accepted checked

theorem normalize_scope (closed : Closed env) (scope : term.Scoped depth) : (normalize env fuel term).Scoped depth :=
  RawLend.Search.normalize_scope closed scope

theorem normalize_scopeCheck (closed : Closed env) (checked : NativeKernel.scopeCheck depth term = true) :
    NativeKernel.scopeCheck depth (normalize env fuel term) = true := RawLend.Search.normalize_scopeCheck closed checked

end Jihoo.NativeKernel.Environment.LoanTyping.Conversion
