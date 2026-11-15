import Jihoo.NativeLendRawAPI
import Jihoo.NativeLendRawSearch
import Jihoo.NativeEnvironmentConversion

/-! Loan64 has its own genuine raw Lend/family/delta/ACU equality. Default60
keeps the existing Family conversion. The bounded search uses the actual raw Lend/family/delta/ACU contractor.
Successful search is proved by actual raw paths; typed dependent finish
preservation is a separate source-specialized theorem. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.Conversion

abbrev Conv := RawLend.Conv
abbrev ListRel := NativeKernel.Conversion.ListRel
abbrev Closed := EnvironmentDelta.Basis.Closed
abbrev treeSize := NativeKernel.Conversion.treeSize
abbrev treeDepth := NativeKernel.Conversion.treeDepth
abbrev substitutionSafe := NativeKernel.Conversion.substitutionSafe
abbrev normalize? := RawLend.Search.normalize?
abbrev normalize := RawLend.Search.normalize
abbrev equal := RawLend.Search.equal

theorem ofLegacy (converted : NativeKernel.Conversion.Conv first second) : Conv env first second :=
  .legacy converted

theorem normalize?_sound (accepted : normalize? env fuel term = some result) : Conv env term result :=
  (RawLend.Search.normalize?_sound accepted)

theorem normalize?_forward (accepted : normalize? env fuel term = some result) : RawLend.Forward env term result :=
  (RawLend.Search.normalize?_forward accepted)

theorem normalize_sound (env : Environment) (fuel : Nat) (term : Term) : Conv env term (normalize env fuel term) :=
  (RawLend.Search.normalize_sound env fuel term)

theorem equal_sound (accepted : equal env fuel first second = true) : Conv env first second :=
  (RawLend.Search.equal_sound accepted)

end Jihoo.NativeKernel.Environment.LoanTyping.Conversion
