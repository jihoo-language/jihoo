import Jihoo.NativeLoanCheckerSoundness

/-! These are executable regressions for actual Lend reduction in a well-typed
natural index and then inside an allocation's expected buffer type. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.LendConversionExamples

def buffer : Term := .buffer (.natural 2)
def owner : Term := .alloc (.natural 2) (.integer 0)
def index : Term := .lend owner (.lam false (.ref buffer) (.natural 2))
  (.lam false .u64 (.lam false buffer (.var 1)))
def indexedBuffer : Term := .buffer index

theorem index_checked : Checker.check 48 empty [] [] true index .u64 = true := by cbv

theorem index_typed : HasType empty [] [] true index .u64 := Checker.check_sound index_checked

theorem actual_lend_normalizes : Conversion.normalize? empty 24 index = some (.natural 2) := by cbv

theorem actual_lend_forward : RawLend.Forward empty index (.natural 2) :=
  Conversion.normalize?_forward actual_lend_normalizes

theorem allocation_with_lend_index_checked :
    Checker.check 48 empty [] [] false owner indexedBuffer = true := by cbv

theorem allocation_with_lend_index_typed : HasType empty [] [] false owner indexedBuffer :=
  Checker.check_sound allocation_with_lend_index_checked

theorem zero_fuel_fails : Conversion.normalize? empty 0 index = none := by rfl

theorem malformed_lend_is_not_contracted :
    RawLend.contract empty (.node .lend [.natural 2]) = none := by rfl

end Jihoo.NativeKernel.Environment.LoanTyping.LendConversionExamples
