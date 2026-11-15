import Jihoo.NativeLendRawAPI
import Jihoo.NativeFamilyIotaComputationSoundness

/-! The genuine untyped raw contractor. Its Lend equation matches the pure
source macro; specialized typed finish contraction is proved separately. -/
namespace Jihoo.NativeKernel.Environment.RawLend

def contract (env : Environment) : Term → Option Term
  | .node .lend [owner,reader,continuation] => some (desugar owner reader continuation)
  | term => FamilyIota.contract env term

theorem contract_forward (accepted : contract env term = some result) : Forward env term result := by
  fun_cases contract env term
  · simp only [contract,Option.some.injEq] at accepted
    subst result
    exact .lend _ _ _
  · simp_all only [contract]
    exact .old (.iota (FamilyIota.contract_sound accepted))

end Jihoo.NativeKernel.Environment.RawLend
