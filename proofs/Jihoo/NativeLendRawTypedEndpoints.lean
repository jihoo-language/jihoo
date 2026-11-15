import Jihoo.NativeLendRawAPI
import Jihoo.NativeLendGhostRule

/-! Actual source Lend reaches an independently derived typed pure result.
This does not claim every raw macro intermediate has the dependent source type:
only the specialized typed endpoint is asserted. -/
namespace Jihoo.NativeKernel.Environment.RawLend

theorem lendTerm_source (owner reader continuation : Term) :
    lendTerm owner reader continuation = .lend owner reader continuation := rfl

theorem desugar_source (owner reader continuation : Term) :
    desugar owner reader continuation = Lending.desugar owner reader continuation := rfl

/-- The raw Lend equation reaches the same concrete dependent beta finish used
by the source-specialized checker. No callback typing premise is needed for
this syntax theorem. -/
theorem explicit_callbacks_forward (owner domain readerBody first again body : Term) :
    Forward env (lendTerm owner (.lam false domain readerBody) (.lam false first (.lam false again body)))
      (Lending.finish owner body (Lending.read owner readerBody)) := by
  refine (Forward.lend owner _ _).trans ?_
  rw [desugar_source]
  exact .old (.old (Lending.desugar_forward owner domain readerBody first again body))

/-- Actual generic or specialized dependent source subchecks construct a typed
pure endpoint reached from the raw Lend source by genuine finite computation.
No final output typing or callback-at-arbitrary-input oracle is a premise. -/
theorem ghost_derivation_typed_endpoint (wf : UnifiedProgram.EnvWellFormed env)
    (derived : Lending.GhostDerivation env ctx (.lend owner reader continuation) type) :
    ∃ output,Forward env (lendTerm owner reader continuation) output ∧ HasType env ctx true output type := by
  obtain ⟨output,path,typed⟩ := derived.sound wf
  refine ⟨output,(Forward.lend owner reader continuation).trans ?_,typed⟩
  rw [desugar_source]
  exact .old (.old path)

end Jihoo.NativeKernel.Environment.RawLend
