import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanLendPreservation

/-! Source-only input certificates for explicit Lend. Generic cases derive
the specialized read by actual beta preservation; dependent cases retain its
actual checked derivation. No callback typing is added to a dependent rule. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem HasType.explicitLendInputs (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body))) type) :
    ∃ ownerType valueType,HasType env [] ctx true owner ownerType ∧ Owned env ownerType ∧
      HasType env [] ctx true (Lending.read owner readerBody) valueType ∧ Outlived env valueType := by
  obtain ⟨principal,origin,converted⟩ := typed.lendView
  cases origin with
  | generic owner owned outlived reader continuation allowed =>
      exact ⟨_,_,owner.ghost [],owned,reader_from_generic_checks wf owner owned reader,outlived⟩
  | dependentCode owner owned binder domain reader outlived first again continuation normalized shifted allowed =>
      exact ⟨_,_,owner.ghost [],owned,reader.ghost [],outlived⟩
  | dependentGhost owner owned binder domain reader outlived first again continuation normalized shifted =>
      exact ⟨_,_,owner.ghost [],owned,reader.ghost [],outlived⟩

end Jihoo.NativeKernel.Environment.LoanTyping
