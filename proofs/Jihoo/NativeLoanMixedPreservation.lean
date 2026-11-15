import Jihoo.NativeLoanMixedAdmission
import Jihoo.NativeLoanFamilyContextualEvaluation

/-! The actual Loan64/resource mixed history supplies the authentic family
provenance used by original-type contextual preservation. No legacy global
typing history or successful-output typing certificate is supplied. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram

theorem History.family_contract_preserves
    (history : History definitions declarations env)
    (contracted : Environment.FamilyIota.contract env term = some result)
    (typed : HasType env [] ctx true term type) : HasType env [] ctx true result type :=
  FamilyIota.contract_preserves (ScopedProgram.History.ofLoanMixed history) contracted typed

theorem History.contextual_preservation
    (history : History definitions declarations env)
    (steps : FamilyEvaluation.Steps env term result)
    (typed : HasType env loans ctx mode term type) :
    RawLend.Forward env term result ∧ HasType env [] ctx true result type :=
  steps.typed_forward (ScopedProgram.History.ofLoanMixed history) typed

theorem History.signature_metadata {family constructor : Nat}
    {entry : CheckedFamily} {signature : Signature}
    (history : History definitions declarations env)
    (found : env.families[family]? = some entry)
    (selected : entry.signatures[constructor]? = some signature) :
    UnifiedProgram.SignatureScoped signature ∧ signature.result.length = entry.declaration.arity ∧
      FamilyIota.Parameters env entry.declaration.params signature :=
  FamilyIota.signature_metadata (ScopedProgram.History.ofLoanMixed history) found selected

theorem legacy_history_contract_preserves
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (contracted : Environment.FamilyIota.contract env term = some result)
    (typed : HasType env [] ctx true term type) : HasType env [] ctx true result type :=
  FamilyIota.contract_preserves (ScopedProgram.History.ofUnified history) contracted typed

end Jihoo.NativeKernel.Environment.LoanTyping.MixedProgram
