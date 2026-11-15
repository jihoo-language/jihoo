import Jihoo.NativeLoanFamilyIotaInstantiation

/-! General field application for actual nonparameter Case telescopes.
All domains and branches originate in authentic checked-family derivations. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

/-- Execute the canonical field telescope and retain its independently given
result conversion. The environment hypothesis is derived from checked history
at callers, never supplied by the contraction implementation. -/
theorem arguments_consume (wf : UnifiedProgram.EnvWellFormed env)
    (arguments : Arguments env [] ctx true data telescope values result)
    (computed : consume telescope values = some output) : Conversion.Conv env output result := by
  induction values generalizing telescope with
  | nil =>
    simp only [consume,Option.some.injEq] at computed
    subst output
    cases arguments with
    | nil converted => exact converted
  | cons value values ih =>
    cases telescope with
    | var => simp [consume] at computed
    | node op children =>
      cases op <;> try simp [consume] at computed
      case pi erased =>
        cases children with
        | nil => simp [consume] at computed
        | cons domain children =>
          cases children with
          | nil => simp [consume] at computed
          | cons body children =>
            cases children with
            | nil =>
              exact ih (arguments_pi_view wf arguments).2 computed
            | cons _ _ => simp [consume] at computed

/-- A selected branch from the real generated list consumes exactly the real
constructor fields. No branch typing or telescope equality is reflected. -/
theorem case_branch_apply_no_parameters {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (parameters : entry.declaration.params = 0)
    (generated : dataCaseTypes family entry.declaration.params ctx.length entry.signatures [] motive false proof = some types)
    (branches : BranchTypes env [] ctx true types cases) (selected : cases[constructor]? = some branch)
    (arguments : Arguments env [] ctx true entry.declaration.data (signatureTerm family signature) values result)
    (size : values.length = signature.fields.length) :
    HasType env [] ctx true (applications branch values)
      (.app (applications motive (signature.result.map (Term.subst (fieldSubstitution values))))
        (.node (.con family constructor values.length) values)) := by
  rw [parameters] at generated
  obtain ⟨branchType,typeFound,built⟩ := dataCaseTypes_get generated sigFound
  have signatureScope := (signature_metadata history found sigFound).1
  have related := data_case_domains_no_parameters signatureScope built
  rw [← size] at related
  obtain ⟨output,computed,typed⟩ := apply_same_domains history.wellFormed related arguments
    (branch_get branches typeFound selected)
  have exactResult := consume_data_case_no_parameters signatureScope built size
  have same := Option.some.inj (computed.symm.trans exactResult)
  cases same
  exact typed

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
