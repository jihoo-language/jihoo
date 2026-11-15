import Jihoo.NativeLoanFamilyIotaCase

/-! Constructor-result alignment follows the actual dependent argument
derivation and the authenticated signature; no result-type oracle is used. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

theorem signatureTerm_close_fields (family : Nat) (signature : Signature) :
    signatureTerm family signature =
      closeDataFields (signature.fields.map (fun field => (field.erased,field.domain)))
        (.node (.ind family signature.result.length) signature.result) := by
  rcases signature with ⟨fields,indices⟩
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    simp only [signatureTerm,closeDataFields,List.map_cons,List.foldr_cons] at ih ⊢
    exact congrArg (Term.pi field.erased field.domain) ih

theorem consume_signature (family : Nat) (signature : Signature) (values : List Term)
    (size : values.length = signature.fields.length) :
    consume (signatureTerm family signature) values =
      some (.node (.ind family signature.result.length)
        (signature.result.map (Term.subst (fieldSubstitution values)))) := by
  rw [signatureTerm_close_fields,consume_close_fields _ _ _ (by simpa only [List.length_map] using size.symm)]
  simp only [Term.subst,substArgs_dataInd]

theorem constructor_result_conversion (wf : UnifiedProgram.EnvWellFormed env)
    (arguments : Arguments env [] ctx true data (signatureTerm family signature) values result)
    (size : values.length = signature.fields.length) :
    Conversion.Conv env (.node (.ind family signature.result.length)
      (signature.result.map (Term.subst (fieldSubstitution values)))) result :=
  arguments_consume wf arguments (consume_signature family signature values size)

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
