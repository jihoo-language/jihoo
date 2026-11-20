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

private theorem constructor_arguments_count (wf : UnifiedProgram.EnvWellFormed env)
    (typed : Arguments env [] ctx true data (closeDataFields fields (.node (.ind family arity) indices)) values
      (.node (.ind family resultArity) resultIndices)) : values.length = fields.length := by
  induction values generalizing fields indices with
  | nil =>
      cases fields with
      | nil => rfl
      | cons field fields =>
          cases typed with
          | nil related =>
              exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .pi field.1)
                (op' := .ind family resultArity) rfl rfl (by intro eq; cases eq) related wf.admissible)
  | cons value values ih =>
      cases fields with
      | nil =>
          cases typed with
          | cons related _ _ =>
              exact False.elim (RawLend.Conv.full_rigid_disjoint (op := .ind family arity)
                rfl rfl (by intro eq; cases eq) related wf.admissible)
      | cons field fields =>
          have tail := (arguments_pi_view wf typed).2
          change Arguments env [] ctx true data
            ((closeDataFields fields (.node (.ind family arity) indices)).subst (single value)) values
            (.node (.ind family resultArity) resultIndices) at tail
          have transform := closeDataFields_subst fields 0 (.node (.ind family arity) indices) (single value)
          simp only [liftSub, Nat.zero_add, Term.subst, substArgs_dataInd] at transform
          rw [transform] at tail
          have count := ih tail
          rw [transformDataFields_length] at count
          exact congrArg Nat.succ count

/-- A checked constructor uses exactly its signature's field count. A Pi
head cannot be confused with the terminal Ind, even beneath conversion. -/
theorem checked_constructor_fields (history : ScopedProgram.History definitions declarations env)
    (typed : HasType env [] ctx true (.node (.con family constructor count) values) type) :
    ∃ entry signature, env.families[family]? = some entry ∧
      entry.signatures[constructor]? = some signature ∧ values.length = signature.fields.length := by
  obtain ⟨entry, signature, _, _, found, sig, arguments, _⟩ := typed.principalView
  have signatureScope := (signature_metadata history found sig).1.signatureTerm_scoped family
  rw [closed_rename signatureScope, signatureTerm_close_fields] at arguments
  exact ⟨entry, signature, found, sig,
    (constructor_arguments_count history.wellFormed arguments).trans (List.length_map _)⟩

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
