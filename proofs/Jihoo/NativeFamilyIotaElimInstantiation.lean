import Jihoo.NativeFamilyIotaElimHypotheses

/-! Authentic indexed Elim fields and final result instantiate exactly. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem instantiated_same_domains (fields : List Field) (position : Nat) :
    SameDomains fields.length
      (closeDataFields (instantiatedFields depth ps false position fields) first)
      (closeDataFields (instantiatedFields depth ps recursion position fields) second) := by
  induction fields generalizing position with
  | nil => exact .zero _ _
  | cons field fields ih =>
    simpa only [instantiatedFields,Bool.false_and,Bool.false_eq_true,ite_false,closeDataFields,List.foldr_cons,List.length_cons] using
      SameDomains.step field.erased (if recursion && field.recursive.isSome then true else field.erased)
        (field.domain.subst (parameterAt depth position ps)) (ih (position+1))

/-- Recursive erasure annotations change no ghost field domain. -/
theorem signature_leading_domains_all (scope : UnifiedProgram.SignatureScoped signature)
    (bound : params ≤ signature.fields.length) (size : ps.length = params)
    (computed : consume (signatureTerm family signature) ps = some telescope)
    (generated : dataCaseType family constructor params depth signature ps motive recursion proof = some type) :
    SameDomains (signature.fields.length-params) telescope type := by
  rw [consume_signature_leading family signature params ps bound size] at computed
  cases computed
  have instantiated := closeDataFields_subst
    ((signature.fields.drop params).map (fun field => (field.erased,field.domain))) 0
    (.node (.ind family signature.result.length) signature.result) (fieldSubstitution ps)
  simp only [liftSub,Nat.zero_add] at instantiated
  rw [instantiated]
  have scopes : ∀ (j : Nat) field,(signature.fields.drop params)[j]? = some field →
      field.domain.Scoped (0+j+ps.length) := by
    intro j field found
    have original := scope.domains (params+j) field (by simpa only [List.getElem?_drop] using found)
    have levels : 0+j+ps.length = params+j := by omega
    rw [levels]
    exact original
  rw [transform_fields_parameters _ ps 0 depth scopes]
  unfold dataCaseType at generated
  split at generated
  · contradiction
  · cases generated
    simpa only [List.length_drop] using instantiated_same_domains (depth := depth) (ps := ps)
      (recursion := recursion) (signature.fields.drop params) 0

/-- The actual prefix of field values instantiates recursive indices after
the same leading-parameter substitution used by branch generation. -/
theorem recursive_indices_instantiation {indices ps prefixValues : List Term} {position depth : Nat} (scopes : ∀ term ∈ indices,term.Scoped (position+ps.length))
    (size : prefixValues.length = position) :
    (indices.map (Term.subst (parameterAt depth position ps))).map (Term.subst (fieldSubstitution prefixValues)) =
      indices.map (Term.subst (fieldSubstitution (ps ++ prefixValues))) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro term member
  have scope := scopes term member
  rw [← size] at scope
  simp only [Function.comp_apply]
  rw [← size,← fieldSubstitution_lift_scoped (depth := depth) scope,Term.subst_comp,← fieldSubstitution_append]

/-- All recursive result binders disappear by genuine binder cancellation.
The resulting constructor and result indices are the actual original ones. -/
theorem dataCaseResult_recursive_instantiation (scope : UnifiedProgram.SignatureScoped signature)
    (ps values hypotheses : List Term) (size : ps.length+values.length = signature.fields.length) :
    (dataCaseResult family constructor params values.length hypotheses.length ps motive
      (signature.result.map (Term.subst (parameterAt depth values.length ps)))).subst
      (fieldSubstitution (values ++ hypotheses)) =
      .app (applications motive ((signature.result.map (Term.subst (fieldSubstitution (ps ++ values)))).drop params))
        (.node (.con family constructor (ps ++ values).length) (ps ++ values)) := by
  rw [dataCaseResult_hypotheses_shift,Term.subst_rename,fieldSubstitution_append_shift,
    dataCaseResult_instantiation,List.map_drop,case_result_indices_instantiation scope ps values size]

end Jihoo.NativeKernel.Environment.FamilyIota
