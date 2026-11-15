import Jihoo.NativeLoanFamilyIotaParameterCongruence
import Jihoo.NativeLoanFamilyIotaConstructor

/-! Concrete leading/field substitution algebra for leading parameters. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

theorem fieldSubstitution_append (leading suffix : List Term) :
    fieldSubstitution (leading ++ suffix) =
      fun x => (liftSub suffix.length (fieldSubstitution leading) x).subst (fieldSubstitution suffix) := by
  induction leading with
  | nil =>
    funext x
    simp only [List.nil_append,fieldSubstitution,liftSub_var,Term.subst]
  | cons value leading ih =>
    funext x
    change (liftSub (leading ++ suffix).length (single value) x).subst
      (fieldSubstitution (leading ++ suffix)) = _
    rw [ih,← Term.subst_comp]
    apply congrArg (fun (term : Term) => term.subst (fieldSubstitution suffix))
    simpa only [List.length_append,PartialRenaming.liftSub_add,fieldSubstitution] using
      congrFun (liftSub_comp suffix.length (liftSub leading.length (single value)) (fieldSubstitution leading)) x

theorem fieldSubstitution_parameterAt (values : List Term) :
    fieldSubstitution values = parameterAt 0 0 values := by
  funext x
  by_cases inside : x < values.length
  · have bound : values.length - 1 - x < values.length := by omega
    have selected := List.getElem?_eq_getElem bound
    have twice : values.length - 1 - (values.length - 1 - x) = x := by omega
    have first := fieldSubstitution_selected selected
    have second := parameterAt_field selected
    simpa only [twice] using first.trans second.symm
  · have above : x - values.length + values.length = x := by omega
    have shifted := fieldSubstitution_shift values (.var (x-values.length))
    simp only [Term.rename,Term.subst] at shifted
    rw [above] at shifted
    have absent : values.reverse[x]? = none := List.getElem?_eq_none (by simp only [List.length_reverse];omega)
    simp only [parameterAt,Nat.not_lt_zero,↓reduceIte,Nat.sub_zero,absent,Option.map_none,
      Option.getD_none,Nat.add_zero]
    exact shifted

private theorem liftSub_offset (locals : Nat) (σ : Nat → Term) (x : Nat) :
    liftSub locals σ (x+locals) = (σ x).rename (fun i => i+locals) := by
  induction locals with
  | zero =>
    change σ x = (σ x).rename id
    exact (Term.rename_id _).symm
  | succ locals ih =>
    change (liftSub locals σ (x+locals)).rename Nat.succ = (σ x).rename (fun i => i+(locals+1))
    rw [ih,Term.rename_comp]
    rfl

theorem liftSub_fieldSubstitution (values : List Term) (locals : Nat) :
    liftSub locals (fieldSubstitution values) = parameterAt 0 locals values := by
  funext x
  by_cases bound : x < locals
  · have stable := scoped_subst_lift (Term.Scoped.var bound) (fieldSubstitution values)
    simp only [Term.subst] at stable
    simpa only [parameterAt,bound,↓reduceIte] using stable
  · have index : x = (x-locals)+locals := by omega
    rw [index,liftSub_offset]
    rw [fieldSubstitution_parameterAt]
    have high : ¬ x-locals+locals < locals := by omega
    simp only [parameterAt,Nat.not_lt_zero,bound,high,↓reduceIte,Nat.sub_zero,Nat.add_sub_cancel]
    cases selected : values.reverse[x-locals]? with
    | none =>
      have above := List.getElem?_eq_none_iff.mp selected
      simp only [List.length_reverse] at above
      simp only [selected,Option.map_none,Option.getD_none,Term.rename]
      congr 1
      omega
    | some value =>
      simp only [selected,Option.map_some,Option.getD_some,Term.rename_comp,Nat.add_zero]

theorem fieldSubstitution_lift_scoped {term : Term} {values : List Term}
    (scope : term.Scoped (locals + values.length)) :
    term.subst (liftSub locals (fieldSubstitution values)) = term.subst (parameterAt depth locals values) := by
  rw [liftSub_fieldSubstitution]
  have natural := parameterAt_subst scope Term.var 0 depth
  have identity : Term.subst Term.var = id := by funext term;exact Term.subst_id term
  simpa only [liftSub_var,Term.subst_id,identity,List.map_id] using natural

private theorem close_fields_append (leading trailing : List (Bool × Term)) (body : Term) :
    closeDataFields (leading ++ trailing) body = closeDataFields leading (closeDataFields trailing body) := by
  exact List.foldr_append

theorem consume_signature_leading (family : Nat) (signature : Signature) (params : Nat) (ps : List Term)
    (bound : params ≤ signature.fields.length) (size : ps.length = params) :
    consume (signatureTerm family signature) ps = some
      ((closeDataFields ((signature.fields.drop params).map (fun field => (field.erased,field.domain)))
        (.node (.ind family signature.result.length) signature.result)).subst (fieldSubstitution ps)) := by
  rw [signatureTerm_close_fields]
  have fields : signature.fields.map (fun field => (field.erased,field.domain)) =
      (signature.fields.take params).map (fun field => (field.erased,field.domain)) ++
        (signature.fields.drop params).map (fun field => (field.erased,field.domain)) := by
    rw [← List.map_append,List.take_append_drop]
  rw [fields,close_fields_append,consume_close_fields _ _ _
    (by simp only [List.length_map,List.length_take,Nat.min_eq_left bound,size])]

theorem transform_fields_parameters (fields : List Field) (ps : List Term) (position depth : Nat)
    (scopes : ∀ (j : Nat) field,fields[j]? = some field → field.domain.Scoped (position+j+ps.length)) :
    transformDataFields (fieldSubstitution ps) position (fields.map (fun field => (field.erased,field.domain))) =
      instantiatedFields depth ps false position fields := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih =>
    simp only [List.map_cons,transformDataFields,instantiatedFields,Bool.false_and,Bool.false_eq_true,↓reduceIte]
    rw [fieldSubstitution_lift_scoped (depth := depth)
      (by simpa only [Nat.add_zero] using scopes 0 field rfl)]
    congr 1
    apply ih
    intro j selected found
    simpa only [Nat.add_assoc,Nat.add_comm 1 j] using scopes (j+1) selected found

private theorem close_same_domains (fields : List (Bool × Term)) (first second : Term) :
    SameDomains fields.length (closeDataFields fields first) (closeDataFields fields second) := by
  induction fields with
  | nil => exact .zero _ _
  | cons field fields ih => exact .step field.1 field.1 field.2 ih

/-- The remaining constructor telescope and an authentic generated Case
have the same dependent field domains after the actual leading arguments. -/
theorem signature_leading_domains (scope : UnifiedProgram.SignatureScoped signature)
    (bound : params ≤ signature.fields.length) (size : ps.length = params)
    (computed : consume (signatureTerm family signature) ps = some telescope)
    (generated : dataCaseType family constructor params depth signature ps motive false proof = some type) :
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
  · simp only [Bool.false_eq_true,↓reduceIte,List.length_nil,dataHypothesisTelescope,List.zipIdx_nil,List.foldr_nil] at generated
    cases generated
    simpa only [instantiatedFields_length,List.length_drop] using close_same_domains
      (instantiatedFields depth ps false 0 (signature.fields.drop params)) _ _

private theorem consume_cons_view (computed : consume telescope (value :: values) = some output) :
    ∃ erased domain body,telescope = .pi erased domain body ∧
      consume (body.subst (single value)) values = some output := by
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
          | nil => exact ⟨erased,domain,body,rfl,computed⟩
          | cons _ _ => simp [consume] at computed

/-- Remove precisely the real leading parameter applications from the same
mutual argument derivation. -/
theorem arguments_drop_leading (wf : UnifiedProgram.EnvWellFormed env) (leading : List Term)
    (arguments : Arguments env [] ctx true data telescope (leading ++ values) result)
    (computed : consume telescope leading = some residual) :
    Arguments env [] ctx true data residual values result := by
  induction leading generalizing telescope with
  | nil =>
    simp only [consume,Option.some.injEq] at computed
    subst residual
    exact arguments
  | cons value leading ih =>
    obtain ⟨erased,domain,body,rfl,computed⟩ := consume_cons_view computed
    exact ih (arguments_pi_view wf arguments).2 computed

private theorem identity_rename_function : Term.rename (fun x : Nat => x) = id := by
  funext term
  change term.rename id = term
  exact Term.rename_id term

private theorem shifted_parameters_instantiation (ps values : List Term) :
    (ps.map (Term.rename (fun x => x+values.length))).map (Term.subst (fieldSubstitution values)) = ps := by
  rw [List.map_map]
  calc
    _ = ps.map id := by
      apply List.map_congr_left
      intro term member
      exact fieldSubstitution_shift values term
    _ = _ := List.map_id ps

theorem constructor_parameters_variables_instantiation (family constructor : Nat) (ps values : List Term) :
    (Term.node (.con family constructor (ps.length+values.length))
      (ps.map (Term.rename (fun x => x+values.length)) ++ fieldVariables values.length)).subst
      (fieldSubstitution values) =
      .node (.con family constructor (ps ++ values).length) (ps ++ values) := by
  have actual := constructor_subst family constructor
    (ps.map (Term.rename (fun x => x+values.length)) ++ fieldVariables values.length) (fieldSubstitution values)
  simpa only [List.length_append,List.length_map,fieldVariables_length,List.map_append,
    shifted_parameters_instantiation,fieldVariables_substitution] using actual

theorem dataCaseResult_instantiation (family constructor params : Nat)
    (ps values indices : List Term) (motive : Term) :
    (dataCaseResult family constructor params values.length 0 ps motive indices).subst (fieldSubstitution values) =
      .app (applications motive ((indices.drop params).map (Term.subst (fieldSubstitution values))))
        (.node (.con family constructor (ps ++ values).length) (ps ++ values)) := by
  simp only [dataCaseResult,Nat.add_zero,identity_rename_function,List.map_id,
    List.length_append,List.length_map,List.length_range]
  change (Term.app (applications (motive.rename (fun x => x+values.length)) (indices.drop params))
    (.node (.con family constructor (ps.length+values.length))
      (ps.map (Term.rename (fun x => x+values.length)) ++ fieldVariables values.length))).subst
      (fieldSubstitution values) = _
  simp only [Term.subst,substArgs,Op.binders,liftSub,applications_subst,fieldSubstitution_shift]
  have constructorStep := constructor_parameters_variables_instantiation family constructor ps values
  simp only [Term.subst] at constructorStep
  rw [constructorStep]
  simp only [List.length_append]

theorem case_result_indices_instantiation (scope : UnifiedProgram.SignatureScoped signature)
    (ps values : List Term) (size : ps.length+values.length = signature.fields.length) :
    (signature.result.map (Term.subst (parameterAt depth values.length ps))).map
      (Term.subst (fieldSubstitution values)) =
        signature.result.map (Term.subst (fieldSubstitution (ps ++ values))) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro index member
  have bounded : index.Scoped (values.length+ps.length) := by
    have source := scope.result index member
    have levels : values.length+ps.length = signature.fields.length := by omega
    rw [levels]
    exact source
  simp only [Function.comp_apply]
  rw [← fieldSubstitution_lift_scoped (depth := depth) bounded,Term.subst_comp,← fieldSubstitution_append]

/-- Full leading-parameter branch result: applying all remaining fields
produces the original constructor and its actual instantiated result indices. -/
theorem consume_data_case_parameters (scope : UnifiedProgram.SignatureScoped signature)
    (bound : params ≤ signature.fields.length) (parameterSize : ps.length = params)
    (fieldSize : values.length = signature.fields.length-params)
    (generated : dataCaseType family constructor params depth signature ps motive false proof = some type) :
    consume type values = some (.app
      (applications motive ((signature.result.map (Term.subst (fieldSubstitution (ps ++ values)))).drop params))
      (.node (.con family constructor (ps ++ values).length) (ps ++ values))) := by
  unfold dataCaseType at generated
  split at generated
  · contradiction
  · simp only [Bool.false_eq_true,↓reduceIte,List.length_nil,dataHypothesisTelescope,List.zipIdx_nil,List.foldr_nil] at generated
    cases generated
    rw [consume_close_fields _ _ _ (by simpa only [instantiatedFields_length,List.length_drop] using fieldSize.symm)]
    rw [List.length_drop,← fieldSize,dataCaseResult_instantiation,List.map_drop,
      case_result_indices_instantiation scope ps values (by omega)]

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
