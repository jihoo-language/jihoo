import Jihoo.NativeFamilyIotaTelescopes
import Jihoo.NativeFamilyIotaBinding
import Jihoo.NativeFamilyIotaTyping

/-! Exact field instantiation for authentic dependent constructor telescopes.
The substitution is computed by the same successive binder removals as App. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

/-- Remove fields in declaration order while preserving each remaining binder. -/
def fieldSubstitution : List Term → Nat → Term
  | [] => Term.var
  | value :: values => fun x =>
      (liftSub values.length (single value) x).subst (fieldSubstitution values)

private theorem lift_single_above (binders x : Nat) (value : Term) :
    liftSub binders (single value) (x + binders + 1) = .var (x + binders) := by
  induction binders with
  | zero => simp only [liftSub,Nat.add_zero,single]
  | succ binders ih =>
    simpa only [Nat.add_assoc,Nat.succ_eq_add_one,liftSub,liftSubOne,Term.rename] using
      congrArg (Term.rename Nat.succ) ih

private theorem lift_single_at (binders : Nat) (value : Term) :
    liftSub binders (single value) binders = value.rename (fun x => x + binders) := by
  induction binders with
  | zero =>
    change value = value.rename id
    exact (Term.rename_id value).symm
  | succ binders ih =>
    simp only [liftSub,liftSubOne,ih,Term.rename_comp]
    rfl

theorem fieldSubstitution_shift (values : List Term) (term : Term) :
    (term.rename (fun x => x + values.length)).subst (fieldSubstitution values) = term := by
  induction values with
  | nil =>
    change (term.rename id).subst Term.var = term
    rw [Term.subst_id,Term.rename_id]
  | cons value values ih =>
    rw [show fieldSubstitution (value :: values) =
      (fun x => (liftSub values.length (single value) x).subst (fieldSubstitution values)) from rfl,
      ← Term.subst_comp,Term.subst_rename]
    have shifted : (fun x => liftSub values.length (single value) (x + (value :: values).length)) =
        fun x => Term.var (x + values.length) := by
      funext x
      simpa only [List.length_cons,Nat.add_assoc] using lift_single_above values.length x value
    rw [shifted,variable_subst_eq_rename]
    exact ih

theorem fieldSubstitution_selected {j : Nat} (selected : values[j]? = some value) :
    fieldSubstitution values (values.length - 1 - j) = value := by
  induction values generalizing j with
  | nil => simp at selected
  | cons head values ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      subst value
      simpa only [fieldSubstitution,List.length_cons,Nat.add_sub_cancel,Nat.sub_zero,lift_single_at] using
        fieldSubstitution_shift values head
    | succ j =>
      have inside := (List.getElem?_eq_some_iff.mp selected).1
      have bound : (head :: values).length - 1 - (j+1) < values.length := by simp only [List.length_cons] at *;omega
      have stable := scoped_subst_lift (Term.Scoped.var bound) (single head)
      have liftStable : liftSub values.length (single head) ((head :: values).length - 1 - (j+1)) =
          .var ((head :: values).length - 1 - (j+1)) := by simpa only [Term.subst] using stable
      simp only [fieldSubstitution,liftStable,Term.subst]
      have index : (head :: values).length - 1 - (j+1) = values.length - 1 - j := by simp only [List.length_cons];omega
      rw [index]
      exact ih selected

private theorem transformDataFields_length (fields : List (Bool × Term)) (σ : Nat → Term) (position : Nat) :
    (transformDataFields σ position fields).length = fields.length := by
  induction fields generalizing position with
  | nil => rfl
  | cons field fields ih => simpa only [transformDataFields,List.length_cons] using congrArg Nat.succ (ih (position+1))

/-- Consuming precisely the constructor's fields leaves the actual computed
simultaneous substitution of its terminal expression. -/
theorem consume_close_fields (fields : List (Bool × Term)) (values : List Term) (body : Term)
    (size : fields.length = values.length) :
    consume (closeDataFields fields body) values = some (body.subst (fieldSubstitution values)) := by
  induction values generalizing fields body with
  | nil =>
    have empty : fields = [] := List.length_eq_zero_iff.mp size
    subst fields
    simp only [closeDataFields,List.foldr_nil,consume,fieldSubstitution,Term.subst_id]
  | cons value values ih =>
    cases fields with
    | nil => simp at size
    | cons field fields =>
      have length : fields.length = values.length := Nat.succ.inj size
      simp only [closeDataFields,List.foldr_cons,consume]
      rw [show (fields.foldr (fun field result => Term.pi field.1 field.2 result) body).subst (single value) =
        closeDataFields (transformDataFields (single value) 0 fields)
          (body.subst (liftSub fields.length (single value))) by
          simpa only [Nat.zero_add,closeDataFields,liftSub] using closeDataFields_subst fields 0 body (single value)]
      rw [ih _ _ ((transformDataFields_length _ _ _).trans length)]
      simp only [Term.subst_comp,length,fieldSubstitution]

def fieldVariables (count : Nat) : List Term :=
  (List.range count).map (fun j => Term.var (count - 1 - j))

theorem fieldVariables_length (count : Nat) : (fieldVariables count).length = count := by
  simp only [fieldVariables,List.length_map,List.length_range]

theorem fieldVariables_substitution (values : List Term) :
    (fieldVariables values.length).map (Term.subst (fieldSubstitution values)) = values := by
  apply List.ext_getElem
  · simp only [List.length_map,fieldVariables_length]
  · intro j inside bound
    simp only [fieldVariables,List.getElem_map,List.getElem_range,Term.subst]
    exact fieldSubstitution_selected (List.getElem?_eq_getElem bound)

private theorem identity_rename (term : Term) : term.rename (fun x => x) = term := by
  change term.rename id = term
  exact Term.rename_id term

private theorem identity_rename_function : Term.rename (fun x : Nat => x) = id := by
  funext term
  exact identity_rename term

theorem constructor_variables_instantiation (family constructor : Nat) (values : List Term) :
    (Term.node (.con family constructor values.length) (fieldVariables values.length)).subst
      (fieldSubstitution values) = .node (.con family constructor values.length) values := by
  have actual := constructor_subst family constructor (fieldVariables values.length) (fieldSubstitution values)
  simpa only [fieldVariables_length,List.length_map,fieldVariables_substitution] using actual

theorem dataCaseResult_instantiation_no_parameters (family constructor : Nat)
    (values indices : List Term) (motive : Term) :
    (dataCaseResult family constructor 0 values.length 0 [] motive indices).subst (fieldSubstitution values) =
      .app (applications motive (indices.map (Term.subst (fieldSubstitution values))))
        (.node (.con family constructor values.length) values) := by
  simp only [dataCaseResult,List.map_nil,List.nil_append,List.drop_zero,Nat.add_zero,
    identity_rename,identity_rename_function,List.map_id,List.length_map,List.length_range]
  change (Term.app (applications (motive.rename (fun x => x + values.length)) indices)
    (.node (.con family constructor values.length) (fieldVariables values.length))).subst
      (fieldSubstitution values) = _
  simp only [Term.subst,substArgs,Op.binders,liftSub,applications_subst,fieldSubstitution_shift]
  have constructorStep := constructor_variables_instantiation family constructor values
  simp only [Term.subst] at constructorStep
  rw [constructorStep]

private theorem no_parameters_stable {term : Term} {locals depth : Nat} (scope : term.Scoped locals) :
    term.subst (parameterAt depth locals []) = term := by
  calc
    term.subst (parameterAt depth locals []) = term.subst Term.var := by
      apply scoped_subst_congr scope
      intro x inside
      simp only [parameterAt,inside,↓reduceIte]
    _ = term := Term.subst_id term

theorem dataCaseType_no_parameters (scope : UnifiedProgram.SignatureScoped signature) :
    dataCaseType family constructor 0 depth signature [] motive false proof =
      some (closeDataFields (signature.fields.map (fun field => (field.erased,field.domain)))
        (dataCaseResult family constructor 0 signature.fields.length 0 [] motive signature.result)) := by
  have resultIndices : signature.result.map (Term.subst (parameterAt depth signature.fields.length [])) = signature.result := by
    calc
      _ = signature.result.map id := by
        apply List.map_congr_left
        intro term member
        exact no_parameters_stable (scope.result term member)
      _ = _ := List.map_id signature.result
  simp only [dataCaseType,List.length_nil,Nat.not_lt_zero,Bool.false_eq_true,↓reduceIte,List.drop_zero,
    List.length_nil,resultIndices,dataHypothesisTelescope,List.zipIdx_nil,List.foldr_nil]
  rw [instantiatedFields_no_parameters depth 0 signature.fields
    (by intro j field found;simpa only [Nat.zero_add] using scope.domains j field found)]
  rfl

theorem consume_data_case_no_parameters (scope : UnifiedProgram.SignatureScoped signature)
    (generated : dataCaseType family constructor 0 depth signature [] motive false proof = some type)
    (size : values.length = signature.fields.length) :
    consume type values = some (.app
      (applications motive (signature.result.map (Term.subst (fieldSubstitution values))))
      (.node (.con family constructor values.length) values)) := by
  rw [dataCaseType_no_parameters scope] at generated
  cases generated
  rw [consume_close_fields _ _ _ (by simpa only [List.length_map] using size.symm)]
  rw [← size,dataCaseResult_instantiation_no_parameters]

end Jihoo.NativeKernel.Environment.FamilyIota
