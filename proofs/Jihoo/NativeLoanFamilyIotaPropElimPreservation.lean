import Jihoo.NativeLoanFamilyIotaDataElimPreservation

/-! Proposition induction computes through the real constructor fields and
erased recursive hypotheses while retaining the original indexed proposition. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

private theorem cases_get {constructor : Nat}
    (branches : Cases env [] ctx motive signatures cases)
    (signatureFound : signatures[constructor]? = some signature) (selected : cases[constructor]? = some branch) :
    HasType env [] ctx true branch (propCaseType signature motive) := by
  induction constructor generalizing signatures cases with
  | zero =>
    cases branches with
    | nil => simp at signatureFound
    | cons typed branches =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at signatureFound selected
      subst signature
      subst branch
      exact typed
  | succ constructor ih =>
    cases branches with
    | nil => simp at signatureFound
    | cons typed branches => exact ih branches signatureFound selected

private theorem recursiveFields_selected (member : pair ∈ recursiveFields fields) :
    ∃ field,fields[pair.1]? = some field ∧ field.recursive = some pair.2 := by
  obtain ⟨⟨field,j⟩,inFields,selected⟩ := List.mem_filterMap.mp member
  have found := List.mk_mem_zipIdx_iff_getElem?.mp inFields
  cases recursive : field.recursive with
  | none => simp only [recursive,Option.map_none] at selected;contradiction
  | some indices =>
    simp only [recursive,Option.map_some,Option.some.injEq] at selected
    subst pair
    exact ⟨field,found,recursive⟩

private theorem propHypothesis_instantiation (bound : pair.1 ≤ fields.length) (previous : List Term) :
    (hypothesisType fields.length motive pair previous.length).subst
      (fieldSubstitution (fields ++ previous)) =
      applications motive (pair.2.map (Term.subst (fieldSubstitution (fields.take pair.1)))) := by
  have shift := fieldSubstitution_shift (fields ++ previous) motive
  simp only [List.length_append] at shift
  unfold hypothesisType
  rw [applications_subst]
  simp only [Nat.add_assoc,shift,List.map_map]
  apply congrArg (applications motive)
  apply List.map_congr_left
  intro term member
  exact fieldSubstitution_prefix_shift bound previous term

private theorem apply_prop_hypotheses (recursive : List (Nat × List Term)) (previous fields : List Term) (make : Term → Term)
    (hypotheses : ∀ pair ∈ recursive,∃ argument,fields[pair.1]? = some argument ∧
      HasType env [] ctx true (make argument)
        (applications motive (pair.2.map (Term.subst (fieldSubstitution (fields.take pair.1))))))
    (typed : HasType env [] ctx true function
      ((hypothesisTelescope fields.length previous.length recursive motive body).subst
        (fieldSubstitution (fields ++ previous)))) :
    HasType env [] ctx true (applications function (dataHypothesisArguments recursive fields make))
      (body.subst (fieldSubstitution (fields ++ (previous ++ dataHypothesisArguments recursive fields make)))) := by
  induction recursive generalizing previous function with
  | nil => simpa only [dataHypothesisArguments,List.filterMap_nil,List.append_nil,hypothesisTelescope,
      List.zipIdx_nil,List.foldr_nil,applications,List.foldl_nil] using typed
  | cons pair recursive ih =>
    obtain ⟨argument,found,hypothesis⟩ := hypotheses pair (by simp)
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have tailHypotheses : ∀ p ∈ recursive,∃ arg,fields[p.1]? = some arg ∧
        HasType env [] ctx true (make arg)
          (applications motive (p.2.map (Term.subst (fieldSubstitution (fields.take p.1))))) :=
      fun p hp => hypotheses p (by simp [hp])
    simp only [hypothesisTelescope,List.zipIdx_cons,List.foldr_cons,Term.subst,substArgs,Op.binders,liftSub] at typed
    have applied := HasType.app typed
      (by simpa only [Bool.true_or,propHypothesis_instantiation (Nat.le_of_lt bound) previous] using hypothesis) (Or.inl rfl)
    rw [Term.subst_comp] at applied
    change HasType env [] ctx true _
      ((hypothesisTelescope fields.length (previous.length+1) recursive motive body).subst
        (fun x => (liftSubOne (fieldSubstitution (fields ++ previous)) x).subst (single (make argument)))) at applied
    rw [lift_single_extend,← fieldSubstitution_snoc,List.append_assoc] at applied
    have next := ih (previous ++ [make argument]) tailHypotheses
      (by simpa only [List.length_append,List.length_singleton] using applied)
    simpa only [dataHypothesisArguments,List.filterMap_cons,found,Option.map_some,
      List.append_assoc,List.singleton_append,applications,List.foldl_cons] using next

private theorem close_same_domains (domains : List (Bool × Term)) (first second : Term) :
    SameDomains domains.length (closeDataFields domains first) (closeDataFields domains second) := by
  induction domains with
  | nil => exact .zero _ _
  | cons domain domains ih => exact .step domain.1 domain.1 domain.2 ih

private theorem same_domains (fields : List Field) : SameDomains fields.length
    (signatureTerm family ⟨fields,indices⟩) (propCaseType ⟨fields,indices⟩ motive) := by
  rw [signatureTerm_close_fields,propCaseType_eq]
  have same := close_same_domains (fields.map (fun f => (f.erased,f.domain)))
    (Term.node (.ind family indices.length) indices)
    (hypothesisTelescope fields.length 0 (recursiveFields fields) motive
      (applications (motive.rename (fun x => x+fields.length+(recursiveFields fields).length))
        (indices.map (Term.rename (fun x => x+(recursiveFields fields).length)))))
  simpa only [List.length_map,closeDataFields,List.foldr_map,Function.comp_def] using same

private theorem propResult_instantiation (values hypotheses indices : List Term) (motive : Term) :
    (applications (motive.rename (fun x => x+values.length+hypotheses.length))
      (indices.map (Term.rename (fun x => x+hypotheses.length)))).subst
      (fieldSubstitution (values ++ hypotheses)) =
      applications motive (indices.map (Term.subst (fieldSubstitution values))) := by
  have shifted : applications (motive.rename (fun x => x+values.length+hypotheses.length))
      (indices.map (Term.rename (fun x => x+hypotheses.length))) =
      (applications (motive.rename (fun x => x+values.length)) indices).rename (fun x => x+hypotheses.length) := by
    simp only [applications_rename,Term.rename_comp]
  rw [shifted,Term.subst_rename,fieldSubstitution_append_shift,applications_subst,fieldSubstitution_shift]

/-- Generic actual proposition induction preserves the exact original result,
including all recursive fields and arbitrary independently typed motives. -/
theorem prop_elim_preserves {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (propIs : entry.declaration.data = false)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (typed : HasType env [] ctx true
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env [] ctx true (elimBody entry signature family motive branch cases values) type := by
  obtain ⟨entry',motive',cases',scrutinee',indices,count,layout,found',kind⟩ := elim_inputs typed
  have same := Option.some.inj (found.symm.trans found')
  subst entry'
  have outer := List.cons.inj layout
  have motives := outer.1
  subst motive'
  have parts := List.append_inj' outer.2 (by simp)
  obtain ⟨rfl,scrutineeEq⟩ := parts
  have scrutineeEq := (List.cons.inj scrutineeEq).1
  subst scrutinee'
  rcases kind with ⟨prop,motiveTyped,branches,scrut,result⟩ | ⟨data,other⟩
  case inr => rw [propIs] at data;contradiction
  obtain ⟨constructorEntry,constructorSignature,constructorArity,constructorIndices,constructorFound,signatureFound,arguments,converted⟩ := scrut.principalView
  have sameEntry := Option.some.inj (found.symm.trans constructorFound)
  subst constructorEntry
  have sameSignature := Option.some.inj (sigFound.symm.trans signatureFound)
  subst constructorSignature
  have metadata := signature_metadata history found sigFound
  rw [closed_rename (metadata.1.signatureTerm_scoped family) _] at arguments
  have actualResult := constructor_result_conversion history.wellFormed arguments size
  have actualIndices := ind_injective history.wellFormed (actualResult.trans converted)
  have hypotheses : ∀ pair ∈ recursiveFields signature.fields,∃ argument,values[pair.1]? = some argument ∧
      HasType env [] ctx true (elimTerm family motive cases argument)
        (applications motive (pair.2.map (Term.subst (fieldSubstitution (values.take pair.1))))) := by
    intro pair member
    obtain ⟨field,fieldFound,recursive⟩ := recursiveFields_selected member
    have bound : pair.1 < values.length := by
      have inside := (List.getElem?_eq_some_iff.mp fieldFound).1
      omega
    have valueFound := List.getElem?_eq_getElem bound
    have actual := recursive_field_argument history found sigFound arguments size fieldFound valueFound recursive
    exact ⟨_,valueFound,HasType.propElim found propIs motiveTyped branches actual⟩
  have branchTyped := cases_get branches sigFound selected
  have domains := same_domains (family := family) (indices := signature.result) (motive := motive) signature.fields
  change SameDomains signature.fields.length (signatureTerm family signature) (propCaseType signature motive) at domains
  rw [← size] at domains
  obtain ⟨output,computed,applied⟩ := apply_same_domains history.wellFormed domains arguments branchTyped
  rw [propCaseType_eq] at computed
  have exactConsume := consume_close_fields (signature.fields.map (fun f => (f.erased,f.domain))) values
    (hypothesisTelescope signature.fields.length 0 (recursiveFields signature.fields) motive
      (applications (motive.rename (fun x => x+signature.fields.length+(recursiveFields signature.fields).length))
        (signature.result.map (Term.rename (fun x => x+(recursiveFields signature.fields).length)))))
    (by simp only [List.length_map,size])
  simp only [closeDataFields,List.foldr_map,Function.comp_def] at exactConsume
  have sameOutput := Option.some.inj (computed.symm.trans exactConsume)
  subst output
  have hypothesisLength := dataHypothesisArguments_length (make := elimTerm family motive cases)
    (fun pair member => by obtain ⟨argument,found,_⟩ := hypotheses pair member;exact ⟨argument,found⟩)
  have recursivelyApplied := apply_prop_hypotheses (recursiveFields signature.fields) [] values
    (elimTerm family motive cases) hypotheses (by simpa only [List.length_nil,List.append_nil,size] using applied)
  have exactResult := propResult_instantiation values
    (dataHypothesisArguments (recursiveFields signature.fields) values (elimTerm family motive cases)) signature.result motive
  rw [hypothesisLength,size] at exactResult
  simp only [List.nil_append] at recursivelyApplied
  rw [exactResult] at recursivelyApplied
  have final := HasType.convert recursivelyApplied ((applications_congr (.refl motive) actualIndices.2.2).trans result)
  have hypEq : dataHypothesisArguments (recursiveFields signature.fields) values (elimTerm family motive cases) =
      elimHypotheses family motive cases signature.fields values := by
    have positions := elimHypotheses_positions (depth := 0) (ps := []) (family := family) (motive := motive) (cases := cases) size
    simpa only [instantiatedRecursive,dataHypothesisArguments,List.filterMap_map,Function.comp_def] using positions
  rw [hypEq] at final
  simpa only [elimBody,propIs,Bool.false_eq_true,ite_false,List.drop_zero] using final

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
