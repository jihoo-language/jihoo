import Jihoo.NativeFamilyIotaElimPositions

/-! Generic indexed data Elim iota preservation from actual source typing,
constructor Arguments and independently recovered recursive field metadata. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem authentic_recursive_enabled {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (dataIs : entry.declaration.data = true) :
    (if entry.boxed then instantiatedRecursive depth ps (signature.fields.drop params) else []) =
      instantiatedRecursive depth ps (signature.fields.drop params) := by
  cases boxed : entry.boxed with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    symm
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro pair member
    obtain ⟨position,indices,field,same,fieldFound,recursive⟩ := instantiatedRecursive_selected member
    have stored : signature.fields[params+position]? = some field := by simpa only [List.getElem?_drop] using fieldFound
    have impossible := recursive_data_is_boxed history found sigFound dataIs stored recursive
    rw [boxed] at impossible
    contradiction

private theorem generated_shape
    (generated : dataCaseType family constructor params depth signature ps motive recursion proof = some type) :
    type = closeDataFields (instantiatedFields depth ps recursion 0 (signature.fields.drop params))
      (dataHypothesisTelescope params (signature.fields.length-params) 0
        (if recursion then instantiatedRecursive depth ps (signature.fields.drop params) else []) proof motive
        (dataCaseResult family constructor params (signature.fields.length-params)
          (if recursion then instantiatedRecursive depth ps (signature.fields.drop params) else []).length ps motive
          (signature.result.map (Term.subst (parameterAt depth (signature.fields.length-params) ps))))) := by
  unfold dataCaseType at generated
  split at generated
  · contradiction
  · cases generated
    simp only [List.length_drop]

private theorem related_drop (related : Conversion.ListRel (Conversion.Conv env) xs ys) (n : Nat) :
    Conversion.ListRel (Conversion.Conv env) (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact related
  | succ n ih => cases related with
    | nil => exact .nil
    | cons _ tail => exact ih tail

/-- Every genuine data Elim constructor contraction preserves its exact
original type, with arbitrary indices, parameters, recursive fields and motives. -/
theorem data_elim_preserves {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (dataIs : entry.declaration.data = true)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (typed : HasType env ctx true
      (elimTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env ctx true (elimBody entry signature family motive branch cases values) type := by
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
  rcases kind with ⟨propIs,other⟩ | ⟨data,proof,types,indexSize,motiveTyped,scrut,generated,branches,result⟩
  · rw [dataIs] at propIs;contradiction
  obtain ⟨constructorEntry,constructorSignature,constructorArity,constructorIndices,constructorFound,signatureFound,arguments,converted⟩ := scrut.principalView
  have sameEntry := Option.some.inj (found.symm.trans constructorFound)
  subst constructorEntry
  have sameSignature := Option.some.inj (sigFound.symm.trans signatureFound)
  subst constructorSignature
  have metadata := signature_metadata history found sigFound
  rw [closed_rename (metadata.1.signatureTerm_scoped family) _] at arguments
  have actualResult := constructor_result_conversion history.wellFormed arguments size
  have actualIndices := ind_injective history.wellFormed (actualResult.trans converted)
  have parameterRelated := metadata.2.2.result_alignment history.wellFormed.closed size actualIndices.2.2
  have valueBound : entry.declaration.params ≤ values.length := by have bound := metadata.2.2.1;omega
  have parameterSize : (values.take entry.declaration.params).length = entry.declaration.params := by
    simp only [List.length_take,Nat.min_eq_left valueBound]
  have parameterBound : entry.declaration.params ≤ indices.length := by
    have bound := metadata.2.2.result_bound
    omega
  have observedParameterSize : (indices.take entry.declaration.params).length = entry.declaration.params := by
    simp only [List.length_take,Nat.min_eq_left parameterBound]
  have fieldSize : (values.drop entry.declaration.params).length = signature.fields.length-entry.declaration.params := by
    simp only [List.length_drop,size]
  obtain ⟨branchType,typeFound,built⟩ := dataCaseTypes_get generated sigFound
  obtain ⟨actualType,rebuilt,typeConverted⟩ := dataCaseType_parameters_congr_all history.wellFormed.closed parameterRelated built
  have enabled := authentic_recursive_enabled (depth := ctx.length) (ps := values.take entry.declaration.params)
    (params := entry.declaration.params) history found sigFound dataIs
  have branchTyped := HasType.convert (branch_get branches typeFound selected) typeConverted
  rw [generated_shape rebuilt,enabled] at branchTyped
  let recursive := instantiatedRecursive ctx.length (values.take entry.declaration.params) (signature.fields.drop entry.declaration.params)
  have hypotheses : ∀ pair ∈ recursive,∃ argument,(values.drop entry.declaration.params)[pair.1]? = some argument ∧
      HasType env ctx true (elimTerm family motive cases argument)
        (.app (applications motive ((pair.2.map (Term.subst
          (fieldSubstitution ((values.drop entry.declaration.params).take pair.1)))).drop entry.declaration.params)) argument) := by
    intro pair member
    obtain ⟨position,fieldIndices,field,same,fieldFound,recursiveField⟩ := instantiatedRecursive_selected member
    subst pair
    have stored : signature.fields[entry.declaration.params+position]? = some field := by
      simpa only [List.getElem?_drop] using fieldFound
    have positionBound : position < (values.drop entry.declaration.params).length := by
      have bound := (List.getElem?_eq_some_iff.mp fieldFound).1
      simpa only [List.length_drop,size] using bound
    have valueFound := List.getElem?_eq_getElem positionBound
    have scope : ∀ term ∈ fieldIndices,term.Scoped (position+(values.take entry.declaration.params).length) := by
      intro term member
      have fieldScope := metadata.1.recursive (entry.declaration.params+position) field fieldIndices stored recursiveField term member
      simpa only [parameterSize,Nat.add_comm position] using fieldScope
    have prefixSize : ((values.drop entry.declaration.params).take position).length = position := by
      simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt positionBound)]
    have exactIndices := recursive_indices_instantiation (depth := ctx.length) scope prefixSize
    rw [← List.take_add] at exactIndices
    have call := recursive_data_hypothesis history found sigFound dataIs observedParameterSize motiveTyped generated branches
      arguments size parameterRelated stored (by simpa only [List.getElem?_drop] using valueFound) recursiveField
    refine ⟨_,valueFound,?_⟩
    simpa only [exactIndices] using call
  have leading := consume_signature_leading family signature entry.declaration.params
    (values.take entry.declaration.params) metadata.2.2.1 parameterSize
  have residualArguments := arguments_drop_leading history.wellFormed (values.take entry.declaration.params)
    (values := values.drop entry.declaration.params)
    (by simpa only [List.take_append_drop] using arguments) leading
  have domains := signature_leading_domains_all metadata.1 metadata.2.2.1 parameterSize leading rebuilt
  rw [← fieldSize] at domains
  obtain ⟨output,computed,applied⟩ := apply_same_domains history.wellFormed domains residualArguments
    (.convert (branch_get branches typeFound selected) typeConverted)
  have exactConsume := consume_close_fields
    (instantiatedFields ctx.length (values.take entry.declaration.params) entry.boxed 0 (signature.fields.drop entry.declaration.params))
    (values.drop entry.declaration.params)
    (dataHypothesisTelescope entry.declaration.params (signature.fields.length-entry.declaration.params) 0 recursive proof motive
      (dataCaseResult family constructor entry.declaration.params (signature.fields.length-entry.declaration.params) recursive.length
        (values.take entry.declaration.params) motive
        (signature.result.map (Term.subst (parameterAt ctx.length (signature.fields.length-entry.declaration.params)
          (values.take entry.declaration.params))))))
    (by simp only [instantiatedFields_length,List.length_drop,size])
  rw [generated_shape rebuilt,enabled] at computed
  have sameOutput := Option.some.inj (computed.symm.trans exactConsume)
  subst output
  have hypothesisLength := dataHypothesisArguments_length (make := elimTerm family motive cases)
    (fun pair member => by obtain ⟨argument,found,_⟩ := hypotheses pair member;exact ⟨argument,found⟩)
  have recursivelyApplied := apply_data_hypotheses recursive [] (values.drop entry.declaration.params)
    (elimTerm family motive cases) hypotheses
    (by simpa only [List.length_nil,List.append_nil,fieldSize] using applied)
  have exactResult := dataCaseResult_recursive_instantiation (family := family) (constructor := constructor)
    (params := entry.declaration.params) (depth := ctx.length) (motive := motive) metadata.1
    (values.take entry.declaration.params) (values.drop entry.declaration.params)
    (dataHypothesisArguments recursive (values.drop entry.declaration.params) (elimTerm family motive cases))
    (by rw [parameterSize,fieldSize];omega)
  rw [hypothesisLength,fieldSize,List.take_append_drop] at exactResult
  simp only [List.nil_append] at recursivelyApplied
  rw [exactResult] at recursivelyApplied
  have final := HasType.convert (by simpa only [List.nil_append] using recursivelyApplied)
    ((EnvironmentDelta.Basis.Conv.node .app (.cons
      (applications_congr (.refl motive) (related_drop actualIndices.2.2 _)) (.cons (.refl _) .nil))).trans result)
  have parameterNonrecursive : ∀ j < entry.declaration.params,∀ field,signature.fields[j]? = some field → field.recursive = none := by
    intro j inside field fieldFound
    obtain ⟨stored,_,storedFound,_,recursive,_,_,_⟩ := metadata.2.2.2 j inside
    have same := Option.some.inj (storedFound.symm.trans fieldFound)
    subst stored
    exact recursive
  have actualHypotheses := elimHypotheses_drop_parameters (family := family) (motive := motive) (cases := cases) size parameterNonrecursive
  rw [elimHypotheses_positions (by simp only [List.length_drop,size]),← actualHypotheses] at final
  simpa only [elimBody,dataIs,ite_true] using final

end Jihoo.NativeKernel.Environment.FamilyIota
