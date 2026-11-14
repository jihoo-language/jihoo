import Jihoo.NativeFamilyIotaViewInstantiation

/-! Original-type View iota preservation from authentic checked declarations,
actual constructor Arguments and the actual computed borrowed field plan. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

def ViewInputs (env : Environment) (ctx : Context) : Term → Term → Prop
  | .node (.view recursion family count) args,type =>
    ∃ entry motive cases scrutinee indices dependent types,
      count = cases.length ∧ args = motive :: (cases ++ [scrutinee]) ∧
      env.families[family]? = some entry ∧ entry.declaration.data = true ∧ entry.boxed = true ∧
      entry.declaration.arity = entry.declaration.params ∧ indices.length = entry.declaration.params ∧
      HasType env ctx true scrutinee (.ref (.node (.ind family entry.declaration.arity) indices)) ∧
      HasType env ctx true motive (viewMotiveType dependent (.node (.ind family entry.declaration.arity) indices)) ∧
      viewCaseTypes env family entry.declaration.params ctx.length entry.signatures indices motive recursion dependent = some types ∧
      BranchTypes env ctx true types cases ∧ Conversion.Conv env (viewResult dependent motive scrutinee) type
  | _,_ => True

private theorem ViewInputs.convert (inputs : ViewInputs env ctx term A) (converted : Conversion.Conv env A B) :
    ViewInputs env ctx term B := by
  fun_cases ViewInputs env ctx term A <;> simp only [ViewInputs] at inputs ⊢
  obtain ⟨entry,motive,cases,scrutinee,indices,dependent,types,count,layout,found,data,boxed,arity,size,scrut,motiveTyped,generated,branches,result⟩ := inputs
  exact ⟨entry,motive,cases,scrutinee,indices,dependent,types,count,layout,found,data,boxed,arity,size,scrut,motiveTyped,generated,branches,.trans result converted⟩

theorem view_inputs (typed : HasType env ctx true term type) : ViewInputs env ctx term type := by
  have stronger : ∀ mode,HasType env ctx mode term type → mode = true → ViewInputs env ctx term type := by
    intro mode h
    apply HasType.rec (t := h)
      (motive_1 := fun _ _ _ _ _ => True)
      (motive_2 := fun ctx mode term type _ => mode = true → ViewInputs env ctx term type)
      (motive_3 := fun _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | skip
    case dataElim => split <;> trivial
    case view found data boxed arity size scrutinee motive allowed generated branches _ _ _ trueMode =>
      subst trueMode
      exact ⟨_,_,_,_,_,_,_,rfl,rfl,found,data,boxed,arity,size,scrutinee,motive,generated,branches,.refl _⟩
    case convert typed converted ih trueMode => exact (ih trueMode).convert converted
  exact stronger true typed rfl

private theorem plan_generated
    (generated : viewCaseType env family constructor params depth signature ps motive false dependent = some type)
    (planned : viewPlan env family (signature.fields.drop params) = some plans) :
    type = closeDataFields (viewInstFields depth ps [] plans)
      (viewCaseResult family constructor plans.length 0 ps motive (plans.map ViewFieldPlan.borrowed) dependent) := by
  unfold viewCaseType at generated
  split at generated
  · contradiction
  · simp only [planned,Bind.bind,Option.bind,pure,Bool.false_eq_true,ite_false,List.length_nil,
      viewHypothesisTelescope,List.zipIdx_nil,List.foldr_nil,Option.some.injEq] at generated
    exact generated.symm

/-- Generic one-level borrowed View preservation. Leading parameters,
dependent field domains, owned external fields, dependent motives and
surrounding result conversions are all retained. -/
theorem view_preserves_one_level {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans)
    (typed : HasType env ctx true
      (viewTerm false family motive cases (.borrow (.node (.con family constructor values.length) values))) type) :
    HasType env ctx true (viewBody false family entry.declaration.params motive branch cases values plans) type := by
  obtain ⟨entry',motive',cases',scrutinee',indices,dependent,types,count,layout,found',data,boxed,arity,indexSize,scrut,motiveTyped,generated,branches,result⟩ := view_inputs typed
  have same := Option.some.inj (found.symm.trans found')
  subst entry'
  have outer := List.cons.inj layout
  have motives := outer.1
  subst motive'
  have parts := List.append_inj' outer.2 (by simp)
  obtain ⟨rfl,scrutineeEq⟩ := parts
  have scrutineeEq := (List.cons.inj scrutineeEq).1
  subst scrutinee'
  obtain ⟨ownerType,ownerTyped,ownerConverted⟩ := scrut.principalView
  have owner := HasType.convert ownerTyped (ref_injective history.wellFormed ownerConverted)
  obtain ⟨constructorEntry,constructorSignature,constructorArity,constructorIndices,constructorFound,signatureFound,arguments,converted⟩ := owner.principalView
  have sameEntry := Option.some.inj (found.symm.trans constructorFound)
  subst constructorEntry
  have sameSignature := Option.some.inj (sigFound.symm.trans signatureFound)
  subst constructorSignature
  have metadata := signature_metadata history found sigFound
  rw [closed_rename (metadata.1.signatureTerm_scoped family) _] at arguments
  have actualResult := constructor_result_conversion history.wellFormed arguments size
  have actualIndices := ind_injective history.wellFormed (actualResult.trans converted)
  have parameterRelated := metadata.2.2.result_alignment history.wellFormed.closed size actualIndices.2.2
  have indicesTake : indices.take entry.declaration.params = indices := by
    rw [← indexSize,List.take_length]
  rw [indicesTake] at parameterRelated
  obtain ⟨branchType,typeFound,built⟩ := viewCaseTypes_get generated sigFound
  obtain ⟨actualType,rebuilt,typeConverted⟩ := viewCaseType_parameters_congr history.wellFormed.closed parameterRelated built
  have branchTyped := HasType.convert (branch_get branches typeFound selected) typeConverted
  rw [plan_generated rebuilt planned] at branchTyped
  have valueBound : entry.declaration.params ≤ values.length := by have bound := metadata.2.2.1;omega
  have parameterSize : (values.take entry.declaration.params).length = entry.declaration.params := by
    simp only [List.length_take,Nat.min_eq_left valueBound]
  have sourceFields := viewPlan_source planned
  have fieldSize : (values.drop entry.declaration.params).length = plans.length := by
    have lengths := congrArg List.length sourceFields
    simp only [List.length_map,List.length_drop,size] at lengths ⊢
    exact lengths.symm
  have leading := consume_signature_leading family signature entry.declaration.params
    (values.take entry.declaration.params) metadata.2.2.1 parameterSize
  have residualArguments := arguments_drop_leading history.wellFormed (values.take entry.declaration.params)
    (values := values.drop entry.declaration.params)
    (by simpa only [List.take_append_drop] using arguments) leading
  have instantiated := closeDataFields_subst
    ((signature.fields.drop entry.declaration.params).map (fun field => (field.erased,field.domain))) 0
    (.node (.ind family signature.result.length) signature.result) (fieldSubstitution (values.take entry.declaration.params))
  simp only [liftSub,Nat.zero_add] at instantiated
  rw [instantiated] at residualArguments
  have scopes : ∀ (j : Nat) field,(signature.fields.drop entry.declaration.params)[j]? = some field →
      field.domain.Scoped (0+j+(values.take entry.declaration.params).length) := by
    intro j field fieldFound
    have scope := metadata.1.domains (entry.declaration.params+j) field (by simpa only [List.getElem?_drop] using fieldFound)
    simpa only [parameterSize,Nat.zero_add,Nat.add_comm j] using scope
  rw [transform_fields_parameters _ _ 0 ctx.length scopes,← sourceFields] at residualArguments
  obtain ⟨output,computed,applied⟩ := apply_view_arguments history.wellFormed found boxed plans
    (viewPlan_valid planned) (ReadsAs.empty (env := env))
    (by simpa only [Term.subst_id,List.length_nil] using residualArguments)
    (by simpa only [Term.subst_id] using branchTyped) fieldSize
  simp only [Term.subst_id] at computed
  have exactConsume := consume_close_fields
    (viewInstFields ctx.length (values.take entry.declaration.params) [] plans)
    (viewArguments plans (values.drop entry.declaration.params))
    (viewCaseResult family constructor plans.length 0 (values.take entry.declaration.params) motive
      (plans.map ViewFieldPlan.borrowed) dependent)
    (by rw [viewInstFields_length,viewArguments_length fieldSize,fieldSize])
  have sameOutput := Option.some.inj (computed.symm.trans exactConsume)
  subst output
  have exactResult := viewCaseResult_instantiation (family := family) (constructor := constructor)
    (ps := values.take entry.declaration.params) (motive := motive) (dependent := dependent)
    history.wellFormed.closed fieldSize
  rw [List.take_append_drop] at exactResult
  exact .convert (by simpa only [viewBody,viewHypotheses,Bool.false_eq_true,ite_false,applications,List.foldl_nil] using applied)
    (exactResult.trans result)

/-- Every accepted one-level executable View contraction preserves the exact
original result type, extracting all metadata from actual computation. -/
theorem contract_view_one_level_preserves {family count : Nat}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (accepted : contract env (.node (.view false family count) args) = some result)
    (typed : HasType env ctx true (.node (.view false family count) args) type) :
    HasType env ctx true result type := by
  cases contract_sound accepted with
  | view found boxed signature selected count fields bound planned =>
    exact view_preserves_one_level history found signature selected fields planned typed

end Jihoo.NativeKernel.Environment.FamilyIota
