import Jihoo.NativeScopedProgramHistory
import Jihoo.NativeLoanFamilyIotaViewPositions

/-! Generic recursive View original-type preservation. Every recursive call
is typed from actual constructor Arguments and authenticated recursive fields. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

private theorem plan_self_borrowed (planned : viewFieldPlan env family field = some plan) (self : plan.self = true) :
    plan.borrowed = true := by
  unfold viewFieldPlan at planned
  simp only [Option.map] at planned
  repeat' first | split at planned | contradiction
  all_goals cases planned
  all_goals simp_all

private theorem plan_generated
    (generated : viewCaseType env family constructor params depth signature ps motive true dependent = some type)
    (planned : viewPlan env family (signature.fields.drop params) = some plans) :
    type = closeDataFields (viewInstFields depth ps [] plans)
      (viewHypothesisTelescope plans.length 0 (viewPositions plans) motive dependent
        (viewCaseResult family constructor plans.length (viewPositions plans).length ps motive (plans.map ViewFieldPlan.borrowed) dependent)) := by
  unfold viewCaseType at generated
  split at generated
  · contradiction
  · simp only [planned,Bind.bind,Option.bind,pure,ite_true,Option.some.injEq] at generated
    exact generated.symm

/-- Generic recursive borrowed View preservation. Leading parameters,
dependent field domains, owned external fields, dependent motives and
surrounding result conversions are all retained. -/
theorem view_preserves_recursive {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (planned : viewPlan env family (signature.fields.drop entry.declaration.params) = some plans)
    (typed : HasType env [] ctx true
      (viewTerm true family motive cases (.borrow (.node (.con family constructor values.length) values))) type) :
    HasType env [] ctx true (viewBody true family entry.declaration.params motive branch cases values plans) type := by
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
  have hypotheses : ∀ position ∈ viewPositions plans,∃ argument,
      (viewArguments plans (values.drop entry.declaration.params))[position]? = some argument ∧
      HasType env [] ctx true (viewTerm true family motive cases argument) (viewResult dependent motive argument) := by
    intro position member
    obtain ⟨plan,planFound,self⟩ := viewPositions_selected member
    have positionBound : position < (values.drop entry.declaration.params).length := by
      have bound := viewPositions_bound member
      omega
    have valueFound := List.getElem?_eq_getElem positionBound
    have borrowed := plan_self_borrowed (viewPlan_valid planned plan (List.mem_of_getElem? planFound)) self
    have argumentFound := viewArguments_selected planFound valueFound
    simp only [borrowed,ite_true] at argumentFound
    exact ⟨_,argumentFound,recursive_view_hypothesis history found sigFound data boxed arity indexSize
      motiveTyped generated branches arguments size parameterRelated planned planFound valueFound self⟩
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
    (viewHypothesisTelescope plans.length 0 (viewPositions plans) motive dependent
      (viewCaseResult family constructor plans.length (viewPositions plans).length (values.take entry.declaration.params) motive
        (plans.map ViewFieldPlan.borrowed) dependent))
    (by rw [viewInstFields_length,viewArguments_length fieldSize,fieldSize])
  have sameOutput := Option.some.inj (computed.symm.trans exactConsume)
  subst output
  have hypothesisLength := hypothesisArguments_length
    (make := viewTerm true family motive cases) (fun position member => by
      obtain ⟨argument,found,_⟩ := hypotheses position member
      exact ⟨argument,found⟩)
  have recursivelyApplied := apply_view_hypotheses (viewPositions plans) []
    (viewArguments plans (values.drop entry.declaration.params)) (viewTerm true family motive cases) hypotheses
    (by simpa only [List.length_nil,List.append_nil,viewArguments_length fieldSize,fieldSize] using applied)
  have exactResult := viewCaseResult_recursive_instantiation (family := family) (constructor := constructor)
    (ps := values.take entry.declaration.params) (motive := motive) (dependent := dependent)
    history.wellFormed.closed fieldSize
    (hypothesisArguments (viewPositions plans) (viewArguments plans (values.drop entry.declaration.params))
      (viewTerm true family motive cases))
  rw [hypothesisLength,List.take_append_drop] at exactResult
  have final := HasType.convert (by simpa only [List.nil_append] using recursivelyApplied) (exactResult.trans result)
  simpa only [viewBody,viewHypotheses_positions planned fieldSize] using final

/-- All accepted recursive executable View contractions preserve the exact
independently typed original result. No output-typing oracle is a premise. -/
theorem contract_view_recursive_preserves {family count : Nat}
    (history : ScopedProgram.History definitions declarations env)
    (accepted : contract env (.node (.view true family count) args) = some result)
    (typed : HasType env [] ctx true (.node (.view true family count) args) type) :
    HasType env [] ctx true result type := by
  cases contract_sound accepted with
  | view found boxed signature selected count fields bound planned =>
    exact view_preserves_recursive history found signature selected fields planned typed

/-- Every accepted View contraction, recursive or one-level, preserves the
original dependent result type under the authentic checked history. -/
theorem contract_view_preserves {recursion : Bool} {family count : Nat}
    (history : ScopedProgram.History definitions declarations env)
    (accepted : contract env (.node (.view recursion family count) args) = some result)
    (typed : HasType env [] ctx true (.node (.view recursion family count) args) type) :
    HasType env [] ctx true result type := by
  cases recursion with
  | false => exact contract_view_one_level_preserves history accepted typed
  | true => exact contract_view_recursive_preserves history accepted typed

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
