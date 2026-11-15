import Jihoo.NativeLoanFamilyIotaConstructor
import Jihoo.NativeLoanFamilyIotaParameterAlignment

/-! Original-type Case iota preservation for arbitrary dependent fields of
nonparameter data families. Actual lookup, generated branches, constructor
arguments and checked history discharge every telescope premise. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

private def CaseInputs (env : Environment) (ctx : Context) : Term → Term → Prop
  | .node (.caseOf family count) args,type =>
      ∃ entry motive cases scrutinee indices proof types,
        count = cases.length ∧ args = motive :: (cases ++ [scrutinee]) ∧
        env.families[family]? = some entry ∧
        HasType env [] ctx true scrutinee (.node (.ind family entry.declaration.arity) indices) ∧
        dataCaseTypes family entry.declaration.params ctx.length entry.signatures
          (indices.take entry.declaration.params) motive false proof = some types ∧
        BranchTypes env [] ctx true types cases ∧
        Conversion.Conv env (.app (applications motive (indices.drop entry.declaration.params)) scrutinee) type
  | _,_ => True

private theorem CaseInputs.convert (inputs : CaseInputs env ctx term A) (converted : Conversion.Conv env A B) :
    CaseInputs env ctx term B := by
  fun_cases CaseInputs env ctx term A <;> simp only [CaseInputs] at inputs ⊢
  obtain ⟨entry,motive,cases,scrutinee,indices,proof,types,count,layout,found,scrut,generated,branches,result⟩ := inputs
  exact ⟨entry,motive,cases,scrutinee,indices,proof,types,count,layout,found,scrut,generated,branches,.trans result converted⟩

private theorem case_inputs (typed : HasType env [] ctx true term type) : CaseInputs env ctx term type := by
  have stronger : ∀ stack mode,HasType env stack ctx mode term type → stack = [] → mode = true → CaseInputs env ctx term type := by
    intro stack mode h
    apply HasType.rec (t := h)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun stack ctx mode term type _ => stack = [] → mode = true → CaseInputs env ctx term type)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | skip
    case dataElim found data boxed size motive scrut generated branches allowed ihm ihs ihb emptyStack trueMode =>
      rename_i family entry analysis stack ctx motiveTerm proof ghost scrutinee indices types caseTerms
      cases emptyStack
      subst trueMode
      cases analysis with
      | false => trivial
      | true =>
        exact ⟨entry,motiveTerm,caseTerms,scrutinee,indices,proof,types,rfl,rfl,found,
          by simpa only [Bool.true_or] using scrut,
          by simpa only [Bool.not_true,Bool.and_false] using generated,
          by simpa only [Bool.true_or] using branches,.refl _⟩
    case convert typed converted ih emptyStack trueMode => exact (ih emptyStack trueMode).convert converted
  exact stronger [] true typed rfl rfl

/-- Exact original-type preservation, with arbitrary dependent fields,
indices, branch expressions and surrounding result conversions. Parameters
are zero here; their general transport is a separate subsequent theorem. -/
theorem case_preserves_no_parameters {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (parameters : entry.declaration.params = 0) (selected : cases[constructor]? = some branch)
    (size : values.length = signature.fields.length)
    (typed : HasType env [] ctx true
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env [] ctx true (applications branch values) type := by
  obtain ⟨entry',motive',cases',scrutinee',indices,proof,types,count,layout,found',scrut,generated,branches,result⟩ := case_inputs typed
  have same := Option.some.inj (found.symm.trans found')
  subst entry'
  have outer := List.cons.inj layout
  have motives := outer.1
  subst motive'
  have parts := List.append_inj' outer.2 (by simp)
  obtain ⟨rfl,scrutineeEq⟩ := parts
  have scrutineeEq := (List.cons.inj scrutineeEq).1
  subst scrutinee'
  rw [parameters,List.take_zero] at generated
  rw [parameters,List.drop_zero] at result
  obtain ⟨constructorEntry,constructorSignature,arity,constructorIndices,constructorFound,signatureFound,arguments,converted⟩ := scrut.principalView
  have sameEntry := Option.some.inj (found.symm.trans constructorFound)
  subst constructorEntry
  have sameSignature := Option.some.inj (sigFound.symm.trans signatureFound)
  subst constructorSignature
  have signatureScope := (signature_metadata history found sigFound).1
  rw [closed_rename (signatureScope.signatureTerm_scoped family) _] at arguments
  have actualResult := constructor_result_conversion history.wellFormed arguments size
  have actualIndices := ind_injective history.wellFormed (actualResult.trans converted)
  have branchTyped := case_branch_apply_no_parameters history found sigFound parameters
    (by simpa only [parameters] using generated) branches selected arguments size
  exact .convert branchTyped (.trans
    (.node .app (.cons (applications_congr (.refl motive) actualIndices.2.2) (.cons (.refl _) .nil))) result)

private theorem case_related_drop (related : Conversion.ListRel (Conversion.Conv env) xs ys) (n : Nat) :
    Conversion.ListRel (Conversion.Conv env) (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact related
  | succ n ih => cases related with
    | nil => exact .nil
    | cons head tail => exact ih tail

/-- Full leading-parameter Case iota preservation. All metadata, parameter
alignment and branch-domain transport are derived from the authentic history
and the actual constructor derivation. No caller supplies a telescope oracle. -/
theorem case_preserves {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (typed : HasType env [] ctx true
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env [] ctx true (applications branch (values.drop entry.declaration.params)) type := by
  obtain ⟨entry',motive',cases',scrutinee',indices,proof,types,count,layout,found',scrut,generated,branches,result⟩ := case_inputs typed
  have same := Option.some.inj (found.symm.trans found')
  subst entry'
  have outer := List.cons.inj layout
  have motives := outer.1
  subst motive'
  have parts := List.append_inj' outer.2 (by simp)
  obtain ⟨rfl,scrutineeEq⟩ := parts
  have scrutineeEq := (List.cons.inj scrutineeEq).1
  subst scrutinee'
  obtain ⟨constructorEntry,constructorSignature,arity,constructorIndices,constructorFound,signatureFound,arguments,converted⟩ := scrut.principalView
  have sameEntry := Option.some.inj (found.symm.trans constructorFound)
  subst constructorEntry
  have sameSignature := Option.some.inj (sigFound.symm.trans signatureFound)
  subst constructorSignature
  have metadata := signature_metadata history found sigFound
  rw [closed_rename (metadata.1.signatureTerm_scoped family) _] at arguments
  have actualResult := constructor_result_conversion history.wellFormed arguments size
  have actualIndices := ind_injective history.wellFormed (actualResult.trans converted)
  have parameterRelated := metadata.2.2.result_alignment history.wellFormed.closed size actualIndices.2.2
  obtain ⟨branchType,typeFound,built⟩ := dataCaseTypes_get generated sigFound
  obtain ⟨actualType,rebuilt,typeConverted⟩ := dataCaseType_parameters_congr history.wellFormed.closed parameterRelated built
  have valueBound : entry.declaration.params ≤ values.length := by have bound := metadata.2.2.1;omega
  have parameterSize : (values.take entry.declaration.params).length = entry.declaration.params := by
    simp only [List.length_take,Nat.min_eq_left valueBound]
  have fieldSize : (values.drop entry.declaration.params).length = signature.fields.length-entry.declaration.params := by
    simp only [List.length_drop,size]
  have leading := consume_signature_leading family signature entry.declaration.params
    (values.take entry.declaration.params) metadata.2.2.1 parameterSize
  have residualArguments := arguments_drop_leading history.wellFormed (values.take entry.declaration.params)
    (values := values.drop entry.declaration.params)
    (by simpa only [List.take_append_drop] using arguments) leading
  have domains := signature_leading_domains metadata.1 metadata.2.2.1 parameterSize leading rebuilt
  rw [← fieldSize] at domains
  obtain ⟨output,computed,branchTyped⟩ := apply_same_domains history.wellFormed domains residualArguments
    (.convert (branch_get branches typeFound selected) typeConverted)
  have exactResult := consume_data_case_parameters metadata.1 metadata.2.2.1 parameterSize fieldSize rebuilt
  have sameOutput := Option.some.inj (computed.symm.trans exactResult)
  subst output
  rw [List.take_append_drop] at branchTyped
  exact .convert branchTyped (.trans
    (.node .app (.cons (applications_congr (.refl motive) (case_related_drop actualIndices.2.2 _))
      (.cons (.refl _) .nil))) result)

/-- The executable Case contraction preserves the exact independently typed
input result. All signature and parameter premises are extracted internally
from the computation and the checked history. -/
theorem contract_case_preserves {family count : Nat}
    (history : UnifiedProgram.UnifiedProgramChecked definitions declarations env)
    (accepted : contract env (.node (.caseOf family count) args) = some result)
    (typed : HasType env [] ctx true (.node (.caseOf family count) args) type) :
    HasType env [] ctx true result type := by
  cases contract_sound accepted with
  | caseOf found data signature selected count fields =>
    exact case_preserves history found signature selected fields typed

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
