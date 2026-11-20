import Jihoo.NativeScopedProgramHistory
import Jihoo.NativeFamilyIotaDeterminism
import Jihoo.NativeLoanFamilyIotaConstructor
import Jihoo.NativeLoanFamilyIotaParameterAlignment
import Jihoo.NativeLoanPureConversion

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
        env.families[family]? = some entry ∧ entry.declaration.data = true ∧
        entry.boxed = true ∧ indices.length = entry.declaration.arity ∧
        HasType env [] ctx true motive (dataMotiveType family entry.declaration.params
          entry.declaration.arity (indices.take entry.declaration.params) proof) ∧
        HasType env [] ctx true scrutinee (.node (.ind family entry.declaration.arity) indices) ∧
        dataCaseTypes family entry.declaration.params ctx.length entry.signatures
          (indices.take entry.declaration.params) motive false proof = some types ∧
        BranchTypes env [] ctx true types cases ∧
        Conversion.Conv env (.app (applications motive (indices.drop entry.declaration.params)) scrutinee) type
  | _,_ => True

private theorem CaseInputs.convert (inputs : CaseInputs env ctx term A) (converted : Conversion.Conv env A B) :
    CaseInputs env ctx term B := by
  fun_cases CaseInputs env ctx term A <;> simp only [CaseInputs] at inputs ⊢
  obtain ⟨entry, motive, cases, scrutinee, indices, proof, types, count, layout,
    found, data, boxed, size, motiveTyped, scrut, generated, branches, result⟩ := inputs
  exact ⟨entry, motive, cases, scrutinee, indices, proof, types, count, layout,
    found, data, boxed, size, motiveTyped, scrut, generated, branches, .trans result converted⟩

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
        exact ⟨entry,motiveTerm,caseTerms,scrutinee,indices,proof,types,rfl,rfl,found,data,boxed rfl,size,motive,
          by simpa only [Bool.true_or] using scrut,
          by simpa only [Bool.not_true,Bool.and_false] using generated,
          by simpa only [Bool.true_or] using branches,.refl _⟩
    case convert typed converted ih emptyStack trueMode => exact (ih emptyStack trueMode).convert converted
  exact stronger [] true typed rfl rfl

private def StrictPrefix (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .strict effect _ => ∃ type, HasType env loans ctx mode effect type
  | _ => True

private theorem strict_prefix (typed : HasType env loans ctx mode term type) : StrictPrefix env loans ctx mode term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack context ghost term _ _ => StrictPrefix env stack context ghost term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case strict prefixTyped _ _ _ => exact ⟨_, prefixTyped⟩
  case dataElim found data boxed size motive scrut generated branches allowed ihm ihs ihb =>
    rename_i family entry analysis stack context motiveTerm proof ghost scrutinee indices types caseTerms
    cases analysis <;> trivial

/-- Moving a strict prefix outside Case keeps the original generated arms
and uses the value as the motive's scrutinee. The two result types are
related by the pure conversion that erases only the strict effect. -/
theorem strict_case_inputs
    (typed : HasType env loans ctx mode (caseTerm family motive cases (.strict effect value)) type) :
    ∃ prefixType innerType,
      HasType env [] ctx true effect prefixType ∧
      HasType env [] ctx true (caseTerm family motive cases value) innerType ∧
      RawValue.Conv env innerType type := by
  obtain ⟨entry, motive', cases', scrutinee, indices, proof, types, _, layout, found, data,
    boxed, size, motiveTyped, scrutineeTyped, generated, branches, result⟩ := case_inputs (typed.ghost [])
  obtain ⟨rfl, tails⟩ := List.cons.inj layout
  obtain ⟨rfl, strictEq⟩ := List.append_inj' tails (by simp)
  have same := (List.cons.inj strictEq).1
  subst scrutinee
  obtain ⟨prefixType, prefixTyped⟩ := strict_prefix scrutineeTyped
  obtain ⟨valueType, valueTyped, converted⟩ := scrutineeTyped.principalView
  have inner := HasType.dataElim (analysis := true) (ghost := true) found data (fun _ => boxed) size
    motiveTyped (by simpa only [Bool.true_or] using valueTyped.convert converted)
    (by simpa only [Bool.not_true, Bool.and_false] using generated)
    (by simpa only [Bool.true_or] using branches) (Or.inl rfl)
  exact ⟨prefixType, _, prefixTyped, inner,
    (RawValue.Conv.node .app (.cons (.refl _) (.cons (.symm (.strict effect value)) .nil))).trans (.old result)⟩

/-- When the motive's result is stable in its final argument, the same
checked arms consume any replacement at the original indexed scrutinee type. -/
theorem case_scrutinee_context
    (typed : HasType env [] ctx true (caseTerm family motive cases scrutinee) type)
    (stable : ∀ {entry} {indices : List Term}, env.families[family]? = some entry →
      indices.length = entry.declaration.arity - entry.declaration.params →
      ∀ a b, Conversion.Conv env (.app (applications motive indices) a) (.app (applications motive indices) b)) :
    ∃ scrutineeType, HasType env [] ctx true scrutinee scrutineeType ∧
      ∀ {replacement}, HasType env [] ctx true replacement scrutineeType →
        HasType env [] ctx true (caseTerm family motive cases replacement) type := by
  obtain ⟨entry, motive', cases', scrutinee', indices, proof, types, _, layout, found, data,
    boxed, size, motiveTyped, scrutineeTyped, generated, branches, result⟩ := case_inputs typed
  obtain ⟨rfl, tails⟩ := List.cons.inj layout
  obtain ⟨rfl, single⟩ := List.append_inj' tails (by simp)
  obtain rfl := (List.cons.inj single).1
  refine ⟨_, scrutineeTyped, fun replacementTyped => ?_⟩
  have replaced := HasType.dataElim (analysis := true) (ghost := true) found data (fun _ => boxed) size
    motiveTyped (by simpa only [Bool.true_or] using replacementTyped)
    (by simpa only [Bool.not_true, Bool.and_false] using generated)
    (by simpa only [Bool.true_or] using branches) (Or.inl rfl)
  have indexCount : (indices.drop entry.declaration.params).length = entry.declaration.arity - entry.declaration.params := by
    rw [List.length_drop, size]
  exact replaced.convert ((stable found indexCount _ _).trans result)

private theorem mapped_length {α β : Type} {inputs : List α} {outputs : List β} {f : α → Option β}
    (built : inputs.mapM f = some outputs) :
    outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => cases built; rfl
  | cons first rest ih =>
      simp only [List.mapM_cons] at built
      obtain ⟨_, _, mappedTail⟩ := Option.bind_eq_some_iff.mp built
      obtain ⟨_, tail, equals⟩ := Option.bind_eq_some_iff.mp mappedTail
      cases equals
      exact congrArg Nat.succ (ih tail)

private theorem branch_count (typed : BranchTypes env [] ctx true types cases) : cases.length = types.length := by
  induction types generalizing cases with
  | nil => cases typed; rfl
  | cons first rest ih =>
      cases typed with
      | cons _ tail => exact congrArg Nat.succ (ih tail)

/-- Generation and branch checking preserve the signature vector's length. -/
theorem checked_generated_branch_count {signatures : List Signature} {generate : Signature × Nat → Option Term}
    (generated : signatures.zipIdx.mapM generate = some types)
    (checked : BranchTypes env [] ctx true types cases) : cases.length = signatures.length := by
  have count := mapped_length generated
  rw [List.length_zipIdx] at count
  exact (branch_count checked).trans count

/-- A constructor accepted at the selected family and a complete case vector
determine the selected case and the exact field count. -/
theorem checked_constructor_selection {cases : List Term} (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry)
    (typed : HasType env [] ctx true (.node (.con family constructor values.length) values) type)
    (count : cases.length = entry.signatures.length) :
    ∃ signature branch, entry.signatures[constructor]? = some signature ∧
      values.length = signature.fields.length ∧ cases[constructor]? = some branch := by
  obtain ⟨entry', signature, found', sig, fields⟩ := checked_constructor_fields history typed
  have same := Option.some.inj (found.symm.trans found')
  subst entry'
  have inside : constructor < cases.length := count.symm ▸ (List.getElem?_eq_some_iff.mp sig).1
  exact ⟨signature, cases[constructor], sig, fields, List.getElem?_eq_getElem inside⟩

/-- A typed Case on a constructor supplies the data flag, exact signature
and both graph vector counts. Its branch lookup follows from those counts. -/
theorem checked_case_alignment (history : ScopedProgram.History definitions declarations env)
    (typed : HasType env [] ctx true
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    ∃ entry signature branch, env.families[family]? = some entry ∧ entry.declaration.data = true ∧
      entry.signatures[constructor]? = some signature ∧ cases.length = entry.signatures.length ∧
      values.length = signature.fields.length ∧ cases[constructor]? = some branch := by
  obtain ⟨entry, _, _, _, _, _, _, _, layout, found, data, _, _, _, scrutinee, generated, branches, _⟩ := case_inputs typed
  have tail := (List.cons.inj layout).2
  obtain ⟨rfl, last⟩ := List.append_inj' tail (by simp)
  obtain rfl := (List.cons.inj last).1
  have count := checked_generated_branch_count generated branches
  obtain ⟨signature, branch, sig, fields, selected⟩ := checked_constructor_selection history found scrutinee count
  exact ⟨entry, signature, branch, found, data, sig, count, fields, selected⟩

/-- Exact original-type preservation, with arbitrary dependent fields,
indices, branch expressions and surrounding result conversions. Parameters
are zero here; their general transport is a separate subsequent theorem. -/
theorem case_preserves_no_parameters {family constructor : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (parameters : entry.declaration.params = 0) (selected : cases[constructor]? = some branch)
    (size : values.length = signature.fields.length)
    (typed : HasType env [] ctx true
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env [] ctx true (applications branch values) type := by
  obtain ⟨entry',motive',cases',scrutinee',indices,proof,types,count,layout,found',_,_,_,_,scrut,generated,branches,result⟩ :=
    case_inputs typed
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
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (selected : cases[constructor]? = some branch) (size : values.length = signature.fields.length)
    (typed : HasType env [] ctx true
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    HasType env [] ctx true (applications branch (values.drop entry.declaration.params)) type := by
  obtain ⟨entry',motive',cases',scrutinee',indices,proof,types,count,layout,found',_,_,_,_,scrut,generated,branches,result⟩ :=
    case_inputs typed
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
    (history : ScopedProgram.History definitions declarations env)
    (accepted : contract env (.node (.caseOf family count) args) = some result)
    (typed : HasType env [] ctx true (.node (.caseOf family count) args) type) :
    HasType env [] ctx true result type := by
  cases contract_sound accepted with
  | caseOf found data signature selected count fields =>
    exact case_preserves history found signature selected fields typed

/-- Checked Case inputs with a known constructor always contract. The
executable result retains the independently requested type. -/
theorem contract_case_from_typing (history : ScopedProgram.History definitions declarations env)
    (typed : HasType env [] ctx true
      (caseTerm family motive cases (.node (.con family constructor values.length) values)) type) :
    ∃ result, contract env (caseTerm family motive cases (.node (.con family constructor values.length) values)) =
      some result ∧ HasType env [] ctx true result type := by
  obtain ⟨entry, signature, branch, found, data, sig, count, fields, selected⟩ := checked_case_alignment history typed
  have root : Root env (caseTerm family motive cases (.node (.con family constructor values.length) values))
      (applications branch (values.drop entry.declaration.params)) :=
    .caseOf found data sig selected count fields
  exact ⟨_, root.complete, case_preserves history found sig selected fields typed⟩

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
