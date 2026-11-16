import Jihoo.NativeScopedProgramHistory
import Jihoo.NativeLoanFamilyIotaElimCongruence

/-! Principal Elim inputs and independently typed actual recursive calls for
both proposition and indexed data elimination. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

private theorem related_symm (related : Conversion.ListRel (Conversion.Conv env) xs ys) :
    Conversion.ListRel (Conversion.Conv env) ys xs := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.symm ih

private theorem related_trans (left : Conversion.ListRel (Conversion.Conv env) xs ys)
    (right : Conversion.ListRel (Conversion.Conv env) ys zs) :
    Conversion.ListRel (Conversion.Conv env) xs zs := by
  induction left generalizing zs with
  | nil => cases right;exact .nil
  | cons head tail ih => cases right with
    | cons head' tail' => exact .cons (head.trans head') (ih tail')

private theorem related_append (first : Conversion.ListRel (Conversion.Conv env) xs ys)
    (second : Conversion.ListRel (Conversion.Conv env) rest rest') :
    Conversion.ListRel (Conversion.Conv env) (xs ++ rest) (ys ++ rest') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem related_refl (xs : List Term) : Conversion.ListRel (Conversion.Conv env) xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl _) ih

/-- Recursive calls reuse the actual source motive/branches at its observed
parameter instance; checked recursive parameters align the real field to it. -/
theorem recursive_data_hypothesis {family constructor j : Nat} {entry : CheckedFamily} {signature : Signature}
    (history : ScopedProgram.History definitions declarations env)
    (found : env.families[family]? = some entry) (sigFound : entry.signatures[constructor]? = some signature)
    (dataIs : entry.declaration.data = true) (parameterSize : ps.length = entry.declaration.params)
    (motiveTyped : HasType env [] ctx true motive
      (dataMotiveType family entry.declaration.params entry.declaration.arity ps proof))
    (generated : dataCaseTypes family entry.declaration.params ctx.length entry.signatures ps motive entry.boxed proof = some types)
    (branches : BranchTypes env [] ctx true types cases)
    (arguments : Arguments env [] ctx true entry.declaration.data (signatureTerm family signature) values result)
    (size : values.length = signature.fields.length)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps (values.take entry.declaration.params))
    (fieldFound : signature.fields[j]? = some field) (valueFound : values[j]? = some value)
    (recursive : field.recursive = some indices) :
    HasType env [] ctx true (elimTerm family motive cases value)
      (.app (applications motive
        ((indices.map (Term.subst (fieldSubstitution (values.take j)))).drop entry.declaration.params)) value) := by
  have shape := signature_recursive_metadata history found sigFound j field fieldFound
  have indexSize := (shape.2 indices recursive).2.1
  let actualIndices := indices.map (Term.subst (fieldSubstitution (values.take j)))
  have actual := recursive_field_argument history found sigFound arguments size fieldFound valueFound recursive
  have aligned := recursive_parameter_alignment history found sigFound dataIs size fieldFound recursive
  have parameterRelation := related_trans aligned (related_symm parameters)
  have indicesRelated : Conversion.ListRel (Conversion.Conv env) actualIndices
      (ps ++ actualIndices.drop entry.declaration.params) := by
    simpa only [actualIndices,List.take_append_drop] using related_append parameterRelation (related_refl (actualIndices.drop entry.declaration.params))
  have observed := HasType.convert actual (.node _ indicesRelated)
  have parameterBound : entry.declaration.params ≤ entry.declaration.arity := by
    have metadata := signature_metadata history found sigFound
    have bound := metadata.2.2.result_bound
    omega
  have count : (ps ++ actualIndices.drop entry.declaration.params).length = entry.declaration.arity := by
    simp only [List.length_append,parameterSize,List.length_drop,actualIndices,List.length_map,indexSize]
    omega
  have parameterTake : (ps ++ actualIndices.drop entry.declaration.params).take entry.declaration.params = ps := by
    rw [← parameterSize,List.take_left]
  have parameterDrop : (ps ++ actualIndices.drop entry.declaration.params).drop entry.declaration.params =
      actualIndices.drop entry.declaration.params := by rw [← parameterSize,List.drop_left]
  have formed := HasType.dataElim (analysis := false) (proof := proof) (ghost := true) found dataIs
    (by intro impossible;cases impossible) count
    (by simpa only [parameterTake] using motiveTyped)
    (by simpa only [Bool.true_or] using observed)
    (by simpa only [parameterTake,Bool.not_false,Bool.and_true] using generated)
    (by simpa only [Bool.true_or] using branches) (Or.inl rfl)
  simpa only [elimTerm,Bool.false_eq_true,ite_false,parameterDrop] using formed

/-- Complete actual principal Elim inputs; original result conversions remain
explicit in each proposition/data branch. -/
def ElimInputs (env : Environment) (ctx : Context) : Term → Term → Prop
  | .node (.elim family count) args,type =>
    ∃ entry motive cases scrutinee indices,
      count = cases.length ∧ args = motive :: (cases ++ [scrutinee]) ∧
      env.families[family]? = some entry ∧
      ((entry.declaration.data = false ∧
        HasType env [] ctx true motive (propMotiveType entry.declaration.arity) ∧
        Cases env [] ctx motive entry.signatures cases ∧
        HasType env [] ctx true scrutinee (.node (.ind family entry.declaration.arity) indices) ∧
        Conversion.Conv env (applications motive indices) type) ∨
       (entry.declaration.data = true ∧ ∃ proof types,
        indices.length = entry.declaration.arity ∧
        HasType env [] ctx true motive (dataMotiveType family entry.declaration.params entry.declaration.arity
          (indices.take entry.declaration.params) proof) ∧
        HasType env [] ctx true scrutinee (.node (.ind family entry.declaration.arity) indices) ∧
        dataCaseTypes family entry.declaration.params ctx.length entry.signatures
          (indices.take entry.declaration.params) motive entry.boxed proof = some types ∧
        BranchTypes env [] ctx true types cases ∧
        Conversion.Conv env (.app (applications motive (indices.drop entry.declaration.params)) scrutinee) type))
  | _,_ => True

private theorem ElimInputs.convert (inputs : ElimInputs env ctx term A) (converted : Conversion.Conv env A B) :
    ElimInputs env ctx term B := by
  fun_cases ElimInputs env ctx term A <;> simp only [ElimInputs] at inputs ⊢
  obtain ⟨entry,motive,cases,scrutinee,indices,count,layout,found,kind⟩ := inputs
  refine ⟨entry,motive,cases,scrutinee,indices,count,layout,found,?_⟩
  rcases kind with ⟨data,motiveTyped,branches,scrut,result⟩ | ⟨data,proof,types,size,motiveTyped,scrut,generated,branches,result⟩
  · exact Or.inl ⟨data,motiveTyped,branches,scrut,result.trans converted⟩
  · exact Or.inr ⟨data,proof,types,size,motiveTyped,scrut,generated,branches,result.trans converted⟩

theorem elim_inputs (typed : HasType env [] ctx true term type) : ElimInputs env ctx term type := by
  have stronger : ∀ stack mode,HasType env stack ctx mode term type → stack = [] → mode = true → ElimInputs env ctx term type := by
    intro stack mode h
    apply HasType.rec (t := h)
      (motive_1 := fun _ _ _ _ _ _ => True)
      (motive_2 := fun stack ctx mode term type _ => stack = [] → mode = true → ElimInputs env ctx term type)
      (motive_3 := fun _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
    all_goals intros
    all_goals first | trivial | skip
    case propElim found data motive branches scrutinee _ _ _ emptyStack trueMode =>
      cases emptyStack
      subst trueMode
      exact ⟨_,_,_,_,_,rfl,rfl,found,Or.inl ⟨data,motive,branches,scrutinee,.refl _⟩⟩
    case dataElim found data boxed size motive scrut generated branches allowed ihm ihs ihb emptyStack trueMode =>
      rename_i family entry analysis stack ctx motiveTerm proof ghost scrutinee indices types caseTerms
      cases emptyStack
      subst trueMode
      cases analysis with
      | true => trivial
      | false => exact ⟨entry,motiveTerm,caseTerms,scrutinee,indices,rfl,rfl,found,Or.inr
          ⟨data,proof,types,size,motive,by simpa only [Bool.true_or] using scrut,
            by simpa only [Bool.not_false,Bool.and_true] using generated,
            by simpa only [Bool.true_or] using branches,.refl _⟩⟩
    case convert typed converted ih emptyStack trueMode => exact (ih emptyStack trueMode).convert converted
  exact stronger [] true typed rfl rfl

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
