import Jihoo.NativeCorePropSignatureConversion
import Jihoo.NativeLoanFamilyIotaParameterCongruence

/-! Data case types respect conversion of the constructor's stored
fields and indexed recursive hypotheses. Both signatures open under
the same actual parameter substitution. -/
namespace Jihoo.NativeKernel.Environment

open NativeKernel.Conversion (ListRel)
open FamilyEnvironment (RelList)
open LoanTyping.FamilyIota (dataCaseResult_parameters_congr)

private theorem related_drop (first second : List Field) (count : Nat)
    (related : RelList (FieldConversion env) first second) :
    RelList (FieldConversion env) (first.drop count) (second.drop count) := by
  induction count generalizing first second with
  | zero => exact related
  | succ count ih =>
    cases related with
    | nil => exact .nil
    | cons _ tail => exact ih _ _ tail

private theorem related_substitution (closed : EnvironmentDelta.Basis.Closed env)
    (related : ListRel (RawLend.Conv env) xs ys) (assign : Nat → Term) :
    ListRel (RawLend.Conv env) (xs.map (Term.subst assign)) (ys.map (Term.subst assign)) := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons (first.substitution _ closed) ih

private theorem marker_equal (related : RecursiveIndexConversion env first second) :
    first.isSome = second.isSome := by
  cases related <;> rfl

private theorem retained_flag (same : FieldConversion env first second) (recursion : Bool) :
    (if recursion && first.recursive.isSome then true else first.erased) =
      (if recursion && second.recursive.isSome then true else second.erased) := by
  rw [marker_equal same.recursive,same.erasure]

private theorem close_instantiated (closed : EnvironmentDelta.Basis.Closed env)
    (fields : RelList (FieldConversion env) first second) (position : Nat) (body : RawLend.Conv env A B) :
    RawLend.Conv env (closeDataFields (instantiatedFields depth ps recursion position first) A)
      (closeDataFields (instantiatedFields depth ps recursion position second) B) := by
  induction fields generalizing position with
  | nil => exact body
  | cons head rest ih =>
    simp only [instantiatedFields,closeDataFields,List.foldr_cons,retained_flag head recursion]
    exact .node (.pi _) (.cons (head.domain.substitution _ closed) (.cons (ih (position+1)) .nil))

private theorem instantiate_recursive (closed : EnvironmentDelta.Basis.Closed env)
    (related : RelList (RecursiveFieldConversion env) first second) :
    RelList (RecursiveFieldConversion env)
      (first.map (fun (position,indices) => (position,indices.map (Term.subst (parameterAt depth position ps)))))
      (second.map (fun (position,indices) => (position,indices.map (Term.subst (parameterAt depth position ps))))) := by
  induction related with
  | nil => exact .nil
  | @cons first second _ _ head _ ih =>
    obtain ⟨firstPosition,firstIndices⟩ := first
    obtain ⟨secondPosition,secondIndices⟩ := second
    obtain ⟨same,indices⟩ := head
    dsimp only at same indices
    subst secondPosition
    exact .cons ⟨rfl,related_substitution closed indices _⟩ ih

private theorem related_term_drop (count : Nat) (related : ListRel (RawLend.Conv env) first second) :
    ListRel (RawLend.Conv env) (first.drop count) (second.drop count) := by
  induction count generalizing first second with
  | zero => exact related
  | succ count ih =>
    cases related with
    | nil => exact .nil
    | cons _ rest => exact ih rest

private theorem converted_data_hypotheses (closed : EnvironmentDelta.Basis.Closed env)
    (related : RelList (RecursiveFieldConversion env) first second)
    (body : RawLend.Conv env A B) (offset : Nat) :
    RawLend.Conv env (dataHypothesisTelescope params fields offset first proof M A)
      (dataHypothesisTelescope params fields offset second proof M B) := by
  induction related generalizing offset with
  | nil => exact body
  | cons head _ ih =>
    obtain ⟨position,indices⟩ := head
    simp only [dataHypothesisTelescope,List.zipIdx_cons,List.foldr_cons,dataHypothesisType,position]
    exact .node (.pi proof) (.cons
      (.node .app (.cons (application_spines (.refl _)
        (renamed_indices closed _ (related_term_drop params indices))) (.cons (.refl _) .nil)))
      (.cons (ih (offset+1)) .nil))

private theorem related_refl_terms (terms : List Term) : ListRel (RawLend.Conv env) terms terms := by
  induction terms with
  | nil => exact .nil
  | cons term rest ih => exact .cons (.refl _) ih

/-- An independently normalized constructor yields the same case type
up to conversion, including the hypotheses of boxed recursion. -/
theorem SignatureConversion.data_case (closed : EnvironmentDelta.Basis.Closed env)
    (signatures : SignatureConversion env first second)
    (selected : dataCaseType family constructor params depth first ps motive recursion proof = some source) :
    ∃ target, dataCaseType family constructor params depth second ps motive recursion proof = some target ∧
      RawLend.Conv env source target := by
  have width := signatures.fields.length
  unfold dataCaseType at selected ⊢
  split at selected
  · cases selected
  · rename_i valid
    have targetValid : (ps.length != params || params > second.fields.length) ≠ true := by
      simpa only [←width] using valid
    simp only [ite_eq_right targetValid]
    cases selected
    let firstFields := first.fields.drop params
    let secondFields := second.fields.drop params
    have fields := related_drop first.fields second.fields params signatures.fields
    have number := fields.length
    have recursive : RelList (RecursiveFieldConversion env)
        (if recursion then instantiatedRecursive depth ps firstFields else [])
        (if recursion then instantiatedRecursive depth ps secondFields else []) := by
      cases recursion
      · exact .nil
      · exact instantiate_recursive closed (aligned_recursive_fields fields 0)
    have hypotheses := recursive.length
    have indices : RawLend.Conv env
        (dataCaseResult family constructor params firstFields.length
          (if recursion then instantiatedRecursive depth ps firstFields else []).length ps motive
          (first.result.map (Term.subst (parameterAt depth firstFields.length ps))))
        (dataCaseResult family constructor params secondFields.length
          (if recursion then instantiatedRecursive depth ps secondFields else []).length ps motive
          (second.result.map (Term.subst (parameterAt depth secondFields.length ps)))) := by
      rw [number,hypotheses]
      exact dataCaseResult_parameters_congr closed (related_refl_terms ps)
        (related_substitution closed signatures.result _)
    refine ⟨_,rfl,close_instantiated closed fields 0 ?_⟩
    have close := converted_data_hypotheses (params := params) (fields := firstFields.length)
      (proof := proof) (M := motive) closed recursive indices 0
    rw [←number] at close ⊢
    exact close

end Jihoo.NativeKernel.Environment
