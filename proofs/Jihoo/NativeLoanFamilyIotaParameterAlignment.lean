import Jihoo.NativeLoanFamilyIotaParameterInstantiation

/-! Align an independently typed scrutinee's parameter indices with the
actual constructor fields, using authentic stored parameter equations. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

private theorem related_length (related : Conversion.ListRel (Conversion.Conv env) xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem related_lookup {index : Nat} (related : Conversion.ListRel (Conversion.Conv env) xs ys)
    (left : xs[index]? = some a) (right : ys[index]? = some b) : Conversion.Conv env a b := by
  induction related generalizing index with
  | nil => simp at left
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at left right
      subst a
      subst b
      exact head
    | succ index => exact ih left right

private theorem related_of_lookup (size : xs.length = ys.length)
    (lookup : ∀ (index : Nat) a b,xs[index]? = some a → ys[index]? = some b → Conversion.Conv env a b) :
    Conversion.ListRel (Conversion.Conv env) xs ys := by
  induction xs generalizing ys with
  | nil =>
    have empty : ys = [] := List.length_eq_zero_iff.mp size.symm
    subst ys
    exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => simp at size
    | cons y ys =>
      exact .cons (lookup 0 x y rfl rfl)
        (ih (Nat.succ.inj size) (fun index a b left right => lookup (index+1) a b left right))

theorem Parameters.result_bound (parameters : Parameters env params signature) : params ≤ signature.result.length := by
  by_cases zero : params = 0
  · simp only [zero,Nat.zero_le]
  · obtain ⟨field,index,_,_,_,_,found,_⟩ := parameters.2 (params-1) (by omega)
    have inside := (List.getElem?_eq_some_iff.mp found).1
    omega

theorem Parameters.field_instance (parameters : Parameters env params signature)
    (closed : Conversion.Closed env) (size : values.length = signature.fields.length)
    {j : Nat} (inside : j < params) (selected : values[j]? = some value) :
    ∃ index,signature.result[j]? = some index ∧ Conversion.Conv env (index.subst (fieldSubstitution values)) value := by
  obtain ⟨field,index,_,_,_,_,found,converted⟩ := parameters.2 j inside
  refine ⟨index,found,?_⟩
  have instantiated := converted.substitution (fieldSubstitution values) closed
  simpa only [Term.subst,← size,fieldSubstitution_selected selected] using instantiated

/-- The observed parameter prefix is genuinely converted to the actual
constructor parameter arguments, even when the scrutinee type was converted. -/
theorem Parameters.result_alignment (parameters : Parameters env params signature)
    (closed : Conversion.Closed env) (size : values.length = signature.fields.length)
    (converted : Conversion.ListRel (Conversion.Conv env)
      (signature.result.map (Term.subst (fieldSubstitution values))) indices) :
    Conversion.ListRel (Conversion.Conv env) (indices.take params) (values.take params) := by
  have lengths := related_length converted
  simp only [List.length_map] at lengths
  have resultBound := parameters.result_bound
  have valueBound := parameters.1
  have indexBound : params ≤ indices.length := by omega
  have actualBound : params ≤ values.length := by omega
  apply related_of_lookup
  · simp only [List.length_take,Nat.min_eq_left indexBound,Nat.min_eq_left actualBound]
  · intro j observed actual observedFound actualFound
    have inside := (List.getElem?_eq_some_iff.mp observedFound).1
    simp only [List.length_take,Nat.min_eq_left indexBound] at inside
    simp only [List.getElem?_take,inside,↓reduceIte] at observedFound actualFound
    obtain ⟨index,indexFound,parameterConverted⟩ := parameters.field_instance closed size inside actualFound
    have indexConverted := related_lookup (a := index.subst (fieldSubstitution values)) (b := observed) converted
      (by simp only [List.getElem?_map,indexFound,Option.map_some]) observedFound
    exact indexConverted.symm.trans parameterConverted

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
