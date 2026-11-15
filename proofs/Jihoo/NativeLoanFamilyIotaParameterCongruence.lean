import Jihoo.NativeLoanFamilyIotaMetadata
import Jihoo.NativeLoanDataMotiveCongruence
import Jihoo.NativeLoanConversionAlgebra

/-! Concrete parameter congruence for generated family telescopes. Metadata
masks stay fixed; every comparison follows actual full conversion and binding
algebra. Normalization is never assumed natural under substitution. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.FamilyIota
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

private theorem related_length (related : Conversion.ListRel (Conversion.Conv env) xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem related_refl (xs : List Term) : Conversion.ListRel (Conversion.Conv env) xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (.refl x) ih

private theorem related_append (first : Conversion.ListRel (Conversion.Conv env) xs ys)
    (second : Conversion.ListRel (Conversion.Conv env) rest rest') :
    Conversion.ListRel (Conversion.Conv env) (xs ++ rest) (ys ++ rest') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem related_reverse (related : Conversion.ListRel (Conversion.Conv env) xs ys) :
    Conversion.ListRel (Conversion.Conv env) xs.reverse ys.reverse := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.reverse_cons] using related_append ih (.cons head .nil)

private theorem related_drop (related : Conversion.ListRel (Conversion.Conv env) xs ys) (n : Nat) :
    Conversion.ListRel (Conversion.Conv env) (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact related
  | succ n ih => cases related with
    | nil => exact .nil
    | cons head tail => exact ih tail

private theorem related_rename (closed : Conversion.Closed env)
    (related : Conversion.ListRel (Conversion.Conv env) xs ys) (ρ : Nat → Nat) :
    Conversion.ListRel (Conversion.Conv env) (xs.map (Term.rename ρ)) (ys.map (Term.rename ρ)) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.renaming ρ closed) ih

private theorem related_lookup (related : Conversion.ListRel (Conversion.Conv env) xs ys) (x : Nat) :
    match xs[x]?,ys[x]? with
    | none,none => True
    | some a,some b => Conversion.Conv env a b
    | _,_ => False := by
  induction related generalizing x with
  | nil => simp
  | cons head tail ih => cases x with
    | zero => exact head
    | succ x => exact ih x

/-- The actual parameter substitutions are pointwise converted, including
all malformed/free-variable fallback positions. -/
theorem parameterAt_congr (closed : Conversion.Closed env)
    (related : Conversion.ListRel (Conversion.Conv env) ps qs) (depth locals x : Nat) :
    Conversion.Conv env (parameterAt depth locals ps x) (parameterAt depth locals qs x) := by
  have sameLength := related_length related
  by_cases bound : x < locals
  · simp only [parameterAt,bound,↓reduceIte]
    exact .refl _
  · simp only [parameterAt,bound,↓reduceIte]
    have selected := related_lookup (related_reverse related) (x-locals)
    cases left : ps.reverse[x-locals]? with
    | none =>
      cases right : qs.reverse[x-locals]? with
      | none =>
        simp only [left,right,Option.map_none,Option.getD_none]
        rw [sameLength]
        exact .refl _
      | some value => simp only [left,right] at selected
    | some value =>
      cases right : qs.reverse[x-locals]? with
      | none => simp only [left,right] at selected
      | some value' =>
        simp only [left,right,Option.map_some,Option.getD_some] at selected ⊢
        exact selected.renaming _ closed

theorem parameter_term_congr (closed : Conversion.Closed env)
    (related : Conversion.ListRel (Conversion.Conv env) ps qs) (depth locals : Nat) (term : Term) :
    Conversion.Conv env (term.subst (parameterAt depth locals ps)) (term.subst (parameterAt depth locals qs)) :=
  RawLend.Conv.subst_congr closed (parameterAt_congr closed related depth locals) term

private theorem indices_congr (closed : Conversion.Closed env)
    (related : Conversion.ListRel (Conversion.Conv env) ps qs) (depth locals : Nat) (indices : List Term) :
    Conversion.ListRel (Conversion.Conv env) (indices.map (Term.subst (parameterAt depth locals ps)))
      (indices.map (Term.subst (parameterAt depth locals qs))) := by
  induction indices with
  | nil => exact .nil
  | cons index indices ih => exact .cons (parameter_term_congr closed related depth locals index) ih

private theorem constructor_congr (related : Conversion.ListRel (Conversion.Conv env) xs ys) :
    Conversion.Conv env (.node (.con family constructor xs.length) xs) (.node (.con family constructor ys.length) ys) := by
  rw [← related_length related]
  exact .node _ related

theorem dataCaseResult_parameters_congr (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs)
    (indices : Conversion.ListRel (Conversion.Conv env) xs ys) :
    Conversion.Conv env (dataCaseResult family constructor params fields hypotheses ps motive xs)
      (dataCaseResult family constructor params fields hypotheses qs motive ys) := by
  apply RawLend.Conv.node .app
  refine .cons (applications_congr (.refl _) (related_rename closed (related_drop indices params) _)) (.cons ?_ .nil)
  exact constructor_congr (related_append (related_rename closed parameters _) (related_refl _))

theorem instantiated_telescope_parameters_congr (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs) (fields : List Field)
    (body : Conversion.Conv env result result') (position : Nat) :
    Conversion.Conv env (closeDataFields (instantiatedFields depth ps recursion position fields) result)
      (closeDataFields (instantiatedFields depth qs recursion position fields) result') := by
  induction fields generalizing position with
  | nil => exact body
  | cons field fields ih =>
    exact .node (.pi (if recursion && field.recursive.isSome then true else field.erased))
      (.cons (parameter_term_congr closed parameters depth position field.domain) (.cons (ih (position+1)) .nil))

/-- Successful nonrecursive Case generation transports to genuinely converted
parameters. Both resulting Option computations and the actual type relation
are proved; no external builder certificate is accepted. -/
theorem dataCaseType_parameters_congr (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs)
    (generated : dataCaseType family constructor params depth signature ps motive false proof = some type) :
    ∃ type',dataCaseType family constructor params depth signature qs motive false proof = some type' ∧
      Conversion.Conv env type type' := by
  have length := related_length parameters
  unfold dataCaseType at generated ⊢
  split at generated
  · contradiction
  · rename_i valid
    simp only [← length,valid,ite_false,Bool.false_eq_true,↓reduceIte,List.length_nil,
      dataHypothesisTelescope,List.zipIdx_nil,List.foldr_nil] at generated ⊢
    cases generated
    exact ⟨_,rfl,instantiated_telescope_parameters_congr closed parameters _
      (dataCaseResult_parameters_congr closed parameters (indices_congr closed parameters _ _ _)) 0⟩

end Jihoo.NativeKernel.Environment.LoanTyping.FamilyIota
