import Jihoo.NativeFamilyIotaElimArguments

/-! Full recursive Case telescope congruence under actual converted parameters. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem related_length (related : Conversion.ListRel R xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem related_drop (related : Conversion.ListRel (Conversion.Conv env) xs ys) (n : Nat) :
    Conversion.ListRel (Conversion.Conv env) (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => exact related
  | succ n ih => cases related with
    | nil => exact .nil
    | cons _ tail => exact ih tail

private theorem related_rename (closed : Conversion.Closed env)
    (related : Conversion.ListRel (Conversion.Conv env) xs ys) (ρ : Nat → Nat) :
    Conversion.ListRel (Conversion.Conv env) (xs.map (Term.rename ρ)) (ys.map (Term.rename ρ)) := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.renaming ρ closed) ih

private theorem indices_congr (closed : Conversion.Closed env)
    (related : Conversion.ListRel (Conversion.Conv env) ps qs) (depth locals : Nat) (indices : List Term) :
    Conversion.ListRel (Conversion.Conv env) (indices.map (Term.subst (parameterAt depth locals ps)))
      (indices.map (Term.subst (parameterAt depth locals qs))) := by
  induction indices with
  | nil => exact .nil
  | cons index indices ih => exact .cons (parameter_term_congr closed related depth locals index) ih

private def RecursiveRelated (env : Environment) (left right : Nat × List Term) : Prop :=
  left.1 = right.1 ∧ Conversion.ListRel (Conversion.Conv env) left.2 right.2

private inductive RecursiveListRelated (env : Environment) : List (Nat × List Term) → List (Nat × List Term) → Prop where
  | nil : RecursiveListRelated env [] []
  | cons : RecursiveRelated env pair pair' → RecursiveListRelated env rest rest' →
      RecursiveListRelated env (pair :: rest) (pair' :: rest')

private theorem recursive_length (related : RecursiveListRelated env xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem recursive_congr (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs) :
    RecursiveListRelated env (instantiatedRecursive depth ps fields) (instantiatedRecursive depth qs fields) := by
  unfold instantiatedRecursive
  generalize recursiveFields fields = recursive
  induction recursive with
  | nil => exact .nil
  | cons pair recursive ih => exact .cons ⟨rfl,indices_congr closed parameters _ _ _⟩ ih

private theorem hypothesis_congr (closed : Conversion.Closed env) (related : RecursiveRelated env pair pair') :
    Conversion.Conv env (dataHypothesisType params fields motive pair q) (dataHypothesisType params fields motive pair' q) := by
  rcases pair with ⟨position,indices⟩
  rcases pair' with ⟨position',indices'⟩
  obtain ⟨same,indices⟩ := related
  dsimp only at same
  subst position'
  exact .node .app (.cons (applications_congr (.refl _) (related_rename closed (related_drop indices _) _))
    (.cons (.refl _) .nil))

private theorem hypothesis_telescope_congr (closed : Conversion.Closed env)
    (related : RecursiveListRelated env recursive recursive')
    (body : Conversion.Conv env result result') (offset : Nat) :
    Conversion.Conv env (dataHypothesisTelescope params fields offset recursive proof motive result)
      (dataHypothesisTelescope params fields offset recursive' proof motive result') := by
  induction related generalizing offset with
  | nil => exact body
  | cons head tail ih => exact .node (.pi proof) (.cons (hypothesis_congr closed head) (.cons (ih (offset+1)) .nil))

/-- Recursive and nonrecursive generated branches both transport to actual
constructor parameter values, preserving every IH and annotation. -/
theorem dataCaseType_parameters_congr_all (closed : Conversion.Closed env)
    (parameters : Conversion.ListRel (Conversion.Conv env) ps qs)
    (generated : dataCaseType family constructor params depth signature ps motive recursion proof = some type) :
    ∃ type',dataCaseType family constructor params depth signature qs motive recursion proof = some type' ∧
      Conversion.Conv env type type' := by
  cases recursion with
  | false => exact dataCaseType_parameters_congr closed parameters generated
  | true =>
    have length := related_length parameters
    unfold dataCaseType at generated ⊢
    split at generated
    · contradiction
    · rename_i valid
      simp only [← length,valid,ite_false,ite_true] at generated ⊢
      cases generated
      have recursive := recursive_congr (depth := depth) (fields := signature.fields.drop params) closed parameters
      have count := recursive_length recursive
      refine ⟨_,rfl,instantiated_telescope_parameters_congr closed parameters _ ?_ 0⟩
      apply hypothesis_telescope_congr closed recursive
      rw [← count]
      exact dataCaseResult_parameters_congr closed parameters (indices_congr closed parameters _ _ _)

end Jihoo.NativeKernel.Environment.FamilyIota
