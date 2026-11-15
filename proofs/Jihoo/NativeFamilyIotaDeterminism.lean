import Jihoo.NativeFamilyIotaPreservation

/-! The raw family roots are exact deterministic executable equations, even
for untyped/forged family tables. No typing or admission restricts this result. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem splitCases_complete (cases : List Term) (scrutinee : Term) :
    Checker.splitCases cases.length (cases ++ [scrutinee]) = some (cases,scrutinee) := by
  induction cases with
  | nil => rfl
  | cons branch cases ih =>
    simp only [List.length_cons,List.cons_append,Checker.splitCases,ih,Bind.bind,Option.bind,pure]

theorem Root.complete (step : Root env term result) : contract env term = some result := by
  cases step with
  | elim found signature selected count fields =>
    simp only [elimTerm,contract,eliminate,found,Bind.bind,Option.bind]
    rw [splitCases_complete]
    simp only [Bind.bind,Option.bind,signature,selected,fields,count,true_and,↓reduceIte,Bool.false_eq_true]
  | caseOf found data signature selected count fields =>
    simp only [caseTerm,contract,eliminate,found,Bind.bind,Option.bind]
    rw [splitCases_complete]
    simp only [Bind.bind,Option.bind,signature,selected,fields,count,true_and,↓reduceIte,data]
  | view found boxed signature selected count fields bound planned =>
    simp only [viewTerm,contract,FamilyIota.view,found,Bind.bind,Option.bind]
    rw [splitCases_complete]
    simp only [Bind.bind,Option.bind,signature,selected,fields,count,true_and,↓reduceIte,boxed,bound,planned]
  | drop => rfl

/-- Raw root determinism requires no well-formedness or metadata honesty. -/
theorem Root.deterministic (first : Root env term left) (second : Root env term right) : left = right :=
  Option.some.inj (first.complete.symm.trans second.complete)

theorem contract_iff_root : contract env term = some result ↔ Root env term result :=
  ⟨contract_sound,Root.complete⟩

end Jihoo.NativeKernel.Environment.FamilyIota
