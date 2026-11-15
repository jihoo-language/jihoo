import Jihoo.NativeFamilyIotaSyntax
import Jihoo.NativeSubstitution

/-! Syntax-only arbitrary substitution/renaming for every genuine family root. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota
set_option linter.unusedSimpArgs false

private theorem iota_applications_subst (function : Term) (values : List Term) (σ : Nat → Term) :
    (applications function values).subst σ = applications (function.subst σ) (values.map (Term.subst σ)) := by
  induction values generalizing function with
  | nil => rfl
  | cons value values ih =>
    simp only [applications,List.foldl_cons,List.map_cons] at ih ⊢
    rw [ih]
    simp only [Term.subst,substArgs,Op.binders,liftSub]

private theorem iota_variable_subst_eq_rename (term : Term) (ρ : Nat → Nat) :
    term.subst (fun x => .var (ρ x)) = term.rename ρ := by
  simpa only [Term.subst_id,Term.rename] using (Term.rename_subst term Term.var ρ).symm

private theorem substArgs_nonbinding (zero : ∀ i,op.binders i = 0) (σ : Nat → Term)
    (offset : Nat) (values : List Term) : substArgs op σ offset values = values.map (Term.subst σ) := by
  induction values generalizing offset with
  | nil => simp only [substArgs,List.map_nil]
  | cons value values ih => simp only [substArgs,zero,liftSub,ih,List.map_cons]

private theorem nonbinding_subst (zero : ∀ i,op.binders i = 0) (values : List Term) (σ : Nat → Term) :
    (Term.node op values).subst σ = .node op (values.map (Term.subst σ)) := by
  simp only [Term.subst,substArgs_nonbinding zero]

theorem elimTerm_subst (family : Nat) (motive scrutinee : Term) (cases : List Term) (σ : Nat → Term) :
    (elimTerm family motive cases scrutinee).subst σ =
      elimTerm family (motive.subst σ) (cases.map (Term.subst σ)) (scrutinee.subst σ) := by
  unfold elimTerm
  rw [nonbinding_subst (by intro i; rfl)]
  simp only [List.map_cons,List.map_append,List.map_nil,List.length_map]

theorem caseTerm_subst (family : Nat) (motive scrutinee : Term) (cases : List Term) (σ : Nat → Term) :
    (caseTerm family motive cases scrutinee).subst σ =
      caseTerm family (motive.subst σ) (cases.map (Term.subst σ)) (scrutinee.subst σ) := by
  unfold caseTerm
  rw [nonbinding_subst (by intro i; rfl)]
  simp only [List.map_cons,List.map_append,List.map_nil,List.length_map]

theorem viewTerm_subst (recursion : Bool) (family : Nat) (motive scrutinee : Term)
    (cases : List Term) (σ : Nat → Term) :
    (viewTerm recursion family motive cases scrutinee).subst σ =
      viewTerm recursion family (motive.subst σ) (cases.map (Term.subst σ)) (scrutinee.subst σ) := by
  unfold viewTerm
  rw [nonbinding_subst (by intro i; rfl)]
  simp only [List.map_cons,List.map_append,List.map_nil,List.length_map]

theorem constructor_subst (family constructor : Nat) (values : List Term) (σ : Nat → Term) :
    (Term.node (.con family constructor values.length) values).subst σ =
      .node (.con family constructor (values.map (Term.subst σ)).length) (values.map (Term.subst σ)) := by
  simpa only [List.length_map] using nonbinding_subst (op := .con family constructor values.length) (by intro i; rfl) values σ

private theorem borrow_subst (value : Term) (σ : Nat → Term) :
    (Term.borrow value).subst σ = .borrow (value.subst σ) := by
  simp only [Term.subst,substArgs,Op.binders,liftSub]

theorem elimHypotheses_subst (family : Nat) (motive : Term) (cases : List Term)
    (fields : List Field) (values : List Term) (σ : Nat → Term) :
    (elimHypotheses family motive cases fields values).map (Term.subst σ) =
      elimHypotheses family (motive.subst σ) (cases.map (Term.subst σ)) fields (values.map (Term.subst σ)) := by
  induction fields generalizing values with
  | nil => simp only [elimHypotheses,List.zip_nil_left,List.filterMap_nil,List.map_nil]
  | cons field fields ih =>
    cases values with
    | nil => simp [elimHypotheses]
    | cons value values =>
      have tail := ih values
      unfold elimHypotheses at tail
      by_cases recursive : field.recursive.isSome = true <;>
        simp only [elimHypotheses,List.zip_cons_cons,List.map_cons,List.filterMap_cons,
          recursive,Bool.false_eq_true,↓reduceIte,List.map_nil,elimTerm_subst,tail]

theorem elimBody_subst (entry : CheckedFamily) (signature : Signature) (family : Nat)
    (motive branch : Term) (cases values : List Term) (σ : Nat → Term) :
    (elimBody entry signature family motive branch cases values).subst σ =
      elimBody entry signature family (motive.subst σ) (branch.subst σ)
        (cases.map (Term.subst σ)) (values.map (Term.subst σ)) := by
  simp only [elimBody,iota_applications_subst,List.map_drop,elimHypotheses_subst]

theorem viewArguments_subst (plans : List ViewFieldPlan) (values : List Term) (σ : Nat → Term) :
    (viewArguments plans values).map (Term.subst σ) = viewArguments plans (values.map (Term.subst σ)) := by
  induction plans generalizing values with
  | nil => simp [viewArguments]
  | cons plan plans ih =>
    cases values with
    | nil => simp [viewArguments]
    | cons value values =>
      have tail := ih values
      unfold viewArguments at tail
      by_cases borrowed : plan.borrowed = true <;>
        simp only [viewArguments,List.zip_cons_cons,List.map_cons,borrowed,Bool.false_eq_true,↓reduceIte,borrow_subst,tail]

theorem viewHypotheses_subst (recursion : Bool) (family : Nat) (motive : Term) (cases : List Term)
    (plans : List ViewFieldPlan) (values : List Term) (σ : Nat → Term) :
    (viewHypotheses recursion family motive cases plans values).map (Term.subst σ) =
      viewHypotheses recursion family (motive.subst σ) (cases.map (Term.subst σ)) plans (values.map (Term.subst σ)) := by
  cases recursion with
  | false => simp [viewHypotheses]
  | true =>
    induction plans generalizing values with
    | nil => simp [viewHypotheses]
    | cons plan plans ih =>
      cases values with
      | nil => simp [viewHypotheses]
      | cons value values =>
        have tail := ih values
        simp only [viewHypotheses,↓reduceIte] at tail
        by_cases self : plan.self = true <;>
          simp only [viewHypotheses,↓reduceIte,List.zip_cons_cons,List.map_cons,List.filterMap_cons,
            self,Bool.false_eq_true,viewTerm_subst,borrow_subst,tail]

theorem viewBody_subst (recursion : Bool) (family params : Nat) (motive branch : Term)
    (cases values : List Term) (plans : List ViewFieldPlan) (σ : Nat → Term) :
    (viewBody recursion family params motive branch cases values plans).subst σ =
      viewBody recursion family params (motive.subst σ) (branch.subst σ)
        (cases.map (Term.subst σ)) (values.map (Term.subst σ)) plans := by
  simp only [viewBody,iota_applications_subst,List.map_drop,viewArguments_subst,viewHypotheses_subst]

theorem Root.substitution (step : Root env term result) (σ : Nat → Term) :
    Root env (term.subst σ) (result.subst σ) := by
  cases step with
  | elim found signature branch count fields =>
    rw [elimTerm_subst,constructor_subst,elimBody_subst]
    exact .elim found signature (by simp only [List.getElem?_map,branch,Option.map_some])
      (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
  | caseOf found data signature branch count fields =>
    rw [caseTerm_subst,constructor_subst,iota_applications_subst,List.map_drop]
    exact .caseOf found data signature (by simp only [List.getElem?_map,branch,Option.map_some])
      (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
  | view found boxed signature branch count fields params planned =>
    rw [viewTerm_subst,borrow_subst,constructor_subst,viewBody_subst]
    exact .view found boxed signature (by simp only [List.getElem?_map,branch,Option.map_some])
      (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields) params planned
  | drop =>
    simp only [Term.subst,substArgs,Op.binders,liftSub]
    exact .drop _ _ _

theorem Root.renaming (step : Root env term result) (ρ : Nat → Nat) :
    Root env (term.rename ρ) (result.rename ρ) := by
  simpa only [iota_variable_subst_eq_rename] using step.substitution (fun x => .var (ρ x))

end Jihoo.NativeKernel.Environment.FamilyIota
