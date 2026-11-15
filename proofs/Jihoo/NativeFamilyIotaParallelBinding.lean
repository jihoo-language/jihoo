import Jihoo.NativeFamilyIotaParallelInput

/-! Full joint arbitrary substitution and renaming for the enlarged family/ACU
quotient parallel calculus; every original binder and raw metadata guard remains. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
open NativeKernel.Conversion (ListRel)
open ACU
variable {env : Environment}
local notation "QPar" => Parallel env
local notation "QAtom" => Atom env
set_option linter.unusedSimpArgs false

private theorem variable_rename_function (ρ : Nat → Nat) : Term.subst (fun x => .var (ρ x)) = Term.rename ρ := by
  funext term
  simpa only [Term.subst_id,Term.rename] using (Term.rename_subst term Term.var ρ).symm

private theorem elimTerm_renaming (family : Nat) (motive scrutinee : Term) (cases : List Term) (ρ : Nat → Nat) :
    (elimTerm family motive cases scrutinee).rename ρ =
      elimTerm family (motive.rename ρ) (cases.map (Term.rename ρ)) (scrutinee.rename ρ) := by
  simpa only [variable_rename_function] using elimTerm_subst family motive scrutinee cases (fun x => .var (ρ x))

private theorem caseTerm_renaming (family : Nat) (motive scrutinee : Term) (cases : List Term) (ρ : Nat → Nat) :
    (caseTerm family motive cases scrutinee).rename ρ =
      caseTerm family (motive.rename ρ) (cases.map (Term.rename ρ)) (scrutinee.rename ρ) := by
  simpa only [variable_rename_function] using caseTerm_subst family motive scrutinee cases (fun x => .var (ρ x))

private theorem viewTerm_renaming (recursion : Bool) (family : Nat) (motive scrutinee : Term) (cases : List Term) (ρ : Nat → Nat) :
    (viewTerm recursion family motive cases scrutinee).rename ρ =
      viewTerm recursion family (motive.rename ρ) (cases.map (Term.rename ρ)) (scrutinee.rename ρ) := by
  simpa only [variable_rename_function] using viewTerm_subst recursion family motive scrutinee cases (fun x => .var (ρ x))

private theorem constructor_renaming (family constructor : Nat) (values : List Term) (ρ : Nat → Nat) :
    (Term.node (.con family constructor values.length) values).rename ρ =
      .node (.con family constructor (values.map (Term.rename ρ)).length) (values.map (Term.rename ρ)) := by
  simpa only [variable_rename_function] using constructor_subst family constructor values (fun x => .var (ρ x))

private theorem elimBody_renaming (entry : CheckedFamily) (signature : Signature) (family : Nat)
    (motive branch : Term) (cases values : List Term) (ρ : Nat → Nat) :
    (elimBody entry signature family motive branch cases values).rename ρ =
      elimBody entry signature family (motive.rename ρ) (branch.rename ρ)
        (cases.map (Term.rename ρ)) (values.map (Term.rename ρ)) := by
  simpa only [variable_rename_function] using elimBody_subst entry signature family motive branch cases values (fun x => .var (ρ x))

private theorem viewBody_renaming (recursion : Bool) (family params : Nat) (motive branch : Term)
    (cases values : List Term) (plans : List ViewFieldPlan) (ρ : Nat → Nat) :
    (viewBody recursion family params motive branch cases values plans).rename ρ =
      viewBody recursion family params (motive.rename ρ) (branch.rename ρ)
        (cases.map (Term.rename ρ)) (values.map (Term.rename ρ)) plans := by
  simpa only [variable_rename_function] using viewBody_subst recursion family params motive branch cases values plans (fun x => .var (ρ x))

private theorem applications_substitution (function : Term) (values : List Term) (σ : Nat → Term) :
    (applications function values).subst σ = applications (function.subst σ) (values.map (Term.subst σ)) := by
  induction values generalizing function with
  | nil => rfl
  | cons value values ih =>
    simp only [applications,List.foldl_cons,List.map_cons] at ih ⊢
    rw [ih]
    simp only [Term.subst,substArgs,Op.binders,liftSub]

private theorem applications_renaming (function : Term) (values : List Term) (ρ : Nat → Nat) :
    (applications function values).rename ρ = applications (function.rename ρ) (values.map (Term.rename ρ)) := by
  simpa only [variable_rename_function] using applications_substitution function values (fun x => .var (ρ x))

private theorem borrow_substitution (value : Term) (σ : Nat → Term) :
    (Term.borrow value).subst σ = .borrow (value.subst σ) := by
  simp only [Term.subst,substArgs,Op.binders,liftSub]

private theorem borrow_renaming (value : Term) (ρ : Nat → Nat) :
    (Term.borrow value).rename ρ = .borrow (value.rename ρ) := by
  simpa only [variable_rename_function] using borrow_substitution value (fun x => .var (ρ x))

theorem Parallel.sumTerms (h : ListRel QPar xs ys) : QPar (ACU.sumTerms xs) (ACU.sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact h.addCong ih

private theorem rename_sumTerms (xs : List Term) (ρ : Nat → Nat) :
    (sumTerms xs).rename ρ = sumTerms (xs.map (Term.rename ρ)) := by
  induction xs with
  | nil => simp only [sumTerms,List.map_nil,Term.rename,renameArgs]
  | cons x xs ih => simp only [sumTerms,Term.rename,renameArgs,Op.binders,liftRenaming,List.map_cons,ih]

private theorem subst_sumTerms (xs : List Term) (σ : Nat → Term) :
    (sumTerms xs).subst σ = sumTerms (xs.map (Term.subst σ)) := by
  induction xs with
  | nil => simp only [sumTerms,List.map_nil,Term.subst,substArgs]
  | cons x xs ih => simp only [sumTerms,Term.subst,substArgs,Op.binders,liftSub,List.map_cons,ih]

private theorem rename_natural (h : Arithmetic a (.natural n)) (ρ : Nat → Nat) :
    Arithmetic (a.rename ρ) (.natural n) := by
  simpa only [Term.rename,renameArgs] using h.renaming ρ

/-- Quotient parallel computation is stable under capture-safe renaming. -/
theorem Parallel.renaming (h : QPar a b) (ρ : Nat → Nat) : QPar (a.rename ρ) (b.rename ρ) := by
  induction h using Parallel.rec
    (motive_2 := fun x y _ => ∀ ρ, QPar (x.rename ρ) (y.rename ρ))
    (motive_3 := fun xs ys _ => ∀ ρ, ListRel QPar (xs.map (Term.rename ρ)) (ys.map (Term.rename ρ)))
    (motive_4 := fun xs ys _ => ∀ op offset ρ,
      ListRel QPar (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | intro p hs out ih =>
      have input := ((Arithmetic.flatten _).trans (Arithmetic.sumTerms_perm p)).renaming ρ
      have output := out.renaming ρ
      rw [rename_sumTerms] at input output
      exact ((Parallel.sumTerms (ih ρ)).input input.symm).output output.symm
  | var x => rename_i ρ; exact .refl _
  | node op hs ih => rename_i ρ; simpa only [Term.rename] using Parallel.node op (ih op 0 ρ)
  | beta e A body view hb ha ib ia =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,Term.rename_instantiate] using
        Atom.beta e (A.rename ρ) (body.rename (Indexed.liftRenaming ρ))
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ)
          (ib (Indexed.liftRenaming ρ)) (ia ρ)
  | sub m n p left right bound valid =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.sub m n (p.rename ρ) (rename_natural left ρ) (rename_natural right ρ) bound valid
  | read count k p arr index hs selected ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.read count k (p.rename ρ) (by simpa only [Term.rename,NativeKernel.Conversion.renameArgs_elements] using arr.renaming ρ)
          (rename_natural index ρ) (by simpa only [NativeKernel.Conversion.renameArgs_elements] using ih (.elements count) 0 ρ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | witnessPack p a q view ha ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.witnessPack (p.rename ρ) (a.rename ρ) (q.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | proofPack p a q view ha ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.proofPack (p.rename ρ) (a.rename ρ) (q.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | derefBorrow a view ha ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.derefBorrow (a.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | borrowDeref a view ha ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.borrowDeref (a.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | transportRefl a view hp ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.transportRefl (a.rename ρ)
          (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using view.renaming ρ) (ih ρ)
  | ifLtTrue m n no left right bound hy ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,Term.rename_instantiate] using
        Atom.ifLtTrue m n (no.rename ρ) (rename_natural left ρ) (rename_natural right ρ) bound (ih (Indexed.liftRenaming ρ))
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.ifLtFalse m n (yes.rename (Indexed.liftRenaming ρ)) (rename_natural left ρ) (rename_natural right ρ) bound (ih ρ)
  | ifEqTrue n no left right hy ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,Term.rename_instantiate] using
        Atom.ifEqTrue n (no.rename ρ) (rename_natural left ρ) (rename_natural right ρ) (ih (Indexed.liftRenaming ρ))
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using
        Atom.ifEqFalse m n (yes.rename (Indexed.liftRenaming ρ)) (rename_natural left ρ) (rename_natural right ρ) bound (ih ρ)
  | elim family constructor entry signature motive cases scrutinee found sigFound count fields view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i values motiveOut casesOut valuesOut branchOut ρ
      apply Parallel.ofAtom (atomic := by simp only [elimTerm,Term.rename,arithmeticFlatten])
      simpa only [elimTerm_renaming,elimBody_renaming] using
        Atom.elim (values := values.map (Term.rename ρ)) family constructor entry signature (motive.rename ρ) (cases.map (Term.rename ρ)) (scrutinee.rename ρ)
          found sigFound (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
          (by simpa only [constructor_renaming] using view.renaming ρ) (ihMotive ρ) (by simpa only [NativeKernel.Conversion.renameArgs_elements] using ihCases (.elements 0) 0 ρ) (by simpa only [NativeKernel.Conversion.renameArgs_elements] using ihValues (.elements 0) 0 ρ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | caseOf family constructor entry signature motive cases scrutinee found data sigFound count fields view caseSteps valueSteps selected ihCases ihValues =>
      rename_i values casesOut valuesOut branchOut ρ
      apply Parallel.ofAtom (atomic := by simp only [caseTerm,Term.rename,arithmeticFlatten])
      simpa only [caseTerm_renaming,applications_renaming,List.map_drop] using
        Atom.caseOf (values := values.map (Term.rename ρ)) family constructor entry signature (motive.rename ρ) (cases.map (Term.rename ρ)) (scrutinee.rename ρ)
          found data sigFound (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
          (by simpa only [constructor_renaming] using view.renaming ρ) (by simpa only [NativeKernel.Conversion.renameArgs_elements] using ihCases (.elements 0) 0 ρ) (by simpa only [NativeKernel.Conversion.renameArgs_elements] using ihValues (.elements 0) 0 ρ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | view recursion family constructor entry signature motive cases scrutinee found boxed sigFound count fields bound planned view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i plans values motiveOut casesOut valuesOut branchOut ρ
      apply Parallel.ofAtom (atomic := by simp only [viewTerm,Term.rename,arithmeticFlatten])
      simpa only [viewTerm_renaming,viewBody_renaming] using
        Atom.view (values := values.map (Term.rename ρ)) recursion family constructor entry signature (motive.rename ρ) (cases.map (Term.rename ρ)) (scrutinee.rename ρ)
          found boxed sigFound (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields) bound planned
          (by simpa only [borrow_renaming,constructor_renaming] using view.renaming ρ) (ihMotive ρ) (by simpa only [NativeKernel.Conversion.renameArgs_elements] using ihCases (.elements 0) 0 ρ) (by simpa only [NativeKernel.Conversion.renameArgs_elements] using ihValues (.elements 0) 0 ρ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | drop family owner rest restStep ih =>
      rename_i ρ
      apply Parallel.ofAtom (atomic := by simp only [Term.rename,renameArgs,Op.binders,liftRenaming,arithmeticFlatten])
      simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using Atom.drop family (owner.rename ρ) (rest.rename ρ) (ih ρ)
  | nil => rename_i ρ; exact .nil
  | cons h hs ih is => rename_i ρ; exact .cons (ih ρ) (is ρ)
  | _ =>
      rename_i op
      intro offset ρ
      simp only [renameArgs]
      first
        | exact .nil
        | apply ListRel.cons
          · apply_assumption
          · apply_assumption

private theorem lift_qpar {σ τ : Nat → Term} (h : ∀ x, QPar (σ x) (τ x)) (n : Nat) :
    ∀ x, QPar (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x
      cases x with
      | zero => exact .refl _
      | succ x => exact (ih x).renaming Nat.succ

private theorem subst_natural (h : Arithmetic a (.natural n)) (σ : Nat → Term) :
    Arithmetic (a.subst σ) (.natural n) := by
  simpa only [Term.subst,substArgs] using h.substitution σ

/-- Joint parallel substitution on all native terms, with lifted substitutions
at every binding edge. No affine-fragment substitution premise is used. -/
theorem Parallel.substitution {σ τ : Nat → Term} (h : QPar a b) (hσ : ∀ x, QPar (σ x) (τ x)) :
    QPar (a.subst σ) (b.subst τ) := by
  induction h using Parallel.rec
    (motive_2 := fun x y _ => ∀ σ τ, (∀ i, QPar (σ i) (τ i)) → QPar (x.subst σ) (y.subst τ))
    (motive_3 := fun xs ys _ => ∀ σ τ, (∀ i, QPar (σ i) (τ i)) →
      ListRel QPar (xs.map (Term.subst σ)) (ys.map (Term.subst τ)))
    (motive_4 := fun xs ys _ => ∀ op offset σ τ, (∀ i, QPar (σ i) (τ i)) →
      ListRel QPar (substArgs op σ offset xs) (substArgs op τ offset ys)) generalizing σ τ with
  | intro p hs out ih =>
      have input := ((Arithmetic.flatten _).trans (Arithmetic.sumTerms_perm p)).substitution σ
      have output := out.substitution τ
      rw [subst_sumTerms] at input output
      exact ((Parallel.sumTerms (ih σ τ hσ)).input input.symm).output output.symm
  | var x => rename_i σ τ hσ; simpa only [Term.subst] using hσ x
  | node op hs ih => rename_i σ τ hσ; simpa only [Term.subst] using Parallel.node op (ih op 0 σ τ hσ)
  | beta e A body view hb ha ib ia =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub,Term.subst_instantiate] using
        Atom.beta e (A.subst σ) (body.subst (liftSubOne σ))
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ)
          (ib (lift_qpar hσ 1)) (ia hσ)
  | sub m n p left right bound valid =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.sub m n (p.subst σ) (subst_natural left σ) (subst_natural right σ) bound valid
  | read count k p arr index hs selected ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.read count k (p.subst σ) (by simpa only [Term.subst,NativeKernel.Conversion.substArgs_elements] using arr.substitution σ)
          (subst_natural index σ) (by simpa only [NativeKernel.Conversion.substArgs_elements] using ih (.elements count) 0 σ τ hσ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | witnessPack p a q view ha ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.witnessPack (p.subst σ) (a.subst σ) (q.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | proofPack p a q view ha ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.proofPack (p.subst σ) (a.subst σ) (q.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | derefBorrow a view ha ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.derefBorrow (a.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | borrowDeref a view ha ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.borrowDeref (a.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | transportRefl a view hp ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.transportRefl (a.subst σ)
          (by simpa only [Term.subst,substArgs,Op.binders,liftSub] using view.substitution σ) (ih hσ)
  | ifLtTrue m n no left right bound hy ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub,Term.subst_instantiate] using
        Atom.ifLtTrue m n (no.subst σ) (subst_natural left σ) (subst_natural right σ) bound (ih (lift_qpar hσ 1))
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.ifLtFalse m n (yes.subst (liftSubOne σ)) (subst_natural left σ) (subst_natural right σ) bound (ih hσ)
  | ifEqTrue n no left right hy ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub,Term.subst_instantiate] using
        Atom.ifEqTrue n (no.subst σ) (subst_natural left σ) (subst_natural right σ) (ih (lift_qpar hσ 1))
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using
        Atom.ifEqFalse m n (yes.subst (liftSubOne σ)) (subst_natural left σ) (subst_natural right σ) bound (ih hσ)
  | elim family constructor entry signature motive cases scrutinee found sigFound count fields view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i values motiveOut casesOut valuesOut branchOut σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [elimTerm,Term.subst,arithmeticFlatten])
      simpa only [elimTerm_subst,elimBody_subst] using
        Atom.elim (values := values.map (Term.subst σ)) family constructor entry signature (motive.subst σ) (cases.map (Term.subst σ)) (scrutinee.subst σ)
          found sigFound (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
          (by simpa only [constructor_subst] using view.substitution σ) (ihMotive hσ) (by simpa only [NativeKernel.Conversion.substArgs_elements] using ihCases (.elements 0) 0 σ τ hσ) (by simpa only [NativeKernel.Conversion.substArgs_elements] using ihValues (.elements 0) 0 σ τ hσ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | caseOf family constructor entry signature motive cases scrutinee found data sigFound count fields view caseSteps valueSteps selected ihCases ihValues =>
      rename_i values casesOut valuesOut branchOut σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [caseTerm,Term.subst,arithmeticFlatten])
      simpa only [caseTerm_subst,applications_substitution,List.map_drop] using
        Atom.caseOf (values := values.map (Term.subst σ)) family constructor entry signature (motive.subst σ) (cases.map (Term.subst σ)) (scrutinee.subst σ)
          found data sigFound (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields)
          (by simpa only [constructor_subst] using view.substitution σ) (by simpa only [NativeKernel.Conversion.substArgs_elements] using ihCases (.elements 0) 0 σ τ hσ) (by simpa only [NativeKernel.Conversion.substArgs_elements] using ihValues (.elements 0) 0 σ τ hσ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | view recursion family constructor entry signature motive cases scrutinee found boxed sigFound count fields bound planned view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i plans values motiveOut casesOut valuesOut branchOut σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [viewTerm,Term.subst,arithmeticFlatten])
      simpa only [viewTerm_subst,viewBody_subst] using
        Atom.view (values := values.map (Term.subst σ)) recursion family constructor entry signature (motive.subst σ) (cases.map (Term.subst σ)) (scrutinee.subst σ)
          found boxed sigFound (by simpa only [List.length_map] using count) (by simpa only [List.length_map] using fields) bound planned
          (by simpa only [borrow_substitution,constructor_subst] using view.substitution σ) (ihMotive hσ) (by simpa only [NativeKernel.Conversion.substArgs_elements] using ihCases (.elements 0) 0 σ τ hσ) (by simpa only [NativeKernel.Conversion.substArgs_elements] using ihValues (.elements 0) 0 σ τ hσ)
          (by simp only [List.getElem?_map,selected,Option.map_some])
  | drop family owner rest restStep ih =>
      rename_i σ τ hσ
      apply Parallel.ofAtom (atomic := by simp only [Term.subst,substArgs,Op.binders,liftSub,arithmeticFlatten])
      simpa only [Term.subst,substArgs,Op.binders,liftSub] using Atom.drop family (owner.subst σ) (rest.subst σ) (ih hσ)
  | nil => rename_i σ τ hσ; exact .nil
  | cons h hs ih is => rename_i σ τ hσ; exact .cons (ih σ τ hσ) (is σ τ hσ)
  | _ =>
      rename_i op offset σ
      intro τ hσ
      simp only [substArgs]
      first
        | exact .nil
        | apply ListRel.cons
          · apply_assumption; exact lift_qpar hσ _
          · apply_assumption; exact hσ

theorem Parallel.instantiate (hb : QPar body body') (ha : QPar a a') :
    QPar (body.subst (single a)) (body'.subst (single a')) := by
  apply hb.substitution
  intro x
  cases x with
  | zero => exact ha
  | succ x => exact .refl _


end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
