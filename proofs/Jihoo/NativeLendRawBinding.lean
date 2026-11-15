import Jihoo.NativeLendRawConversion
import Jihoo.NativeFamilyIotaForwardAPI

/-! Arbitrary raw Lend binding and environment-prefix stability. The source
checker's variable-only dependent callback gate is not imposed on raw equations. -/
namespace Jihoo.NativeKernel.Environment.RawLend

theorem lendTerm_rename (owner reader continuation : Term) (ρ : Nat → Nat) :
    (lendTerm owner reader continuation).rename ρ = lendTerm (owner.rename ρ) (reader.rename ρ) (continuation.rename ρ) := by
  simp only [lendTerm,Term.rename,renameArgs,Op.binders,liftRenaming]

theorem desugar_rename (owner reader continuation : Term) (ρ : Nat → Nat) :
    (desugar owner reader continuation).rename ρ = desugar (owner.rename ρ) (reader.rename ρ) (continuation.rename ρ) := by
  simp only [desugar,Term.app,Term.borrow,Term.rename,renameArgs,Op.binders,liftRenaming]

theorem lendTerm_subst (owner reader continuation : Term) (σ : Nat → Term) :
    (lendTerm owner reader continuation).subst σ = lendTerm (owner.subst σ) (reader.subst σ) (continuation.subst σ) := by
  simp only [lendTerm,Term.subst,substArgs,Op.binders,liftSub]

theorem desugar_subst (owner reader continuation : Term) (σ : Nat → Term) :
    (desugar owner reader continuation).subst σ = desugar (owner.subst σ) (reader.subst σ) (continuation.subst σ) := by
  simp only [desugar,Term.app,Term.borrow,Term.subst,substArgs,Op.binders,liftSub]

theorem Conv.extend (converted : Conv before a b) (extension : Extends before after) : Conv after a b := by
  induction converted using Conv.rec (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (Conv after) xs ys) with
  | old original => exact .old (original.extend extension)
  | lend owner reader continuation => exact .lend owner reader continuation
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

theorem Conv.renaming (converted : Conv env a b) (ρ : Nat → Nat) (closed : EnvironmentDelta.Basis.Closed env) :
    Conv env (a.rename ρ) (b.rename ρ) := by
  induction converted using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset ρ,
      NativeKernel.Conversion.ListRel (Conv env) (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | old original => exact .old (original.renaming ρ closed)
  | lend owner reader continuation =>
      simpa only [lendTerm_rename,desugar_rename] using Conv.lend (env := env)
        (owner.rename ρ) (reader.rename ρ) (continuation.rename ρ)
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih ρ)
  | trans _ _ first second => exact .trans (first ρ) (second ρ)
  | node op _ ih => simpa only [Term.rename] using Conv.node op (ih op 0 ρ)
  | nil => intros;simp only [renameArgs];exact .nil
  | cons _ _ first rest =>
    rename_i op offset ρ
    simp only [renameArgs]
    exact .cons (first _) (rest op (offset+1) ρ)

theorem Conv.substitution (converted : Conv env a b) (σ : Nat → Term) (closed : EnvironmentDelta.Basis.Closed env) :
    Conv env (a.subst σ) (b.subst σ) := by
  induction converted using Conv.rec
    (motive_2 := fun xs ys _ => ∀ op offset σ,
      NativeKernel.Conversion.ListRel (Conv env) (substArgs op σ offset xs) (substArgs op σ offset ys)) generalizing σ with
  | old original => exact .old (original.substitution σ closed)
  | lend owner reader continuation =>
      simpa only [lendTerm_subst,desugar_subst] using Conv.lend (env := env)
        (owner.subst σ) (reader.subst σ) (continuation.subst σ)
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih σ)
  | trans _ _ first second => exact .trans (first σ) (second σ)
  | node op _ ih => simpa only [Term.subst] using Conv.node op (ih op 0 σ)
  | nil => intros;simp only [substArgs];exact .nil
  | cons _ _ first rest =>
    rename_i op offset σ
    simp only [substArgs]
    exact .cons (first _) (rest op (offset+1) σ)

private theorem lift_related {σ τ : Nat → Term} (closed : EnvironmentDelta.Basis.Closed env) (related : ∀ x,Conv env (σ x) (τ x)) (n : Nat) :
    ∀ x,Conv env (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact related
  | succ n ih => intro x;cases x with
    | zero => exact .refl _
    | succ x => exact (ih x).renaming Nat.succ closed

theorem Conv.subst_congr {σ τ : Nat → Term} (closed : EnvironmentDelta.Basis.Closed env) (related : ∀ x,Conv env (σ x) (τ x)) (term : Term) :
    Conv env (term.subst σ) (term.subst τ) := by
  induction term using Term.rec
    (motive_2 := fun xs => ∀ op offset σ τ,(∀ x,Conv env (σ x) (τ x)) →
      NativeKernel.Conversion.ListRel (Conv env) (substArgs op σ offset xs) (substArgs op τ offset xs)) generalizing σ τ with
  | var x => simp only [Term.subst];exact related x
  | node op _ ih => simpa only [Term.subst] using Conv.node op (ih op 0 σ τ related)
  | nil => intros;simp only [substArgs];exact .nil
  | cons _ _ first rest =>
    rename_i op offset σ τ related
    simp only [substArgs]
    exact .cons (first (lift_related closed related _)) (rest op (offset+1) σ τ related)


theorem Forward.extend (forward : Forward before a b) (extension : Extends before after) : Forward after a b := by
  induction forward using Forward.rec (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (Forward after) xs ys) with
  | old original => exact .old (original.extend extension)
  | lend owner reader continuation => exact .lend owner reader continuation
  | refl => exact .refl
  | trans _ _ first second => exact .trans first second
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

end Jihoo.NativeKernel.Environment.RawLend
