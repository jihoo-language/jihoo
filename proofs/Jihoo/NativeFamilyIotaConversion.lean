import Jihoo.NativeFamilyIotaSyntaxBinding
import Jihoo.NativeEnvironmentConversionShapes

/-! Genuine enlarged raw delta/ACU/family-iota equations and finite forward
witnesses. No conversion comparison oracle or enlarged confluence is assumed.
This relation is deliberately separate until all typing metatheory is rebased. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended

inductive Conv (env : Environment) : Term → Term → Prop where
  | old : EnvironmentDelta.Basis.Conv env a b → Conv env a b
  | iota : Root env a b → Conv env a b
  | refl (term : Term) : Conv env term term
  | symm : Conv env a b → Conv env b a
  | trans : Conv env a b → Conv env b c → Conv env a c
  | node (op : Op) : NativeKernel.Conversion.ListRel (Conv env) xs ys → Conv env (.node op xs) (.node op ys)

/-- Compatibility injection of the pre-environment native equations. -/
theorem Conv.legacy (step : NativeKernel.Conversion.Conv a b) : Conv env a b := .old (.legacy step)
theorem Conv.acu (step : ACU.Conv a b) : Conv env a b := .old (.acu step)
theorem Conv.delta (found : env.globals[index]? = some declaration) :
    Conv env (.node (.global index) []) declaration.value := .old (.delta found)

inductive Forward (env : Environment) : Term → Term → Prop where
  | old : EnvironmentDelta.Forward env a b → Forward env a b
  | iota : Root env a b → Forward env a b
  | refl : Forward env term term
  | trans : Forward env a b → Forward env b c → Forward env a c
  | node (op : Op) : NativeKernel.Conversion.ListRel (Forward env) xs ys → Forward env (.node op xs) (.node op ys)

theorem Forward.toConv (forward : Forward env a b) : Conv env a b := by
  induction forward using Forward.rec (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (Conv env) xs ys) with
  | old original => exact .old (EnvironmentDelta.Basis.forward_toConv original)
  | iota step => exact .iota step
  | refl => exact .refl _
  | trans _ _ first second => exact .trans first second
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

theorem Conv.ofForwardJoin (left : Forward env a common) (right : Forward env b common) : Conv env a b :=
  left.toConv.trans right.toConv.symm

theorem Conv.extend (converted : Conv before a b) (extension : Extends before after) : Conv after a b := by
  induction converted using Conv.rec (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (Conv after) xs ys) with
  | old original => exact .old (original.extend extension)
  | iota step => exact .iota (step.extend extension)
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
  | iota step => exact .iota (step.renaming ρ)
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
  | iota step => exact .iota (step.substitution σ)
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

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
