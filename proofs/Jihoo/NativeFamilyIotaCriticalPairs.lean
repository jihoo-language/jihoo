import Jihoo.NativeFamilyIotaRigid

/-! Genuine raw family-only contextual paths and beta/family critical pairs.
All statements include untyped terms and forged family tables. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended

inductive Iota (env : Environment) : Term → Term → Prop where
  | root : Root env a b → Iota env a b
  | refl : Iota env term term
  | trans : Iota env a b → Iota env b c → Iota env a c
  | node (op : Op) : NativeKernel.Conversion.ListRel (Iota env) xs ys → Iota env (.node op xs) (.node op ys)

theorem Iota.toForward (step : Iota env a b) : Forward env a b := by
  induction step using Iota.rec (motive_2 := fun xs ys _ => NativeKernel.Conversion.ListRel (Forward env) xs ys) with
  | root original => exact .iota original
  | refl => exact .refl
  | trans _ _ first second => exact first.trans second
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

theorem Iota.renaming (step : Iota env a b) (ρ : Nat → Nat) : Iota env (a.rename ρ) (b.rename ρ) := by
  induction step using Iota.rec
    (motive_2 := fun xs ys _ => ∀ op offset ρ,
      NativeKernel.Conversion.ListRel (Iota env) (renameArgs op ρ offset xs) (renameArgs op ρ offset ys)) generalizing ρ with
  | root original => exact .root (original.renaming ρ)
  | refl => exact .refl
  | trans _ _ first second => exact (first ρ).trans (second ρ)
  | node op _ ih => simpa only [Term.rename] using Iota.node op (ih op 0 ρ)
  | nil => intros;simp only [renameArgs];exact .nil
  | cons _ _ first rest =>
    rename_i op offset ρ
    simp only [renameArgs]
    exact .cons (first _) (rest op (offset+1) ρ)

theorem Iota.substitution (step : Iota env a b) (σ : Nat → Term) : Iota env (a.subst σ) (b.subst σ) := by
  induction step using Iota.rec
    (motive_2 := fun xs ys _ => ∀ op offset σ,
      NativeKernel.Conversion.ListRel (Iota env) (substArgs op σ offset xs) (substArgs op σ offset ys)) generalizing σ with
  | root original => exact .root (original.substitution σ)
  | refl => exact .refl
  | trans _ _ first second => exact (first σ).trans (second σ)
  | node op _ ih => simpa only [Term.subst] using Iota.node op (ih op 0 σ)
  | nil => intros;simp only [substArgs];exact .nil
  | cons _ _ first rest =>
    rename_i op offset σ
    simp only [substArgs]
    exact .cons (first _) (rest op (offset+1) σ)

private theorem lift_related {σ τ : Nat → Term} (related : ∀ x,Iota env (σ x) (τ x)) (n : Nat) :
    ∀ x,Iota env (liftSub n σ x) (liftSub n τ x) := by
  induction n with
  | zero => exact related
  | succ n ih => intro x;cases x with
    | zero => exact .refl
    | succ x => exact (ih x).renaming Nat.succ

theorem Iota.subst_congr {σ τ : Nat → Term} (related : ∀ x,Iota env (σ x) (τ x)) (term : Term) :
    Iota env (term.subst σ) (term.subst τ) := by
  induction term using Term.rec
    (motive_2 := fun xs => ∀ op offset σ τ,(∀ x,Iota env (σ x) (τ x)) →
      NativeKernel.Conversion.ListRel (Iota env) (substArgs op σ offset xs) (substArgs op τ offset xs)) generalizing σ τ with
  | var x => simp only [Term.subst];exact related x
  | node op _ ih => simpa only [Term.subst] using Iota.node op (ih op 0 σ τ related)
  | nil => intros;simp only [substArgs];exact .nil
  | cons _ _ first rest =>
    rename_i op offset σ τ related
    simp only [substArgs]
    exact .cons (first (lift_related related _)) (rest op (offset+1) σ τ related)

/-- Raw beta/body-family overlap joins by the proved full iota substitution
path, including duplicated/discarded arguments and all binder depths. -/
theorem beta_body_join (step : Iota env body body') (erased : Bool) (domain argument : Term) :
    ∃ common,Forward env (body.subst (single argument)) common ∧
      Forward env (.app (.lam erased domain body') argument) common :=
  ⟨body'.subst (single argument),(step.substitution _).toForward,
    .old (.acu (.compute (.beta erased domain body' argument)))⟩

/-- Raw beta/annotation-family overlap erases exactly the same annotation on
both paths, without asking the annotation to be typed. -/
theorem beta_annotation_join (_step : Iota env domain domain') (erased : Bool) (body argument : Term) :
    ∃ common,Forward env (body.subst (single argument)) common ∧
      Forward env (.app (.lam erased domain' body) argument) common := by
  exact ⟨body.subst (single argument),.refl,.old (.acu (.compute (.beta erased domain' body argument)))⟩

/-- Raw beta/argument-family overlap joins by pointwise iota substitution,
so arbitrary multiplicity in the function body is handled constructively. -/
theorem beta_argument_join (step : Iota env argument argument') (erased : Bool) (domain body : Term) :
    ∃ common,Forward env (body.subst (single argument)) common ∧
      Forward env (.app (.lam erased domain body) argument') common := by
  refine ⟨body.subst (single argument'),?_,.old (.acu (.compute (.beta erased domain body argument')))⟩
  apply Iota.toForward
  apply Iota.subst_congr
  intro x
  cases x with
  | zero => exact step
  | succ x => exact .refl

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
