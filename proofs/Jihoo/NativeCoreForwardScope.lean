import Jihoo.NativeScopeAlgebra
import Jihoo.NativeACULegacyTransport

/-! Genuine forward computation preserves an explicitly scoped input. Reverse
conversion expansions are deliberately absent: beta expansion can hide arbitrary
unbound arguments, even when the contracted result is closed. -/
namespace Jihoo.NativeKernel.ACU
open Conversion (ListRel)

private theorem binary (nonbinding : ∀ index,op.binders index = 0)
    (first : a.Scoped depth) (second : b.Scoped depth) : (Term.node op [a,b]).Scoped depth := by
  apply Term.Scoped.nonbinding nonbinding
  intro child member
  rcases List.mem_cons.mp member with rfl | member
  · exact first
  · rcases List.mem_cons.mp member with rfl | member
    · exact second
    · cases member

private theorem add_left (scope : (Term.uadd a b).Scoped depth) : a.Scoped depth := by
  simpa only [Op.binders,Nat.add_zero] using scope.child (index := 0) rfl

private theorem add_right (scope : (Term.uadd a b).Scoped depth) : b.Scoped depth := by
  simpa only [Op.binders,Nat.add_zero] using scope.child (index := 1) rfl

private theorem compact_scope (scopes : ∀ term ∈ terms,term.Scoped depth) : (compact terms).Scoped depth := by
  induction terms with
  | nil => exact .leaf _ _
  | cons first rest ih =>
    cases rest with
    | nil => exact scopes first (by simp)
    | cons second rest =>
      exact binary (by intro index; rfl) (scopes first (by simp))
        (ih (fun term member => scopes term (List.mem_cons_of_mem _ member)))

theorem ArithmeticRed.scope (step : ArithmeticRed term result) : ∀ depth,term.Scoped depth → result.Scoped depth := by
  induction step using ArithmeticRed.rec
    (motive_2 := fun first second _ => ListRel (fun first second => ∀ depth,first.Scoped depth → second.Scoped depth) first second) with
  | refl => intro depth scope; exact scope
  | trans _ _ first second => intro depth scope; exact second depth (first depth scope)
  | node op related ih => intro depth scope; exact scope.node_transport ih
  | assocRight a b c =>
    intro depth scope
    exact binary (by intro index; rfl) (add_left (add_left scope))
      (binary (by intro index; rfl) (add_right (add_left scope)) (add_right scope))
  | assocLeft a b c =>
    intro depth scope
    exact binary (by intro index; rfl)
      (binary (by intro index; rfl) (add_left scope) (add_left (add_right scope))) (add_right (add_right scope))
  | comm a b => intro depth scope; exact binary (by intro index; rfl) (add_right scope) (add_left scope)
  | zeroRight a => intro depth scope; exact add_left scope
  | zeroLeft a => intro depth scope; exact add_right scope
  | literalSplit value bound =>
    intro depth scope
    apply compact_scope
    intro term member
    have same := List.eq_of_mem_replicate member
    subst term
    exact .leaf _ _
  | literalAdd => intro depth scope; exact .leaf _ _
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

theorem Computes.scope (step : Computes term result) : ∀ depth,term.Scoped depth → result.Scoped depth := by
  cases step with
  | beta erased domain body argument =>
    intro depth scope
    have function := scope.child (index := 0) rfl
    have bodyScope := function.child (index := 1) rfl
    have argumentScope := scope.child (index := 1) rfl
    exact Term.Scoped.instantiate (by simpa only [Op.binders,Nat.add_zero] using bodyScope)
      (by simpa only [Op.binders,Nat.add_zero] using argumentScope)
  | sub => intro depth scope; exact .leaf _ _
  | read count values index proof value selected =>
    intro depth scope
    have elements := scope.child (index := 0) rfl
    simpa only [Op.binders,Nat.add_zero] using elements.child selected
  | witnessPack predicate value proof =>
    intro depth scope
    have packed := scope.child (index := 0) rfl
    simpa only [Op.binders,Nat.add_zero] using packed.child (index := 1) rfl
  | proofPack predicate value proof =>
    intro depth scope
    have packed := scope.child (index := 0) rfl
    simpa only [Op.binders,Nat.add_zero] using packed.child (index := 2) rfl
  | derefBorrow value =>
    intro depth scope
    have borrowed := scope.child (index := 0) rfl
    simpa only [Op.binders,Nat.add_zero] using borrowed.child (index := 0) rfl
  | borrowDeref value =>
    intro depth scope
    have dereferenced := scope.child (index := 0) rfl
    simpa only [Op.binders,Nat.add_zero] using dereferenced.child (index := 0) rfl
  | transportRefl family value proof =>
    intro depth scope
    simpa only [Op.binders,Nat.add_zero] using scope.child (index := 2) rfl
  | ifLtTrue first second yes no ordered =>
    intro depth scope
    apply Term.Scoped.instantiate (by simpa only [Op.binders] using scope.child (index := 2) rfl)
    exact binary (by intro index; rfl) (.leaf _ _) (.leaf _ _)
  | ifLtFalse => intro depth scope; simpa only [Op.binders,Nat.add_zero] using scope.child (index := 3) rfl
  | ifEqTrue value yes no =>
    intro depth scope
    apply Term.Scoped.instantiate (by simpa only [Op.binders] using scope.child (index := 2) rfl)
    apply Term.Scoped.nonbinding (by intro index; rfl)
    intro term member
    have same := List.mem_singleton.mp member
    subst term
    exact .leaf _ _
  | ifEqFalse => intro depth scope; simpa only [Op.binders,Nat.add_zero] using scope.child (index := 3) rfl

theorem MixedRed.scope (step : MixedRed term result) : ∀ depth,term.Scoped depth → result.Scoped depth := by
  induction step using MixedRed.rec
    (motive_2 := fun first second _ => ListRel (fun first second => ∀ depth,first.Scoped depth → second.Scoped depth) first second) with
  | refl => intro depth scope; exact scope
  | trans _ _ first second => intro depth scope; exact second depth (first depth scope)
  | node op related ih => intro depth scope; exact scope.node_transport ih
  | arithmetic step => exact step.scope
  | compute step => exact step.scope
  | nil => exact .nil
  | cons first rest ihfirst ihrest => exact .cons ihfirst ihrest

end Jihoo.NativeKernel.ACU
