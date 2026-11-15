import Jihoo.NativeFamilyIotaNeutralSpines

/-! Arbitrary higher-kinded neutral applications have unique heads, arities
and argument conversion classes in the genuine enlarged relation. These APIs
retain the fixed-basis calling convention for actual-source model migration. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended
open NativeKernel.Conversion (ListRel)

private theorem spine_syntax_injective
    (same : neutralSpine head arguments = neutralSpine other replacements) : head = other ∧ arguments = replacements := by
  induction arguments generalizing replacements with
  | nil => cases replacements with
    | nil => exact ⟨Term.var.inj same,rfl⟩
    | cons => cases same
  | cons argument rest ih => cases replacements with
    | nil => cases same
    | cons replacement tail =>
      have children := (Term.node.inj same).2
      have functions := (List.cons.inj children).1
      have values := (List.cons.inj (List.cons.inj children).2).1
      obtain ⟨heads,arguments⟩ := ih functions
      cases values
      cases arguments
      exact ⟨heads,rfl⟩

private theorem joined_arguments (left : ListRel (Forward env) arguments common)
    (right : ListRel (Forward env) replacements common) : ListRel (Conv env) arguments replacements := by
  induction left generalizing replacements with
  | nil => cases right;exact .nil
  | cons first rest ih => cases right with
    | cons other tail => exact .cons (Conv.ofForwardJoin first other) (ih tail)

theorem Conv.neutralSpine_injective (admissible : EnvironmentDelta.Admissible env)
    (converted : Conv env (neutralSpine head arguments) (neutralSpine other replacements)) :
    head = other ∧ ListRel (Conv env) arguments replacements := by
  obtain ⟨common,left,right⟩ := converted.church_rosser admissible
  obtain ⟨middle,leftShape,leftArguments⟩ := left.neutralSpine_shape head arguments rfl
  obtain ⟨shared,rightShape,rightArguments⟩ := right.neutralSpine_shape other replacements rfl
  obtain ⟨heads,same⟩ := spine_syntax_injective (leftShape.symm.trans rightShape)
  subst shared
  exact ⟨heads,joined_arguments leftArguments rightArguments⟩

theorem Conv.neutralSpine_node_separate (admissible : EnvironmentDelta.Admissible env)
    (_ordinary : GlobalEnvironment.ordinary op = true) (notApplication : op ≠ .app) (headRigid : rigid op = true) :
    ¬ Conv env (neutralSpine head arguments) (.node op children) := by
  intro converted
  obtain ⟨common,left,right⟩ := converted.church_rosser admissible
  obtain ⟨arguments',leftShape,_⟩ := left.neutralSpine_shape head arguments rfl
  obtain ⟨children',rightShape,_⟩ := right.rigid_shape headRigid rfl
  have same := leftShape.symm.trans rightShape
  cases arguments' with
  | nil => cases same
  | cons argument rest => exact notApplication (Term.node.inj same).1.symm

theorem Conv.family_application_injective (admissible : EnvironmentDelta.Admissible env)
    (converted : Conv env (.app (.var head) argument) (.app (.var other) replacement)) :
    head = other ∧ Conv env argument replacement := by
  obtain ⟨same,children⟩ := Conv.neutralSpine_injective (arguments := [argument])
    (replacements := [replacement]) admissible converted
  cases children with
  | cons argument remaining => exact ⟨same,argument⟩

end Jihoo.NativeKernel.Environment.FamilyIota.Extended
