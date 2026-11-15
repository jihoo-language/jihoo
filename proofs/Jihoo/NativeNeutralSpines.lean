import Jihoo.NativeEnvironmentWellFormed
import Jihoo.NativeNeutralSpineSyntax
import Jihoo.NativeFamilyIotaNeutralCoherence

/-! Authentic conversion of neutral higher-kinded family applications.
The argument list is stored from the last argument towards the head. These
facts permit arbitrary argument terms and use quotient confluence, rather
than assuming typing, normalization or preservation of parallel reduction. -/
namespace Jihoo.NativeKernel


namespace ACU
open Conversion (ListRel)

private theorem arithmetic_variable_node (rigid : arithmeticRigid op = true) :
    ¬ Arithmetic (.var head) (.node op children) := by
  intro converted
  have flat : arithmeticFlatten (.node op children) = [.node op children] := by
    cases op <;> simp_all only [arithmeticRigid,Bool.false_eq_true,arithmeticFlatten]
  have model := converted.model
  unfold ArithmeticModel at model
  simp only [arithmeticFlatten,flat] at model
  have atom := model.singleton ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
  cases atom

private theorem arithmetic_spine_node (notApplication : op ≠ .app) (rigid : arithmeticRigid op = true) :
    ¬ Arithmetic (neutralSpine head arguments) (.node op children) := by
  cases arguments with
  | nil => exact arithmetic_variable_node rigid
  | cons argument rest =>
    intro converted
    exact notApplication (converted.head_fields rfl rigid).1.symm

private theorem arithmetic_spine_injective
    (converted : Arithmetic (neutralSpine head arguments) (neutralSpine other replacements)) :
    head = other ∧ ListRel Arithmetic arguments replacements := by
  induction arguments generalizing replacements with
  | nil =>
    cases replacements with
    | nil => exact ⟨converted.variable_injective,.nil⟩
    | cons argument rest => exact False.elim (arithmetic_variable_node (op := .app) rfl converted)
  | cons argument rest ih =>
    cases replacements with
    | nil => exact False.elim (arithmetic_variable_node (op := .app) rfl converted.symm)
    | cons replacement tail =>
      obtain ⟨_,children⟩ := converted.head_fields rfl rfl
      cases children with
      | cons function tailChildren =>
        cases tailChildren with
        | cons value remaining =>
          obtain ⟨same,arguments⟩ := ih function
          exact ⟨same,.cons value arguments⟩

/-- A neutral application has no beta root, even modulo arbitrary arithmetic
changes to its function and its arguments. -/
theorem QPar.neutralSpine_view (step : QPar (neutralSpine head arguments) result) :
    ∃ replacements, Arithmetic result (neutralSpine head replacements) ∧ ListRel QPar arguments replacements := by
  induction arguments generalizing result with
  | nil =>
    obtain ⟨atom,reduced,converted⟩ := step.atom_view (by simp only [neutralSpine,arithmeticFlatten])
    cases reduced
    exact ⟨[],converted,.nil⟩
  | cons argument rest ih =>
    obtain ⟨atom,reduced,converted⟩ := step.atom_view (by simp only [neutralSpine,Term.app,arithmeticFlatten])
    cases reduced with
    | node op children =>
      cases children with
      | cons function tailChildren =>
        cases tailChildren with
        | cons value remaining =>
          cases remaining
          obtain ⟨replacements,view,functions⟩ := ih function
          exact ⟨_ :: replacements,converted.trans (.node .app (.cons view (.cons (.refl _) .nil))),.cons value functions⟩
    | beta erased domain body view bodyStep argumentStep =>
      exact False.elim (arithmetic_spine_node (by intro same; cases same) rfl view)

private theorem prepend_parallel (first : ListRel QPar arguments middle) (rest : ListRel QStar middle replacements) :
    ListRel QStar arguments replacements := by
  induction first generalizing replacements with
  | nil => cases rest; exact .nil
  | cons first tail ih => cases rest with | cons next remaining => exact .cons (.cons first next) (ih remaining)

private theorem reflexive_stars (arguments : List Term) : ListRel QStar arguments arguments := by
  induction arguments with
  | nil => exact .nil
  | cons argument rest ih => exact .cons .refl ih

theorem QStar.neutralSpine_shape (steps : QStar term result) (view : Arithmetic term (neutralSpine head arguments)) :
    ∃ replacements, Arithmetic result (neutralSpine head replacements) ∧ ListRel QStar arguments replacements := by
  induction steps generalizing arguments with
  | refl => exact ⟨arguments,view,reflexive_stars arguments⟩
  | cons first rest ih =>
    obtain ⟨middle,next,argumentsSteps⟩ := (first.input view).neutralSpine_view
    obtain ⟨replacements,last,remaining⟩ := ih next
    exact ⟨replacements,last,prepend_parallel argumentsSteps remaining⟩

private theorem join_arguments (first : ListRel QStar arguments middle) (same : ListRel Arithmetic middle shared)
    (second : ListRel QStar replacements shared) : ListRel Conv arguments replacements := by
  induction first generalizing shared replacements with
  | nil => cases same; cases second; exact .nil
  | cons first tail ih => cases same with | cons same remaining => cases second with
    | cons second rest => exact .cons (first.toConv.trans (same.toConv.trans second.toConv.symm)) (ih remaining rest)

/-- Free-head applications are injective at every finite arity under the full
conversion relation. Every source argument retains its actual conversion. -/
theorem Conv.neutralSpine_injective
    (converted : Conv (neutralSpine head arguments) (neutralSpine other replacements)) :
    head = other ∧ ListRel Conv arguments replacements := by
  obtain ⟨common,first,second⟩ := converted.church_rosser_modulo_arithmetic
  obtain ⟨middle,firstView,firstArguments⟩ := first.neutralSpine_shape (.refl _)
  obtain ⟨shared,secondView,secondArguments⟩ := second.neutralSpine_shape (.refl _)
  obtain ⟨same,argumentEquivalences⟩ := arithmetic_spine_injective (firstView.symm.trans secondView)
  exact ⟨same,join_arguments firstArguments argumentEquivalences secondArguments⟩

theorem Conv.neutralSpine_node_separate (notApplication : op ≠ .app) (rigid : fullRigid op = true) :
    ¬ Conv (neutralSpine head arguments) (.node op children) := by
  intro converted
  obtain ⟨common,first,second⟩ := converted.church_rosser_modulo_arithmetic
  obtain ⟨middle,firstView,_⟩ := first.neutralSpine_shape (.refl _)
  obtain ⟨shared,secondView,_⟩ := second.rigid_shape rigid (.refl _)
  exact arithmetic_spine_node notApplication (Bool.and_eq_true_iff.mp rigid).2 (firstView.symm.trans secondView)

end ACU
end Jihoo.NativeKernel

namespace Jihoo.NativeKernel.EnvironmentDelta

theorem expand_neutralSpine (env : Environment) (head : Nat) (arguments : List Term) :
    expand env (neutralSpine head arguments) = neutralSpine head (arguments.map (expand env)) := by
  induction arguments with
  | nil => simp only [neutralSpine,expand,List.map_nil]
  | cons argument rest ih => simp only [neutralSpine,Term.app,expand,expandArgs,List.map_cons,ih]

end Jihoo.NativeKernel.EnvironmentDelta

namespace Jihoo.NativeKernel.EnvironmentDelta.Basis
open NativeKernel.Conversion (ListRel)

private theorem arguments_of_projected
    (arguments : ListRel ACU.Conv (source.map (expand env)) (target.map (expand env))) :
    ListRel (Conv env) source target := by
  induction source generalizing target with
  | nil => cases target with
    | nil => exact .nil
    | cons => cases arguments
  | cons first rest ih => cases target with
    | nil => cases arguments
    | cons other tail => cases arguments with
      | cons head remaining => exact .cons (.ofProjected head) (ih remaining)

/-- Authenticated delta does not identify different open family heads, change
application arity, or discard any argument conversion. This includes globals
and arbitrary native computations inside every family argument. -/
theorem Conv.neutralSpine_injective (admissible : Admissible env)
    (converted : Conv env (neutralSpine head arguments) (neutralSpine other replacements)) :
    head = other ∧ ListRel (Conv env) arguments replacements := by
  have projected := converted.toProjected admissible
  simp only [EnvironmentDelta.Conv,expand_neutralSpine] at projected
  obtain ⟨same,children⟩ := projected.neutralSpine_injective
  exact ⟨same,arguments_of_projected children⟩

theorem Conv.neutralSpine_node_separate (admissible : Admissible env)
    (ordinary : GlobalEnvironment.ordinary op = true)
    (notApplication : op ≠ .app) (rigid : ACU.fullRigid op = true) :
    ¬ Conv env (neutralSpine head arguments) (.node op children) := by
  intro converted
  have projected := converted.toProjected admissible
  simp only [EnvironmentDelta.Conv,expand_neutralSpine,expand_ordinary ordinary] at projected
  exact ACU.Conv.neutralSpine_node_separate notApplication rigid projected

theorem Conv.family_application_injective (admissible : Admissible env)
    (converted : Conv env (.app (.var head) argument) (.app (.var other) replacement)) :
    head = other ∧ Conv env argument replacement := by
  obtain ⟨same,children⟩ := Conv.neutralSpine_injective (arguments := [argument])
    (replacements := [replacement]) admissible converted
  cases children with
  | cons argument remaining => exact ⟨same,argument⟩

end Jihoo.NativeKernel.EnvironmentDelta.Basis
