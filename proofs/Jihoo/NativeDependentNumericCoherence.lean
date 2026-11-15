import Jihoo.NativeDependentLogicalRelation
import Jihoo.NativeNumeralForward
set_option maxUniverseOffset 40

/-! Uniqueness of the mathematical natural represented by the concrete glued
numeric relation, including valid additive trees larger than one word. The
proof uses genuine raw Lend projection, family Church-Rosser and numeric shape
preservation; no arbitrary typed-U64 literal canonicity is assumed. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentRelation
open EnvironmentDelta.NumeralForward

private theorem represented_unique (first : Represents term firstValue) (second : Represents term secondValue) :
    firstValue = secondValue := by
  induction first generalizing secondValue with
  | natural value => cases second; rfl
  | add left right ihleft ihright =>
    cases second with
    | add otherLeft otherRight => rw [ihleft otherLeft,ihright otherRight]

private theorem represented_project (represented : Represents term value) : RawLend.project env term = term := by
  induction represented with
  | natural value =>
    simp only [RawLend.project,Term.natural,EnvironmentDelta.expand,EnvironmentDelta.expandArgs,RawLend.unlend,
      RawLend.unlendArgs,RawLend.rebuild]
  | add left right ihleft ihright =>
    simp only [Term.uadd,RawLend.project_ordinary (op := .uadd) (by rfl),RawLend.rebuild,
      List.map_cons,List.map_nil,ihleft,ihright]

theorem numeralTree_injective (admissible : EnvironmentDelta.Admissible env)
    (converted : RawLend.Conv env (numeralTree first) (numeralTree second)) : first = second := by
  have firstTree : Represents (numeralTree first) first := replicate_ones first
  have secondTree : Represents (numeralTree second) second := replicate_ones second
  have mapped := converted.projected admissible
  rw [represented_project firstTree,represented_project secondTree] at mapped
  obtain ⟨common,left,right⟩ := mapped.church_rosser admissible
  exact represented_unique (family_forward_preserves left firstTree) (family_forward_preserves right secondTree)

theorem natural_value_unique (admissible : EnvironmentDelta.Admissible env)
    (Γ : Contextual.Context) (point : Γ) {firstValue secondValue : Finite.Carrier Finite.natural}
    (first : (natural env Γ).realizes point term firstValue)
    (second : (natural env Γ).realizes point term secondValue) : firstValue = secondValue := by
  cases firstValue
  cases secondValue
  exact congrArg ULift.up (numeralTree_injective admissible (first.symm.trans second))

end Jihoo.NativeKernel.Environment.Semantics.DependentRelation
