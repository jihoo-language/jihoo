import Jihoo.NativeClosingResourceSemantics

/-! Semantic classification of every genuinely typed proposition or Type0
runtime domain. Its representation may be neutral, computed, or aliased. -/
namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}
variable {sort : SortTag}

/-- First-order kinds themselves always inhabit a positive universe. This uses
principal inversion and the actual predicative Pi universe rule. -/
theorem Kind.sort_positive (kind : Kind)
    (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx ghost kind.term sort.term) :
    ∃ level, sort = .type (level + 1) := by
  induction kind generalizing ctx ghost sort with
  | type level =>
      cases sort with
      | prop => exact False.elim (HasType.universe_not_proposition wellFormed typed)
      | type actual => exact ⟨level,congrArg SortTag.type (typed.universe_successor wellFormed)⟩
  | index erased result ih =>
      obtain ⟨domainSort,resultSort,domainTyped,resultTyped,converted⟩ := typed.principalView
      obtain ⟨level,same⟩ := ih resultTyped
      subst resultSort
      have aligned := converted.sort_injective wellFormed.admissible
      subst sort
      cases domainSort with
      | prop => exact ⟨level,rfl⟩
      | type domainLevel =>
          refine ⟨max domainLevel (level + 1) - 1,?_⟩
          simp only [SortTag.pi,SortTag.type.injEq]
          omega

/-- Converted arbitrary domains retain genuine source typing by actual forward
common reduction and authenticated declaration history. Symmetric conversion
is never treated as a typing-preservation theorem. -/
theorem small_sort_not_kind
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx ghost domain sort.term)
    (small : sort = .prop ∨ sort = .type 0) :
    ∀ kind : Kind, ¬ Conversion.Conv env domain kind.term := by
  intro kind converted
  obtain ⟨common,domainForward,kindForward⟩ := converted.church_rosser history.wellFormed.admissible
  have fixed := kind.forward_fixed kindForward
  subst common
  have kindTyped := typed.ghostFamilyForward history domainForward
  obtain ⟨level,positive⟩ := kind.sort_positive history.wellFormed kindTyped
  rcases small with rfl | rfl <;> cases positive

theorem DomainClassified.of_small_sort
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx ghost domain sort.term)
    (small : sort = .prop ∨ sort = .type 0) : DomainClassified env domain :=
  Or.inr (small_sort_not_kind history typed small)

theorem DomainClassified.of_type0
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx ghost domain (.univ 0)) : DomainClassified env domain :=
  DomainClassified.of_small_sort history (sort := .type 0) typed (Or.inr rfl)

theorem DomainClassified.of_prop
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env ctx ghost domain .prop) : DomainClassified env domain :=
  DomainClassified.of_small_sort history (sort := .prop) typed (Or.inl rfl)

end Jihoo.NativeKernel.Environment.CodeKinds

namespace Jihoo.NativeKernel.Environment.CodeKinds
variable {definitions : List GlobalDeclaration} {familyDeclarations : List FamilyDeclaration}

theorem Kind.not_u64 (kind : Kind) (admissible : EnvironmentDelta.Admissible env) :
    ¬ Conversion.Conv env kind.term .u64 := by
  intro converted
  cases kind with
  | type level =>
      exact FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible
  | index erased result =>
      exact FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible

theorem Kind.not_family (kind : Kind) (admissible : EnvironmentDelta.Admissible env) :
    ¬ Conversion.Conv env kind.term (.node (.ind family count) indices) := by
  intro converted
  cases kind with
  | type level =>
      exact FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible
  | index erased result =>
      exact FamilyIota.Extended.Conv.full_rigid_disjoint rfl rfl
        (by intro same; cases same) converted admissible

/-- Authentic first-order kind parameters are runtime binders. This follows
from actual binder formation and policy, including the erased-data arm. -/
theorem binder_kind_runtime
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (binding : Binder env ctx erased domain sort)
    {kind : Kind} (converted : Conversion.Conv env domain kind.term) : erased = false := by
  cases erased with
  | false => rfl
  | true =>
      cases binding with
      | intro typed allowed =>
          obtain ⟨common,domainForward,kindForward⟩ := converted.church_rosser history.wellFormed.admissible
          have fixed := kind.forward_fixed kindForward
          subst common
          have kindTyped := typed.ghostFamilyForward history domainForward
          obtain ⟨level,positive⟩ := kind.sort_positive history.wellFormed kindTyped
          rcases allowed with pure | data
          · simp only [pureBinderAllowed,↓reduceIte] at pure
            rcases pure with prop | u64
            · cases positive.symm.trans prop
            · exact False.elim (kind.not_u64 history.wellFormed.admissible (converted.symm.trans u64))
          · obtain ⟨_,family,count,indices,entry,selected,isData,familyConverted⟩ := data
            exact False.elim (kind.not_family history.wellFormed.admissible
              (converted.symm.trans familyConverted))

end Jihoo.NativeKernel.Environment.CodeKinds
