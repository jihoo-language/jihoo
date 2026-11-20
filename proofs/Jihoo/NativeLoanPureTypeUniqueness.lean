import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanPureTypingChecker
import Jihoo.NativeLoanTypeUniqueness

/-! Ghost inference remains functional with RawValue conversion. Native
leaves use the full Loan64 uniqueness theorem. The three structural rules
compare the original binders and application arguments of both derivations. -/
namespace Jihoo.NativeKernel.Environment.RawValue

open Semantics.ValueErasure.Loan (project project_ordinary_node)

private theorem project_sort (env : Environment) (sort : SortTag) :
    project env sort.term = sort.term := by
  cases sort with
  | prop => exact project_ordinary_node (op := .prop) rfl (by intro same; cases same) []
  | type level =>
      exact project_ordinary_node (op := .universe level) rfl (by intro same; cases same) []

theorem Conv.sort_injective {first second : SortTag} (converted : Conv env first.term second.term)
    (admissible : EnvironmentDelta.Admissible env) : first = second := by
  have projected := converted.projected admissible
  rw [project_sort, project_sort] at projected
  exact projected.sort_injective admissible

end Jihoo.NativeKernel.Environment.RawValue

namespace Jihoo.NativeKernel.Environment.LoanTyping.PureTyping

/-- A typed Pi exposes the original domain formation and a typed codomain
under that same domain. Both determine the principal sort before conversion. -/
theorem pi_replay (typed : HasType env ctx expression type) :
    ∀ erased domain codomain, expression = .pi erased domain codomain →
      ∃ domainSort resultSort : SortTag,
        LoanTyping.HasType env [] ctx true domain domainSort.term ∧
        HasType env (⟨domain, erased⟩ :: ctx) codomain resultSort.term ∧
        RawValue.Conv env (domainSort.pi resultSort).term type := by
  induction typed with
  | native original =>
      intro erased domain codomain shape
      cases shape
      obtain ⟨domainSort, resultSort, domainTyped, bodyTyped, converted⟩ := original.principalView
      exact ⟨domainSort, resultSort, domainTyped, .native bodyTyped, .old converted⟩
  | convert _ _ converted ih =>
      intro erased domain codomain shape
      obtain ⟨domainSort, resultSort, domainTyped, bodyTyped, prior⟩ := ih erased domain codomain shape
      exact ⟨domainSort, resultSort, domainTyped, bodyTyped, prior.trans converted⟩
  | pi binder bodyTyped _ =>
      intro erased domain codomain shape
      cases shape
      cases binder with
      | intro formed _ => exact ⟨_, _, formed, bodyTyped, .refl _⟩
  | lam _ _ _ _ => intro erased domain codomain shape; cases shape
  | app _ _ _ _ => intro erased domain codomain shape; cases shape

private theorem native_unique (wellFormed : UnifiedProgram.EnvWellFormed env)
    (extended : HasType env ctx term second)
    (original : LoanTyping.HasType env [] ctx true term first) :
    RawValue.Conv env first second := by
  induction extended generalizing first with
  | native checked => exact .old (original.unique wellFormed checked)
  | convert _ _ converted ih => exact (ih original).trans converted
  | pi binder _ ih =>
      obtain ⟨_, _, originalDomain, originalBody, converted⟩ := original.principalView
      cases binder with
      | intro domainTyped _ =>
          have sameDomain := originalDomain.sort_unique wellFormed domainTyped
          have sameResult := (ih originalBody).sort_injective wellFormed.admissible
          rw [sameDomain, sameResult] at converted
          exact .old converted.symm
  | lam _ _ _ ih =>
      obtain ⟨_, _, _, bodyTyped, converted⟩ := original.lamView
      exact (RawValue.Conv.old converted).symm.trans
        (.node _ (.cons (.refl _) (.cons (ih bodyTyped) .nil)))
  | app _ _ _ ih =>
      obtain ⟨_, _, _, functionTyped, _, _, converted⟩ := original.appView
      have codomains := ((ih functionTyped).pi_injective wellFormed.admissible).2.2
      exact (RawValue.Conv.old converted).symm.trans
        (codomains.substitution (single _) wellFormed.admissible)

/-- Any two derivations of the same ghost expression in the same context
have convertible types under the full extended conversion. -/
theorem HasType.unique (left : HasType env ctx term first)
    (wellFormed : UnifiedProgram.EnvWellFormed env) (right : HasType env ctx term second) :
    RawValue.Conv env first second := by
  induction left generalizing second with
  | native original => exact native_unique wellFormed right original
  | convert _ _ converted ih => exact converted.symm.trans (ih right)
  | pi binder _ ih =>
      obtain ⟨_, _, rightDomain, rightBody, converted⟩ := pi_replay right _ _ _ rfl
      cases binder with
      | intro leftDomain _ =>
          have sameDomain := leftDomain.sort_unique wellFormed rightDomain
          have sameResult := (ih rightBody).sort_injective wellFormed.admissible
          rw [sameDomain, sameResult]
          exact converted
  | lam _ _ _ ih =>
      obtain ⟨_, rightBody, converted⟩ := lambda_replay right _ _ _ rfl
      exact (RawValue.Conv.node _ (.cons (.refl _) (.cons (ih rightBody) .nil))).trans converted
  | app _ _ _ ih =>
      obtain ⟨_, _, _, rightFunction, _, converted⟩ := application_replay right _ _ rfl
      have codomains := ((ih rightFunction).pi_injective wellFormed.admissible).2.2
      exact (codomains.substitution (single _) wellFormed.admissible).trans converted

theorem HasType.sort_unique {first second : SortTag} (left : HasType env ctx term first.term)
    (wellFormed : UnifiedProgram.EnvWellFormed env) (right : HasType env ctx term second.term) :
    first = second := (left.unique wellFormed right).sort_injective wellFormed.admissible

/-- Compare an executable check's exact annotation with any independently
derived type, including structural typing used by mixed declaration replay. -/
theorem Checker.check?_type_unique (wellFormed : UnifiedProgram.EnvWellFormed env)
    (checked : check? env typingFuel conversionFuel budget ctx term requested = some sort)
    (other : HasType env ctx term type) : RawValue.Conv env requested type :=
  (check?_sound checked).2.unique wellFormed other

end Jihoo.NativeKernel.Environment.LoanTyping.PureTyping
