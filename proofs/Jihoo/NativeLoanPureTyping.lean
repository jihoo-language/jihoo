import Jihoo.NativeLoanPureConversion
import Jihoo.NativeLoanPureFreeBoundary
import Jihoo.NativeLoanSubstitution

/-! Ghost typing with RawValue conversion and independently formed target
annotations. Loan64 supplies the leaves, binder policy, and the argument
typing used to substitute into dependent codomains. These constructors do not
change Loan64 admission or the runtime and resource judgments. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.PureTyping

open Semantics.ValueErasure.Loan (project)

/-- Conversion checks its requested type using the original Loan64 judgment.
The structural rules can compose extended derivations without treating their
terms as raw Loan64 substitutions. -/
inductive HasType (env : Environment) : Context → Term → Term → Prop where
  | native : LoanTyping.HasType env [] ctx true term type → HasType env ctx term type
  | convert {sort : SortTag} : HasType env ctx term original → LoanTyping.HasType env [] ctx true requested sort.term →
      RawValue.Conv env original requested → HasType env ctx term requested
  | pi {resultSort : SortTag} : LoanTyping.Binder env [] ctx erased domain domainSort →
      HasType env (⟨domain, erased⟩ :: ctx) codomain resultSort.term →
      HasType env ctx (.pi erased domain codomain) (domainSort.pi resultSort).term
  | lam {resultSort : SortTag} : LoanTyping.Binder env [] ctx erased domain domainSort →
      LoanTyping.HasType env [] (⟨domain, erased⟩ :: ctx) true codomain resultSort.term →
      HasType env (⟨domain, erased⟩ :: ctx) body codomain →
      HasType env ctx (.lam erased domain body) (.pi erased domain codomain)
  | app {resultSort : SortTag} : HasType env ctx function (.pi erased domain codomain) →
      LoanTyping.HasType env [] (⟨domain, erased⟩ :: ctx) true codomain resultSort.term →
      LoanTyping.HasType env [] ctx true argument domain →
      HasType env ctx (.app function argument) (codomain.subst (single argument))

theorem convert_native {sort : SortTag} (typed : LoanTyping.HasType env loans ctx mode term original)
    (formed : LoanTyping.HasType env formationLoans ctx true requested sort.term)
    (converted : RawValue.Conv env original requested) : HasType env ctx term requested :=
  .convert (.native (typed.ghost [])) (formed.ghost []) converted

/-- Projection supplies the same conversion used by the typed rule, with
raw source typing and independent formation still required. -/
theorem convert_projected {sort : SortTag} (typed : HasType env ctx term original)
    (formed : LoanTyping.HasType env [] ctx true requested sort.term)
    (converted : FamilyIota.Extended.Conv env (project env original) (project env requested)) :
    HasType env ctx term requested :=
  .convert typed formed (RawValue.Conv.ofProjected converted)

theorem application_result_formed {sort : SortTag} (wellFormed : UnifiedProgram.EnvWellFormed env)
    (formed : LoanTyping.HasType env [] (⟨domain, erased⟩ :: ctx) true codomain sort.term)
    (typed : LoanTyping.HasType env [] ctx true argument domain) :
    LoanTyping.HasType env [] ctx true (codomain.subst (single argument)) sort.term := by
  simpa only [SortTag.subst_term] using formed.ghostInstantiate wellFormed typed

private theorem subst_pi (values : Nat → Term) :
    (Term.pi erased domain codomain).subst values =
      .pi erased (domain.subst values) (codomain.subst (liftSubOne values)) := by
  simp only [Term.pi, Term.subst, substArgs, Op.binders, liftSub]

private theorem subst_lam (values : Nat → Term) :
    (Term.lam erased domain body).subst values =
      .lam erased (domain.subst values) (body.subst (liftSubOne values)) := by
  simp only [Term.lam, Term.subst, substArgs, Op.binders, liftSub]

private theorem subst_app (values : Nat → Term) :
    (Term.app function argument).subst values = .app (function.subst values) (argument.subst values) := by
  simp only [Term.app, Term.subst, substArgs, Op.binders, liftSub]

/-- Substitution uses actual Loan64-typed replacements under every binder.
The RawValue equations are stable under the very same substitution. -/
theorem HasType.ghostSubstitution (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx term type) (replacements : Ghost.Substitution env ctx target values) :
    HasType env target (term.subst values) (type.subst values) := by
  induction typed generalizing target values with
  | native typed => exact .native (typed.ghostSubstitution wellFormed replacements)
  | convert _ formed converted ih =>
    exact .convert (ih replacements)
      (by simpa only [SortTag.subst_term] using formed.ghostSubstitution wellFormed replacements)
      (converted.substitution values wellFormed.admissible)
  | pi binder _ ih =>
    rw [subst_pi, SortTag.subst_term]
    exact .pi (binder.ghostSubstitution wellFormed replacements)
      (by simpa only [SortTag.subst_term] using ih (replacements.lift wellFormed _ _))
  | @lam ctx erased domain domainSort codomain body resultSort binder formed _ ih =>
    rw [subst_lam, subst_pi]
    have lifted := replacements.lift wellFormed domain erased
    exact .lam (binder.ghostSubstitution wellFormed replacements)
      (by simpa only [SortTag.subst_term] using formed.ghostSubstitution wellFormed lifted)
      (ih lifted)
  | app _ formed argumentTyped ih =>
    rw [subst_app, Term.subst_instantiate]
    exact .app (by simpa only [subst_pi] using ih replacements)
      (by simpa only [SortTag.subst_term] using formed.ghostSubstitution wellFormed (replacements.lift wellFormed _ _))
      (argumentTyped.ghostSubstitution wellFormed replacements)

theorem HasType.ghostInstantiate (wellFormed : UnifiedProgram.EnvWellFormed env)
    (body : HasType env (⟨domain, erased⟩ :: ctx) source codomain)
    (argument : LoanTyping.HasType env [] ctx true value domain) :
    HasType env ctx (source.subst (single value)) (codomain.subst (single value)) :=
  body.ghostSubstitution wellFormed (Ghost.Substitution.single erased argument)

private theorem lambda_replay (typed : HasType env ctx expression type) :
    ∀ erased domain body, expression = .lam erased domain body →
      ∃ result, HasType env (⟨domain, erased⟩ :: ctx) body result ∧
        RawValue.Conv env (.pi erased domain result) type := by
  induction typed with
  | native original =>
    intro erased domain body shape
    cases shape
    obtain ⟨_, result, _, bodyTyped, converted⟩ := original.lamView
    exact ⟨result, .native bodyTyped, .old converted⟩
  | convert _ _ converted ih =>
    intro erased domain body shape
    obtain ⟨result, bodyTyped, original⟩ := ih erased domain body shape
    exact ⟨result, bodyTyped, original.trans converted⟩
  | lam _ _ bodyTyped _ =>
    intro erased domain body shape
    cases shape
    exact ⟨_, bodyTyped, .refl _⟩
  | pi _ _ _ => intro erased domain body shape; cases shape
  | app _ _ _ _ => intro erased domain body shape; cases shape

/-- Beta uses the original binder and a raw Loan64-typed argument. RawValue
Pi injectivity transports the instantiated body to the independently formed
codomain of the application. -/
theorem ghost_beta {sort : SortTag} (wellFormed : UnifiedProgram.EnvWellFormed env)
    (functionTyped : HasType env ctx (.lam erased domain body) (.pi erased domain codomain))
    (formed : LoanTyping.HasType env [] (⟨domain, erased⟩ :: ctx) true codomain sort.term)
    (argumentTyped : LoanTyping.HasType env [] ctx true argument domain) :
    HasType env ctx (body.subst (single argument)) (codomain.subst (single argument)) := by
  obtain ⟨_, bodyTyped, converted⟩ := lambda_replay functionTyped erased domain body rfl
  have aligned := (converted.pi_injective wellFormed.admissible).2.2
  exact .convert (bodyTyped.ghostInstantiate wellFormed argumentTyped)
    (application_result_formed wellFormed formed argumentTyped)
    (aligned.substitution (single argument) wellFormed.admissible)

theorem instantiate_conversion (admissible : EnvironmentDelta.Admissible env)
    (codomains : RawValue.Conv env original requested) (arguments : RawValue.Conv env first second) :
    RawValue.Conv env (original.subst (single first)) (requested.subst (single second)) := by
  apply (codomains.substitution (single first) admissible).trans
  apply RawValue.Conv.subst_congr admissible
  intro index
  cases index with
  | zero => exact arguments
  | succ index => exact .refl _

private theorem project_single (env : Environment) (argument : Term) :
    (fun index => project env (single argument index)) = single (project env argument) := by
  funext index
  cases index with
  | zero => rfl
  | succ index => exact Semantics.ValueErasure.Loan.project_variable env index

theorem projected_instantiation (admissible : EnvironmentDelta.Admissible env)
    (codomains : RawValue.Conv env original requested) (arguments : RawValue.Conv env first second) :
    FamilyIota.Extended.Conv env
      ((project env original).subst (single (project env first)))
      ((project env requested).subst (single (project env second))) := by
  simpa only [Semantics.ValueErasure.Loan.project_substitution admissible, project_single] using
    (instantiate_conversion admissible codomains arguments).projected admissible

/-- The application keeps its exact source argument. The alternate argument
forms the requested instantiated annotation, and projection certifies that
the two dependent results agree. -/
theorem application_with_coherent_argument {originalSort requestedSort : SortTag}
    (wellFormed : UnifiedProgram.EnvWellFormed env)
    (functionTyped : HasType env ctx function (.pi erased domain original))
    (originalFormed : LoanTyping.HasType env [] (⟨domain, erased⟩ :: ctx) true original originalSort.term)
    (requestedFormed : LoanTyping.HasType env [] (⟨domain, erased⟩ :: ctx) true requested requestedSort.term)
    (sourceArgument : LoanTyping.HasType env [] ctx true first domain)
    (alternateArgument : LoanTyping.HasType env [] ctx true second domain)
    (codomains : RawValue.Conv env original requested) (arguments : RawValue.Conv env first second) :
    HasType env ctx (.app function first) (requested.subst (single second)) ∧
    FamilyIota.Extended.Conv env
      ((project env original).subst (single (project env first)))
      ((project env requested).subst (single (project env second))) := by
  exact ⟨.convert (.app functionTyped originalFormed sourceArgument)
      (application_result_formed wellFormed requestedFormed alternateArgument)
      (instantiate_conversion wellFormed.admissible codomains arguments),
    projected_instantiation wellFormed.admissible codomains arguments⟩

open PureFreeBoundary (owner annotation body)

private def naturalBinder : Binding := ⟨.u64, false⟩
private def freeCodomain : Term := .eq (.free owner (.var 0)) (.var 0)
private def reflexiveCodomain : Term := .eq (.var 0) (.var 0)

private theorem binderTyped : LoanTyping.Binder empty [] [] false .u64 (.type 0) :=
  .intro .u64 (Or.inl (by simp [pureBinderAllowed]))

private theorem ownerTyped (ctx : Context) :
    LoanTyping.HasType empty [] ctx true owner (.buffer (.natural 1)) := by
  exact .alloc (.natural (by decide)) (.integer (by decide) (by decide))

private theorem indexTyped : LoanTyping.HasType empty [] [naturalBinder] true (.var 0) .u64 :=
  .var (b := ⟨.u64, false⟩) (by simp [naturalBinder, lookup, Term.u64, Term.rename, renameArgs]) (Or.inl rfl)

private theorem freeCodomainFormed : LoanTyping.HasType empty [] [naturalBinder] true freeCodomain .prop :=
  .eq (.free (ownerTyped _) indexTyped) indexTyped

private theorem reflexiveCodomainFormed :
    LoanTyping.HasType empty [] [naturalBinder] true reflexiveCodomain .prop :=
  .eq indexTyped indexTyped

private theorem freeCodomainConversion : RawValue.Conv empty freeCodomain reflexiveCodomain :=
  (RawValue.free_eq_forward owner (.var 0) (.var 0)).toConv

/-- Admit the exact Free/Pi annotation that the earlier raw Loan64 boundary
separates from reflexivity. Both its binder and codomain are independently
formed by Loan64. The pure conversion occurs inside the dependent binder. -/
theorem free_equality_function : HasType empty [] body annotation :=
  .lam (resultSort := .prop) binderTyped freeCodomainFormed
    (convert_native (sort := .prop) (mode := true) (.refl indexTyped) freeCodomainFormed freeCodomainConversion.symm)

theorem free_equality_function_formation : HasType empty [] annotation .prop :=
  .pi (resultSort := .prop) binderTyped (.native freeCodomainFormed)

/-- The exact dependent application contains a Free in its argument. Both
the codomain's binder occurrence and the argument are compared using the
pure conversion, while the requested equality is formed in raw Loan64. -/
theorem dependent_free_application :
    HasType empty [] (.app body (.free owner (.natural 0))) (.eq (.natural 0) (.natural 0)) := by
  have alternate : LoanTyping.HasType empty [] [] true (.natural 0) .u64 := .natural (by decide)
  have original : LoanTyping.HasType empty [] [] true (.free owner (.natural 0)) .u64 :=
    .free (ownerTyped _) alternate
  simpa only [reflexiveCodomain, Term.eq, Term.subst, substArgs, Op.binders, liftSub, single] using
    (application_with_coherent_argument (originalSort := .prop) (requestedSort := .prop)
    UnifiedProgram.EnvWellFormed.empty
    free_equality_function freeCodomainFormed reflexiveCodomainFormed original alternate
    freeCodomainConversion (.free owner (.natural 0))).1

theorem dependent_free_application_beta :
    HasType empty [] (.refl (.free owner (.natural 0))) (.eq (.natural 0) (.natural 0)) := by
  have alternate : LoanTyping.HasType empty [] [] true (.natural 0) .u64 := .natural (by decide)
  have original : LoanTyping.HasType empty [] [] true (.free owner (.natural 0)) .u64 :=
    .free (ownerTyped _) alternate
  have stepped := ghost_beta (sort := .prop) UnifiedProgram.EnvWellFormed.empty
    free_equality_function freeCodomainFormed original
  have aligned := instantiate_conversion UnifiedProgram.EnvWellFormed.empty.admissible
    freeCodomainConversion (.free owner (.natural 0))
  have checked := HasType.convert (sort := .prop) stepped
    (application_result_formed UnifiedProgram.EnvWellFormed.empty reflexiveCodomainFormed alternate) aligned
  simpa only [body, reflexiveCodomain, Term.refl, Term.eq, Term.subst, substArgs, Op.binders, liftSub, single]
    using checked

end Jihoo.NativeKernel.Environment.LoanTyping.PureTyping
