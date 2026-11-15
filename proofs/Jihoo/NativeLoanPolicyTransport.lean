import Jihoo.NativeLoanPolicies
import Jihoo.NativeBackMetatheory
import Jihoo.NativeEnvironmentGhostMetatheory

/-! Loan-local raw representation witnesses are closed under arbitrary
binding and raw conversion. No old Family policy is transported along a raw
Lend equation without its explicit embedding into the local policy first. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

theorem Owned.renaming (h : Owned env T) (ρ : Nat → Nat) (closed : Conversion.Closed env) : Owned env (T.rename ρ) := by
  cases h with
  | buffer converted =>
      exact .buffer (by simpa only [rename_buffer] using converted.renaming ρ closed)
  | family found boxed converted =>
      exact .family found boxed (by simpa only [Term.rename] using converted.renaming ρ closed)

theorem Owned.substitution (h : Owned env T) (σ : Nat → Term) (closed : Conversion.Closed env) : Owned env (T.subst σ) := by
  cases h with
  | buffer converted =>
      exact .buffer (by simpa only [subst_buffer] using converted.substitution σ closed)
  | family found boxed converted =>
      exact .family found boxed (by simpa only [Term.subst] using converted.substitution σ closed)


theorem binderAllowed_renaming (closed : Conversion.Closed env) (allowed : binderAllowed env erased domain sort) (ρ : Nat → Nat) :
    binderAllowed env erased (domain.rename ρ) sort := by
  rcases allowed with pure | ⟨erased, family, count, indices, entry, found, data, converted⟩
  · exact Or.inl (pureBinderAllowed_renaming closed pure ρ)
  · exact Or.inr ⟨erased, family, count, indices.map (Term.rename ρ), entry, found, data,
      by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ closed⟩

theorem binderAllowed_substitution (closed : Conversion.Closed env) (allowed : binderAllowed env erased domain sort) (substitution : Nat → Term) :
    binderAllowed env erased (domain.subst substitution) sort := by
  rcases allowed with pure | ⟨erased, family, count, indices, entry, found, data, converted⟩
  · exact Or.inl (pureBinderAllowed_substitution closed pure substitution)
  · exact Or.inr ⟨erased, family, count, indices.map (Term.subst substitution), entry, found, data,
      by simpa [Term.subst, substArgs, Op.binders, liftSub] using converted.substitution substitution closed⟩

theorem BackRepresentation.renaming (h : BackRepresentation env ghost erased motive) (ρ : Nat → Nat) (closed : Conversion.Closed env) :
    BackRepresentation env ghost erased (motive.rename ρ) := by
  rcases h with ghost | erased | ⟨flag, domain, body, converted, fixed⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl erased)
  · exact Or.inr (Or.inr ⟨flag, domain.rename ρ, body.rename (liftRenaming 1 ρ),
      by simpa only [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ closed,
      by simpa only [fixedRepresentation_rename] using fixed⟩)

theorem BackRepresentation.substitution (h : BackRepresentation env ghost erased motive) (σ : Nat → Term) (closed : Conversion.Closed env) :
    BackRepresentation env ghost erased (motive.subst σ) := by
  rcases h with ghost | erased | ⟨flag, domain, body, converted, fixed⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl erased)
  · exact Or.inr (Or.inr ⟨flag, domain.subst σ, body.subst (liftSub 1 σ),
      by simpa only [Term.subst, substArgs, Op.binders, liftSub] using converted.substitution σ closed,
      fixedRepresentation_substitution fixed _⟩)

theorem outlivedHead_rename (term : Term) (ρ : Nat → Nat) :
    Lending.outlivedHead env (term.rename ρ) = Lending.outlivedHead env term := by
  cases term with
  | var => simp [Lending.outlivedHead,Term.rename]
  | node op args =>
    cases op <;> cases args with
    | nil => simp [Lending.outlivedHead,Term.rename,renameArgs]
    | cons first rest =>
      cases rest with
      | nil => simp [Lending.outlivedHead,Term.rename,renameArgs]
      | cons second tail =>
        cases tail <;> simp [Lending.outlivedHead,Term.rename,renameArgs]

theorem outlivedHead_subst (term : Term) (σ : Nat → Term)
    (allowed : Lending.outlivedHead env term = true) : Lending.outlivedHead env (term.subst σ) = true := by
  cases term with
  | var => simp [Lending.outlivedHead] at allowed
  | node op args =>
    cases op <;> cases args with
    | nil => simp_all [Lending.outlivedHead,Term.subst,substArgs]
    | cons first rest =>
      cases rest with
      | nil => simp_all [Lending.outlivedHead,Term.subst,substArgs]
      | cons second tail =>
        cases tail <;> simp_all [Lending.outlivedHead,Term.subst]


theorem Outlived.renaming (closed : Conversion.Closed env)
    (allowed : Outlived env type) (ρ : Nat → Nat) : Outlived env (type.rename ρ) := by
  obtain ⟨normal,converted,head⟩ := allowed
  exact ⟨normal.rename ρ,converted.renaming ρ closed,by simpa only [outlivedHead_rename] using head⟩

theorem Outlived.substitution (closed : Conversion.Closed env)
    (allowed : Outlived env type) (σ : Nat → Term) : Outlived env (type.subst σ) := by
  obtain ⟨normal,converted,head⟩ := allowed
  exact ⟨normal.subst σ,converted.substitution σ closed,outlivedHead_subst normal σ head⟩

theorem Owned.of_conversion (converted : Conv env first second) (owned : Owned env second) : Owned env first := by
  cases owned with
  | buffer original => exact .buffer (converted.trans original)
  | family found boxed original => exact .family found boxed (converted.trans original)

theorem binderAllowed_congr (allowed : binderAllowed env erased first sort) (converted : Conv env first second) :
    binderAllowed env erased second sort := by
  rcases allowed with pure | ⟨erased,family,count,indices,entry,found,data,related⟩
  · apply Or.inl
    cases erased with
    | false => exact pure
    | true =>
        rcases pure with proposition | scalar
        · exact Or.inl proposition
        · exact Or.inr (converted.symm.trans scalar)
  · exact Or.inr ⟨erased,family,count,indices,entry,found,data,converted.symm.trans related⟩

theorem applicationAllowed_congr (allowed : applicationAllowed env ghost domain argument)
    (domains : Conv env domain domain') (arguments : Conv env argument argument') :
    applicationAllowed env ghost domain' argument' := by
  rcases allowed with ghost | ⟨normal,converted,free,represented⟩
  · exact Or.inl ghost
  · refine Or.inr ⟨normal,domains.symm.trans converted,free,?_⟩
    rcases represented with ordinary | ⟨kind,value,reduced,plain⟩
    · exact Or.inl ordinary
    · exact Or.inr ⟨kind,value,arguments.symm.trans reduced,plain⟩

theorem nonFunction_congr (allowed : nonFunction env first) (converted : Conv env first second) : nonFunction env second :=
  RawLend.NonFunction.of_conversion converted.symm allowed

theorem absurdAllowed_congr (allowed : absurdAllowed env ghost first) (converted : Conv env first second) :
    absurdAllowed env ghost second := by
  rcases allowed with ghost | function
  · exact Or.inl ghost
  · exact Or.inr (nonFunction_congr function converted)

theorem continuationAllowed_congr (allowed : continuationAllowed env ghost first) (converted : Conv env first second) :
    continuationAllowed env ghost second := by
  rcases allowed with ghost | function
  · exact Or.inl ghost
  · exact Or.inr (nonFunction_congr function converted)

theorem Outlived.of_conversion (converted : Conv env first second) (allowed : Outlived env second) : Outlived env first := by
  obtain ⟨normal,reduced,head⟩ := allowed
  exact ⟨normal,converted.trans reduced,head⟩

theorem loopMotiveAllowed_congr (allowed : loopMotiveAllowed env ghost proof motive) (converted : Conv env motive motive') :
    loopMotiveAllowed env ghost proof motive' := by
  rcases allowed with ghost | proof | ⟨normal,reduced,scalar⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr ⟨normal,converted.symm.trans reduced,scalar⟩)

theorem BackRepresentation.of_conversion (converted : Conv env first second)
    (allowed : BackRepresentation env ghost erased second) : BackRepresentation env ghost erased first := by
  rcases allowed with ghost | erased | ⟨flag,domain,body,reduced,fixed⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl erased)
  · exact Or.inr (Or.inr ⟨flag,domain,body,converted.trans reduced,fixed⟩)

theorem IterationMotiveAllowed.of_conversion (converted : Conv env first second)
    (allowed : IterationMotiveAllowed env ghost proof second) : IterationMotiveAllowed env ghost proof first := by
  rcases allowed with ghost | proof | ⟨normal,reduced,scalar⟩ | ⟨flag,domain,body,reduced,owned⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr (Or.inl ⟨normal,converted.trans reduced,scalar⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨flag,domain,body,converted.trans reduced,owned⟩))

theorem ViewMotiveAllowed.of_conversion (converted : Conv env first second)
    (allowed : ViewMotiveAllowed env ghost dependent second) : ViewMotiveAllowed env ghost dependent first := by
  rcases allowed with ghost | dependent | ⟨flag,domain,body,reduced,represented⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl dependent)
  · exact Or.inr (Or.inr ⟨flag,domain,body,converted.trans reduced,represented⟩)

end Jihoo.NativeKernel.Environment.LoanTyping
