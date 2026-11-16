import Jihoo.NativeLoanHigherKindSource
import Jihoo.NativeLoanSubstitution
set_option maxUniverseOffset 40

/-! Actual Loan64 ghost substitutions reconstruct higher-kind intrinsic
substitutions and their semantic valuation maps. Replacement coverage uses the
same existing Recognized grammar, and no semantic substitution or realization
certificate is supplied. Syntax and meaning commute with the constructed
substitution, including lambda lifting and the weakened arrow-code codomain.
This is a source-indexed coherence theorem for that existing coverage, not
an interpretation of arbitrary dependent Loan64 annotations or consistency. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Loan64

private abbrev RenameMembers (source target : List Kind) (indices : Nat → Nat) :=
  ∀ {kind index}, Member kind source index → Member kind target (indices index)

private def liftMembers (mapping : RenameMembers source target indices) (head : Kind) :
    RenameMembers (head :: source) (head :: target) (liftRenaming 1 indices) :=
  fun member => match member with
    | .here => .here
    | .there previous => .there (mapping previous)

private def renameExpression : Expression source kind →
    RenameMembers source target indices → Expression target kind
  | .var member,mapping => .var (mapping member)
  | .u64,_ => .u64
  | .univ level,_ => .univ level
  | .lam (domain := domain) valid body,mapping =>
      .lam valid (renameExpression body (liftMembers mapping domain))
  | .app function argument,mapping =>
      .app (renameExpression function mapping) (renameExpression argument mapping)
  | .arrowCode domain codomain,mapping =>
      .arrowCode (renameExpression domain mapping) (renameExpression codomain mapping)

private theorem shifted_renaming (term : Term) (indices : Nat → Nat) :
    (term.rename Nat.succ).rename (liftRenaming 1 indices) =
      (term.rename indices).rename Nat.succ := by
  rw [Term.rename_comp,Term.rename_comp]
  rfl

private theorem shifted_substitution (term : Term) (values : Nat → Term) :
    (term.rename Nat.succ).subst (liftSub 1 values) =
      (term.subst values).rename Nat.succ := by
  rw [Term.subst_rename,Term.rename_subst]
  rfl

private theorem rename_zero_lift (indices : Nat → Nat) : liftRenaming 0 indices = indices := rfl

private theorem substitution_zero_lift (values : Nat → Term) : liftSub 0 values = values := rfl

private theorem rename_syntax (expression : Expression source kind) :
    ∀ {target indices} (mapping : RenameMembers source target indices),
      (renameExpression expression mapping).syntax = expression.syntax.rename indices := by
  induction expression with
  | var member => intros; simp only [renameExpression,Expression.syntax,Term.rename]
  | u64 => intros; simp only [renameExpression,Expression.syntax,Term.u64,Term.rename,renameArgs]
  | univ level => intros; simp only [renameExpression,Expression.syntax,Term.univ,Term.rename,renameArgs]
  | @lam domain source codomain valid body ih =>
      intro target indices mapping
      simp only [renameExpression,Expression.syntax,Term.lam,Term.rename,renameArgs,
        Op.binders,Kind.syntax_rename,rename_zero_lift]
      rw [ih (liftMembers mapping domain)]
  | app function argument ihf iha =>
      intro target indices mapping
      simp only [renameExpression,Expression.syntax,Term.app,Term.rename,renameArgs,Op.binders,rename_zero_lift]
      rw [ihf mapping,iha mapping]
  | arrowCode domain codomain ihd ihc =>
      intro target indices mapping
      simp only [renameExpression,Expression.syntax,Term.pi,Term.rename,renameArgs,Op.binders,
        ihd mapping,ihc mapping,shifted_renaming,rename_zero_lift]

private theorem rename_meaning (expression : Expression source kind) :
    ∀ {target indices} (mapping : RenameMembers source target indices)
      (sourceValues : Values source) (targetValues : Values target),
      (∀ {kind index} (member : Member kind source index),
        (mapping member).value targetValues = member.value sourceValues) →
      (renameExpression expression mapping).meaning targetValues = expression.meaning sourceValues := by
  induction expression with
  | var member => intro target indices mapping sourceValues targetValues agreement; exact agreement member
  | u64 => intros; rfl
  | univ level => intros; rfl
  | @lam domain source codomain valid body ih =>
      intro target indices mapping sourceValues targetValues agreement
      simp only [renameExpression,Expression.meaning]
      congr 1
      funext argument
      apply ih (liftMembers mapping domain) (.cons argument sourceValues) (.cons argument targetValues)
      intro kind index member
      cases member with
      | here => rfl
      | there previous => exact agreement previous
  | app function argument ihf iha =>
      intro target indices mapping sourceValues targetValues agreement
      simp only [renameExpression,Expression.meaning]
      rw [ihf mapping sourceValues targetValues agreement,iha mapping sourceValues targetValues agreement]
  | arrowCode domain codomain ihd ihc =>
      intro target indices mapping sourceValues targetValues agreement
      simp only [renameExpression,Expression.meaning]
      rw [ihd mapping sourceValues targetValues agreement,ihc mapping sourceValues targetValues agreement]

/-- A replacement for each actual source member, with exactly its source
kind. The corresponding semantic substitution is derived by evaluation. -/
structure IntrinsicSubstitution (source target : List Kind) where
  expression : ∀ {kind index}, Member kind source index → Expression target kind

private def IntrinsicSubstitution.tail (replacement : IntrinsicSubstitution (head :: source) target) :
    IntrinsicSubstitution source target :=
  ⟨fun member => replacement.expression (.there member)⟩

def IntrinsicSubstitution.values : {source : List Kind} → IntrinsicSubstitution source target →
    Values target → Values source
  | [],_,_ => .nil
  | _ :: _,replacement,values =>
      .cons ((replacement.expression .here).meaning values) (replacement.tail.values values)

private theorem member_values (member : Member kind source index) :
    ∀ (replacement : IntrinsicSubstitution source target) (values : Values target),
      member.value (replacement.values values) = (replacement.expression member).meaning values := by
  induction member with
  | here => intros; rfl
  | there previous ih =>
      intro replacement values
      exact ih replacement.tail values

def IntrinsicSubstitution.Matches (replacement : IntrinsicSubstitution source target)
    (values : Nat → Term) : Prop :=
  ∀ {kind index} (member : Member kind source index), (replacement.expression member).syntax = values index

private def IntrinsicSubstitution.lift (replacement : IntrinsicSubstitution source target) (head : Kind) :
    IntrinsicSubstitution (head :: source) (head :: target) where
  expression member := match member with
    | .here => .var .here
    | .there previous => renameExpression (replacement.expression previous) (fun member => .there member)

private theorem matches_lift (replacement : IntrinsicSubstitution source target)
    (agreement : replacement.Matches values) (head : Kind) :
    (replacement.lift head).Matches (liftSubOne values) := by
  intro kind index member
  cases member with
  | here => rfl
  | there previous =>
      change (renameExpression (replacement.expression previous) (fun member => .there member)).syntax = _
      rw [rename_syntax,agreement previous]
      rfl

def IntrinsicSubstitution.apply (replacement : IntrinsicSubstitution source target) :
    Expression source kind → Expression target kind
  | .var member => replacement.expression member
  | .u64 => .u64
  | .univ level => .univ level
  | .lam (domain := domain) valid body => .lam valid ((replacement.lift domain).apply body)
  | .app function argument => .app (replacement.apply function) (replacement.apply argument)
  | .arrowCode domain codomain => .arrowCode (replacement.apply domain) (replacement.apply codomain)

/-- Substitution is capture-avoiding in the actual source syntax. Only the
member-indexed equations for the reconstructed replacements are needed. -/
theorem IntrinsicSubstitution.apply_syntax (expression : Expression source kind) :
    ∀ {target} (replacement : IntrinsicSubstitution source target) (values : Nat → Term),
      replacement.Matches values → (replacement.apply expression).syntax = expression.syntax.subst values := by
  induction expression with
  | var member =>
      intro target replacement values agreement
      simpa only [IntrinsicSubstitution.apply,Expression.syntax,Term.subst] using agreement member
  | u64 => intros; simp only [IntrinsicSubstitution.apply,Expression.syntax,Term.u64,Term.subst,substArgs]
  | univ level => intros; simp only [IntrinsicSubstitution.apply,Expression.syntax,Term.univ,Term.subst,substArgs]
  | @lam domain source codomain valid body ih =>
      intro target replacement values agreement
      simp only [IntrinsicSubstitution.apply,Expression.syntax,Term.lam,Term.subst,substArgs,
        Op.binders,Kind.syntax_subst,liftSub]
      rw [ih (replacement.lift domain) (liftSubOne values) (matches_lift replacement agreement domain)]
  | app function argument ihf iha =>
      intro target replacement values agreement
      simp only [IntrinsicSubstitution.apply,Expression.syntax,Term.app,Term.subst,substArgs,Op.binders,liftSub]
      rw [ihf replacement values agreement,iha replacement values agreement]
  | arrowCode domain codomain ihd ihc =>
      intro target replacement values agreement
      simp only [IntrinsicSubstitution.apply,Expression.syntax,Term.pi,Term.subst,substArgs,Op.binders,
        ihd replacement values agreement,ihc replacement values agreement,shifted_substitution,substitution_zero_lift]

private theorem apply_meaning_agreement (expression : Expression source kind) :
    ∀ {target} (replacement : IntrinsicSubstitution source target)
      (sourceValues : Values source) (targetValues : Values target),
      (∀ {kind index} (member : Member kind source index),
        (replacement.expression member).meaning targetValues = member.value sourceValues) →
      (replacement.apply expression).meaning targetValues = expression.meaning sourceValues := by
  induction expression with
  | var member => intro target replacement sourceValues targetValues agreement; exact agreement member
  | u64 => intros; rfl
  | univ level => intros; rfl
  | @lam domain source codomain valid body ih =>
      intro target replacement sourceValues targetValues agreement
      simp only [IntrinsicSubstitution.apply,Expression.meaning]
      congr 1
      funext argument
      apply ih (replacement.lift domain) (.cons argument sourceValues) (.cons argument targetValues)
      intro kind index member
      cases member with
      | here => rfl
      | there previous =>
          change (renameExpression (replacement.expression previous) (fun member => .there member)).meaning
            (.cons argument targetValues) = previous.value sourceValues
          exact (rename_meaning (replacement.expression previous) (fun member => .there member)
            targetValues (.cons argument targetValues) (by intros; rfl)).trans (agreement previous)
  | app function argument ihf iha =>
      intro target replacement sourceValues targetValues agreement
      simp only [IntrinsicSubstitution.apply,Expression.meaning]
      rw [ihf replacement sourceValues targetValues agreement,iha replacement sourceValues targetValues agreement]
  | arrowCode domain codomain ihd ihc =>
      intro target replacement sourceValues targetValues agreement
      simp only [IntrinsicSubstitution.apply,Expression.meaning]
      rw [ihd replacement sourceValues targetValues agreement,ihc replacement sourceValues targetValues agreement]

/-- The valuation map is induced by the intrinsic replacements. No arbitrary
semantic substitution or SubstitutionRealizes certificate is supplied. -/
theorem IntrinsicSubstitution.apply_meaning (replacement : IntrinsicSubstitution source target)
    (expression : Expression source kind) (values : Values target) :
    (replacement.apply expression).meaning values = expression.meaning (replacement.values values) :=
  apply_meaning_agreement expression replacement (replacement.values values) values
    (fun member => (member_values member replacement values).symm)

private theorem replacement_expression (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.Ghost.Substitution env (context source) (context target) values)
    (recognized : ∀ {kind index} (_member : Member kind source index), Recognized (values index))
    (member : Member kind source index) :
    ∃ expression : Expression target kind, expression.syntax = values index := by
  have actual : LoanTyping.HasType env [] (context target) true (values index) kind.syntax := by
    simpa only [Kind.syntax_subst] using typed index ⟨kind.syntax,false⟩ member.lookup
  obtain ⟨selected,expression,sourceEq,converted⟩ := recognized_principal wf (recognized member) actual
  have same : selected = kind := kind_syntax_injective wf converted
  subst selected
  exact ⟨expression,sourceEq⟩

/-- Actual source lookup typing reconstructs every intrinsic replacement at
its precise original Kind. Choice selects proved witnesses; no replacement
expression, semantic valuation map or output realization is an input. -/
theorem typed_substitution (wf : UnifiedProgram.EnvWellFormed env)
    (typed : LoanTyping.Ghost.Substitution env (context source) (context target) values)
    (recognized : ∀ {kind index} (_member : Member kind source index), Recognized (values index)) :
    ∃ replacement : IntrinsicSubstitution source target, replacement.Matches values := by
  classical
  let replacement : IntrinsicSubstitution source target :=
    ⟨fun member => Classical.choose (replacement_expression wf typed recognized member)⟩
  refine ⟨replacement,?_⟩
  intro kind index member
  exact Classical.choose_spec (replacement_expression wf typed recognized member)

/-- The complete Loan64 source judgment reconstructs both source and
substituted expressions. The same typed replacement map constructs their
semantic substitution and proves exact syntax/meaning coherence. Both source
and replacement coverage remain the existing Recognized grammar. -/
theorem checked_substitution_coherence
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanTyping.HasType env loans (context source) mode term type)
    (sourceRecognized : Recognized term)
    (substitution : LoanTyping.Ghost.Substitution env (context source) (context target) values)
    (replacementRecognized : ∀ {kind index} (_member : Member kind source index), Recognized (values index)) :
    ∃ kind, ∃ original : Expression source kind, ∃ result : Expression target kind,
      ∃ replacement : IntrinsicSubstitution source target,
        original.syntax = term ∧ LoanTyping.Conversion.Conv env kind.syntax type ∧
        LoanTyping.HasType env [] (context target) true (term.subst values) (type.subst values) ∧
        LoanTyping.Conversion.Conv env kind.syntax (type.subst values) ∧
        replacement.Matches values ∧ result.syntax = term.subst values ∧
        ∀ assignment : Values target, result.meaning assignment = original.meaning (replacement.values assignment) := by
  obtain ⟨kind,original,sourceEq,converted⟩ := recognized_principal history.wellFormed sourceRecognized typed
  obtain ⟨replacement,agreement⟩ := typed_substitution history.wellFormed substitution replacementRecognized
  have substituted := typed.ghostSubstitution history.wellFormed substitution
  have convertedSubstitution : LoanTyping.Conversion.Conv env kind.syntax (type.subst values) := by
    simpa only [Kind.syntax_subst] using converted.substitution values history.wellFormed.closed
  refine ⟨kind,original,replacement.apply original,replacement,sourceEq,converted,
    substituted,convertedSubstitution,agreement,?_,?_⟩
  · rw [replacement.apply_syntax original values agreement,sourceEq]
  · intro assignment
    exact replacement.apply_meaning original assignment

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Loan64
