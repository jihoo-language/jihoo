import Jihoo.NativeEffectfulCodeInterpretation
import Jihoo.NativeLoanValueProjection
set_option maxUniverseOffset 40

/-! Concrete finite code denotations also respect the genuine raw Lend macro
theory. Typed source recovery keeps using the installed native judgment; this
additive bridge does not recheck untyped macro intermediates as source code. -/
namespace Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
open MultiUniverse (Mono)
variable {parameters familyCount observationCount : Nat}
variable {levels : Fin parameters → Fin 32} {signatures : Fin familyCount → Signature parameters}
variable {observed : Fin observationCount → Mono parameters}

theorem TypeCode.loan_project_syntax (A : TypeCode parameters familyCount observationCount) :
    ValueErasure.Loan.project env (A.syntax offset) = A.syntax offset := by
  induction A generalizing offset with
  | parameter index => exact ValueErasure.Loan.project_variable _ _
  | natural => exact ValueErasure.Loan.project_ordinary_node (by rfl) (by intro h; cases h) []
  | arrow A B ha hb => rw [TypeCode.syntax_arrow,ValueErasure.Loan.project_pi,ha,hb]
  | fiber family observation =>
    change ValueErasure.Loan.project env (.app (.var _) (.var _)) = _
    rw [ValueErasure.Loan.project_application,ValueErasure.Loan.project_variable,ValueErasure.Loan.project_variable]
    rfl

theorem Annotation.loan_project_syntax (source : Annotation parameters familyCount observationCount) :
    ValueErasure.Loan.project env (source.syntax offset) = source.code.syntax offset := by
  induction source generalizing offset with
  | pure code => exact code.loan_project_syntax
  | arrow domain body hd hb =>
    simp only [Annotation.syntax,Annotation.code,TypeCode.syntax_arrow,ValueErasure.Loan.project_pi,hd,hb]
  | strict first result ih => simp only [Annotation.syntax,Annotation.code,ValueErasure.Loan.project_strict,ih]
  | free owner result ih => simp only [Annotation.syntax,Annotation.code,ValueErasure.Loan.project_free,ih]

/-- Conversion paths can contain arbitrary untyped Lend macros and forged
family metadata; only the actual environment's admitted delta invariant is used. -/
theorem Annotation.raw_loan_code_injective (wf : UnifiedProgram.EnvWellFormed env)
    {first second : Annotation parameters familyCount observationCount}
    (converted : RawLend.Conv env (first.syntax offset) (second.syntax offset)) : first.code = second.code := by
  have projected := ValueErasure.Loan.conversion wf.admissible converted
  rw [Annotation.loan_project_syntax,Annotation.loan_project_syntax] at projected
  exact TypeCode.syntax_injective wf projected

theorem Annotation.checked_loan_model_coherent (wf : UnifiedProgram.EnvWellFormed env)
    (frame : LookupFrame levels signatures observed offset ctx)
    (first second : Annotation parameters familyCount observationCount)
    (firstTyped : HasType env ctx firstMode (first.syntax offset) firstType)
    (secondTyped : HasType env ctx secondMode (second.syntax offset) secondType)
    (converted : RawLend.Conv env (first.syntax offset) (second.syntax offset))
    (assignment : Assignment levels signatures observed) :
    HEq (first.interpret_checked wf frame firstTyped assignment)
      (second.interpret_checked wf frame secondTyped assignment) := by
  have projected := ValueErasure.Loan.conversion wf.admissible converted
  rw [Annotation.loan_project_syntax,Annotation.loan_project_syntax] at projected
  exact TypeCode.model_coherent wf projected assignment
    (first.recover wf frame firstTyped).1 (second.recover wf frame secondTyped).1

/-- Replay alignment reaches the same pure finite-code annotation under the
composed projected actual values, even if its original equation uses Lend. -/
theorem Annotation.closing_loan_projection (admissible : EnvironmentDelta.Admissible env)
    (source : Annotation parameters familyCount observationCount)
    (aligned : RawLend.Conv env ((source.syntax offset).subst values) actualDomain) :
    FamilyIota.Extended.Conv env
      ((source.code.syntax offset).subst (fun index => ValueErasure.Loan.project env (values index)))
      (ValueErasure.Loan.project env actualDomain) := by
  simpa only [Annotation.loan_project_syntax] using ValueErasure.Loan.closing_annotation_projection admissible aligned

end Jihoo.NativeKernel.Environment.Semantics.DependentFamilies
