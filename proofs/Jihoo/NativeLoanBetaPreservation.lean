import Jihoo.NativeLoanFunctionInversion

/-! Original-type ghost beta preservation for the full loan-indexed judgment.
This theorem does not substitute computations into CODE derivations. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem HasType.ghostBetaContract
    (wf : UnifiedProgram.EnvWellFormed env)
    (function : HasType env loans ctx mode (.lam erased domain body) (.pi actualErased actualDomain result))
    (argument : HasType env argumentLoans ctx true value actualDomain) :
    HasType env [] ctx true (body.subst (single value)) (result.subst (single value)) := by
  obtain ⟨sort, bodyType, domainTyped, bodyTyped, converted⟩ := function.lamView
  obtain ⟨sameErased, domains, results⟩ := converted.pi_injective wf.admissible
  exact (bodyTyped.ghostInstantiate wf (argument.convert domains.symm)).convert
    (results.substitution (single value) wf.closed)

theorem HasType.ghostBeta
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.app (.lam erased domain body) value) type) :
    HasType env [] ctx true (body.subst (single value)) type := by
  obtain ⟨actualErased, actualDomain, result, function, argument, allowed, converted⟩ := typed.appView
  exact (function.ghostBetaContract wf (argument.ghost [])).convert converted

end Jihoo.NativeKernel.Environment.LoanTyping
