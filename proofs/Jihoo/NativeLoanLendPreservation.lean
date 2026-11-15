import Jihoo.NativeLoanConversionAlgebra
import Jihoo.NativeLoanBetaPreservation

/-! Atomic pure results of the actual loan-indexed body checks. Specialized
callbacks need not type at arbitrary arguments, so no intermediate desugared
term is assumed typed. Runtime heap/quantity preservation is separate. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open Lending

theorem finish_from_specialized_checks
    (wf : UnifiedProgram.EnvWellFormed env)
    (continuation : HasType env loans ctx mode (restore owner first body) (.pi false domain result))
    (reader : HasType env readerLoans ctx true value domain) :
    HasType env [] ctx true (finish owner body value) (result.subst (single value)) := by
  have applied : HasType env [] ctx true (.app (restore owner first body) value)
      (result.subst (single value)) :=
    .app (continuation.ghost []) (reader.ghost []) (Or.inl rfl)
  exact applied.ghostBeta wf

theorem dependent_finish_original_type
    (wf : UnifiedProgram.EnvWellFormed env)
    (reader : HasType env readerLoans ctx readerMode (read owner readerBody) domain)
    (firstConverted : Conversion.Conv env first domain)
    (continuation : HasType env loans ctx mode (restore owner first body) (.pi false first result))
    (converted : Conversion.Conv env result normal)
    (removed : PartialRenaming.shift (-1) 0 normal = some outside) :
    HasType env [] ctx true (finish owner body (read owner readerBody)) outside := by
  exact (finish_from_specialized_checks wf continuation
    ((reader.ghost []).convert firstConverted.symm)).convert
      (result_outside wf converted removed)

theorem reader_from_generic_checks
    (wf : UnifiedProgram.EnvWellFormed env)
    (ownerTyped : HasType env ownerLoans ctx ownerMode owner ownerType)
    (owned : Owned env ownerType)
    (reader : HasType env loans ctx mode (.lam false domain body)
      (.pi false (.ref ownerType) (result.rename Nat.succ))) :
    HasType env [] ctx true (read owner body) result := by
  have argument : HasType env [] ctx true (.borrow owner) (.ref ownerType) :=
    .ghostBorrowOwned (ownerTyped.ghost []) owned
  have applied : HasType env [] ctx true (.app (.lam false domain body) (.borrow owner)) result := by
    simpa only [NativeKernel.single, Term.subst_rename, Term.subst_id] using
      (HasType.app (reader.ghost []) argument (Or.inl rfl))
  exact applied.ghostBeta wf

theorem continuation_from_generic_checks
    (wf : UnifiedProgram.EnvWellFormed env)
    (ownerTyped : HasType env ownerLoans ctx ownerMode owner ownerType)
    (reader : HasType env readerLoans ctx true value domain)
    (continuation : HasType env loans ctx mode (.lam false first (.lam false again body))
      (.pi false domain ((Term.pi false ownerType (result.rename Nat.succ)).rename Nat.succ))) :
    HasType env [] ctx true (finish owner body value) result := by
  have applied : HasType env [] ctx true
      (.app (.lam false first (.lam false again body)) value)
      (.pi false ownerType (result.rename Nat.succ)) := by
    simpa only [NativeKernel.single, Term.subst_rename, Term.subst_id] using
      (HasType.app (continuation.ghost []) (reader.ghost []) (Or.inl rfl))
  have reduced : HasType env [] ctx true
      (.lam false (again.subst (single value)) (body.subst (liftSubOne (single value))))
      (.pi false ownerType (result.rename Nat.succ)) := by
    simpa only [Term.lam, Term.subst, substArgs, Op.binders, liftSub] using applied.ghostBeta wf
  have returned : HasType env [] ctx true
      (.app (.lam false (again.subst (single value)) (body.subst (liftSubOne (single value)))) owner)
      result := by
    simpa only [NativeKernel.single, Term.subst_rename, Term.subst_id] using
      (HasType.app reduced (ownerTyped.ghost []) (Or.inl rfl))
  simpa only [returned_owner_substitutions] using returned.ghostBeta wf

theorem generic_finish_original_type
    (wf : UnifiedProgram.EnvWellFormed env)
    (ownerTyped : HasType env ownerLoans ctx ownerMode owner ownerType)
    (owned : Owned env ownerType)
    (reader : HasType env loans ctx mode (.lam false readerDomain readerBody)
      (.pi false (.ref ownerType) (domain.rename Nat.succ)))
    (continuation : HasType env loans ctx mode (.lam false first (.lam false again body))
      (.pi false domain ((Term.pi false ownerType (result.rename Nat.succ)).rename Nat.succ))) :
    HasType env [] ctx true (finish owner body (read owner readerBody)) result :=
  continuation_from_generic_checks wf ownerTyped
    (reader_from_generic_checks wf ownerTyped owned reader) continuation

theorem HasType.explicitLendFinish
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) :
    ∀ owner domain readerBody first again body,
      term = .lend owner (.lam false domain readerBody) (.lam false first (.lam false again body)) →
      HasType env [] ctx true (finish owner body (read owner readerBody)) type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ context _ expression result _ =>
      ∀ owner domain readerBody first again body,
        expression = .lend owner (.lam false domain readerBody) (.lam false first (.lam false again body)) →
        HasType env [] context true (finish owner body (read owner readerBody)) result)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case convert =>
    rename_i stack context ghost expression original target prior converted ih owner domain readerBody first again body matched
    exact (ih owner domain readerBody first again body matched).convert converted
  case lendGeneric =>
    rename_i stack context ghost originalOwner ownerType domainType reader continuation result
      ownerTyped owned outlived readerTyped continuationTyped allowed ihOwner ihReader ihContinuation
      owner domain readerBody first again body matched
    cases matched
    exact generic_finish_original_type wf ownerTyped owned readerTyped continuationTyped
  case lendDependentCode =>
    rename_i stack context originalOwner ownerType originalDomain sort originalReader domainType originalFirst
      originalAgain originalBody result normal outside ownerTyped owned domainTyped domainConverted readerTyped
      outlived firstConverted againConverted continuationTyped converted removed allowed ihOwner ihDomain ihReader ihContinuation
      owner domain readerBody first again body matched
    cases matched
    exact dependent_finish_original_type wf readerTyped firstConverted continuationTyped converted removed
  case lendDependentGhost =>
    rename_i stack context originalOwner ownerType originalDomain sort originalReader domainType originalFirst
      originalAgain originalBody result normal outside ownerTyped owned domainTyped domainConverted readerTyped
      outlived firstConverted againConverted continuationTyped converted removed ihOwner ihDomain ihReader ihContinuation
      owner domain readerBody first again body matched
    cases matched
    exact dependent_finish_original_type wf readerTyped firstConverted continuationTyped converted removed
  case dataElim =>
    rename_i family entry analysis stack context motive proof ghost scrutinee indices types branches
      found isData boxed size motiveTyped scrutineeTyped generated branchesTyped allowed ihMotive ihScrutinee ihBranches
      owner domain readerBody first again body matched
    cases analysis <;> cases matched
  all_goals rename_i owner domain readerBody first again body matched
  all_goals cases matched

end Jihoo.NativeKernel.Environment.LoanTyping
