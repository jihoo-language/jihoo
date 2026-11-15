import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanGhostPromotion
import Jihoo.NativeLendRawAPI

/-! An explicit pair of callback lambda telescopes uses atomic finish. Every
other typable Lend has the genuine generic source premises, so its immediate
macro expansion is typed without imposing new callback assumptions. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

def explicitCallbacks : Term → Term → Bool
  | .lam false _ _, .lam false _ (.lam false _ _) => true
  | _,_ => false

private theorem app_constant
    (function : HasType env [] ctx true f (.pi false A (B.rename Nat.succ)))
    (argument : HasType env [] ctx true a A) : HasType env [] ctx true (.app f a) B := by
  have applied := HasType.app function argument (Or.inl rfl)
  change HasType env [] ctx true (.app f a) ((B.rename Nat.succ).subst (single a)) at applied
  simpa only [Term.shift_subst_single] using applied

theorem generic_pure_typed
    (ownerTyped : HasType env loans ctx mode owner ownerType) (owned : Owned env ownerType)
    (readerTyped : HasType env loans ctx mode reader (.pi false (.ref ownerType) (valueType.rename Nat.succ)))
    (continuationTyped : HasType env loans ctx mode continuation
      (.pi false valueType ((Term.pi false ownerType (result.rename Nat.succ)).rename Nat.succ))) :
    HasType env [] ctx true (RawLend.desugar owner reader continuation) result := by
  have borrowed : HasType env [] ctx true (.borrow owner) (.ref ownerType) :=
    .ghostBorrowOwned (ownerTyped.ghost []) owned
  have readTyped : HasType env [] ctx true (.app reader (.borrow owner)) valueType :=
    app_constant (readerTyped.ghost []) borrowed
  have continued : HasType env [] ctx true (.app continuation (.app reader (.borrow owner)))
      (.pi false ownerType (result.rename Nat.succ)) :=
    app_constant (continuationTyped.ghost []) readTyped
  exact app_constant continued (ownerTyped.ghost [])

theorem HasType.nonexplicitLendDesugar
    (typed : HasType env loans ctx mode (.lend owner reader continuation) type)
    (nonexplicit : explicitCallbacks reader continuation = false) :
    HasType env [] ctx true (RawLend.desugar owner reader continuation) type := by
  obtain ⟨principal,origin,converted⟩ := typed.lendView
  cases origin with
  | generic ownerTyped owned outlived readerTyped continuationTyped allowed =>
    exact (generic_pure_typed ownerTyped owned readerTyped continuationTyped).convert converted
  | dependentCode => simp [explicitCallbacks] at nonexplicit
  | dependentGhost => simp [explicitCallbacks] at nonexplicit

end Jihoo.NativeKernel.Environment.LoanTyping
