import Jihoo.NativeLoanGhostPromotion

/-! Runtime Borrow permission follows from the loan-indexed typing derivation,
including arbitrary conversions of its result type. Ghost borrowing ignores
runtime permissions, and exiting the last reader prevents further code borrows. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

def BorrowPermission (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .node .borrow [owner] => Loans.borrowAllowed mode ctx.length loans owner = true
  | _ => True

theorem HasType.borrow_permission (typed : HasType env loans ctx mode term type) :
    BorrowPermission loans ctx mode term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun loans ctx mode term _ _ => BorrowPermission loans ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case ghostBorrow => exact Loans.ghost_borrow_allowed
  case ghostBorrowOwned => exact Loans.ghost_borrow_allowed
  case dataElim => split <;> trivial

theorem HasType.code_borrow_named (typed : HasType env loans ctx false (.borrow owner) type) :
    ∃ index, owner = .var index ∧ Loans.active ctx.length loans index = true := by
  have allowed := typed.borrow_permission
  exact Loans.code_borrow_allowed.mp allowed

theorem HasType.no_code_borrow_without_reader :
    ¬ HasType env [] ctx false (.borrow owner) type := by
  intro typed
  obtain ⟨index,named,active⟩ := typed.code_borrow_named
  exact Bool.noConfusion active

end Jihoo.NativeKernel.Environment.LoanTyping
