import Jihoo.NativeLoanEmbedding

/-! Ghost promotion erases runtime permissions, including after a dependent
reader entered a loan frame. The target stack is arbitrary. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem HasType.ghost (typed : HasType env loans ctx mode term type) :
    ∀ target, HasType env target ctx true term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ ctx erased domain sort _ => ∀ target, Binder env target ctx erased domain sort)
    (motive_2 := fun _ ctx _ term type _ => ∀ target, HasType env target ctx true term type)
    (motive_3 := fun _ ctx _ data telescope arguments result _ => ∀ target, Arguments env target ctx true data telescope arguments result)
    (motive_4 := fun _ ctx motive signatures branches _ => ∀ target, Cases env target ctx motive signatures branches)
    (motive_5 := fun _ ctx _ types branches _ => ∀ target, BranchTypes env target ctx true types branches)
  all_goals intros
  all_goals first
    | solve | apply Binder.intro <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.var <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.univ <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.prop <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.u64 <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.i64 <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.natural <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.integer <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.array <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.lt <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.eq <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.pi <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.lam <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.app <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.uadd <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.usub <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.refl <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.zeroLe <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.decide <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.decideConverted <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.elements <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.index <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.arith <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.strict <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ltAdd <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ltCancel <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ltLe <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.transport <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.refine <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.pack <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.witness <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.proof <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ifLt <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ifEq <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.absurd <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.foldI64 <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.loop <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.global <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ind <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.con <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.propElim <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.buffer <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.alloc <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.store <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.load <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.free <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.refBuffer <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ghostBorrow <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ghostDeref <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.borrowedIndex <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.back <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.give <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.take <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.foldOwned <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.dataElim <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.drop <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.refOwned <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ghostBorrowOwned <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.ghostDerefOwned <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.view <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply HasType.convert <;> first | assumption | apply_assumption | exact Or.inl rfl | simpa only [Bool.true_or]
    | solve | apply Arguments.nil <;> first | assumption | apply_assumption
    | solve | apply Arguments.cons <;> first | assumption | apply_assumption | simpa only [Bool.true_or]
    | solve | apply Cases.nil
    | solve | apply Cases.cons <;> first | assumption | apply_assumption
    | solve | apply BranchTypes.nil
    | solve | apply BranchTypes.cons <;> first | assumption | apply_assumption | simpa only [Bool.true_or]
    | solve | apply HasType.lendGeneric <;> first | assumption | apply_assumption | exact Or.inl rfl
    | solve | apply HasType.lendDependentGhost <;> first | assumption | apply_assumption
    | solve | apply HasType.elements <;> first | assumption | solve | intros; apply_assumption <;> assumption
    | solve | apply HasType.ind <;> first | assumption | solve | intros; apply_assumption <;> assumption

end Jihoo.NativeKernel.Environment.LoanTyping
