import Jihoo.NativeLoanTyping

/-! Every existing shared-kernel derivation embeds constructively at any loan
stack. This proves extension of all five mutually inductive judgments, rather
than assuming their compatibility with the new loan-indexed rules. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem ofEnvironment (typed : Environment.HasType env ctx mode term type) :
    HasType env loans ctx mode term type := by
  apply Environment.HasType.rec (t := typed)
    (motive_1 := fun ctx erased domain sort _ => Binder env loans ctx erased domain sort)
    (motive_2 := fun ctx mode term type _ => HasType env loans ctx mode term type)
    (motive_3 := fun ctx mode data telescope arguments result _ => Arguments env loans ctx mode data telescope arguments result)
    (motive_4 := fun ctx motive signatures branches _ => Cases env loans ctx motive signatures branches)
    (motive_5 := fun ctx mode types branches _ => BranchTypes env loans ctx mode types branches)
  all_goals intros
  all_goals first
    | solve | apply Binder.intro <;> assumption
    | solve | apply HasType.var <;> assumption
    | solve | apply HasType.univ <;> assumption
    | solve | apply HasType.prop <;> assumption
    | solve | apply HasType.u64 <;> assumption
    | solve | apply HasType.i64 <;> assumption
    | solve | apply HasType.natural <;> assumption
    | solve | apply HasType.integer <;> assumption
    | solve | apply HasType.array <;> assumption
    | solve | apply HasType.lt <;> assumption
    | solve | apply HasType.eq <;> assumption
    | solve | apply HasType.pi <;> assumption
    | solve | apply HasType.lam <;> assumption
    | solve | apply HasType.app <;> assumption
    | solve | apply HasType.uadd <;> assumption
    | solve | apply HasType.usub <;> assumption
    | solve | apply HasType.refl <;> assumption
    | solve | apply HasType.zeroLe <;> assumption
    | solve | apply HasType.decide <;> assumption
    | solve | apply HasType.decideConverted <;> assumption
    | solve | apply HasType.elements <;> assumption
    | solve | apply HasType.index <;> assumption
    | solve | apply HasType.arith <;> assumption
    | solve | apply HasType.strict <;> assumption
    | solve | apply HasType.ltAdd <;> assumption
    | solve | apply HasType.ltCancel <;> assumption
    | solve | apply HasType.ltLe <;> assumption
    | solve | apply HasType.transport <;> assumption
    | solve | apply HasType.refine <;> assumption
    | solve | apply HasType.pack <;> assumption
    | solve | apply HasType.witness <;> assumption
    | solve | apply HasType.proof <;> assumption
    | solve | apply HasType.ifLt <;> assumption
    | solve | apply HasType.ifEq <;> assumption
    | solve | apply HasType.absurd <;> assumption
    | solve | apply HasType.foldI64 <;> assumption
    | solve | apply HasType.loop <;> assumption
    | solve | apply HasType.global <;> assumption
    | solve | apply HasType.ind <;> assumption
    | solve | apply HasType.con <;> assumption
    | solve | apply HasType.propElim <;> assumption
    | solve | apply HasType.buffer <;> assumption
    | solve | apply HasType.alloc <;> assumption
    | solve | apply HasType.store <;> assumption
    | solve | apply HasType.load <;> assumption
    | solve | apply HasType.free <;> assumption
    | solve | apply HasType.refBuffer <;> assumption
    | solve | apply HasType.ghostBorrow <;> assumption
    | solve | apply HasType.ghostDeref <;> assumption
    | solve | apply HasType.borrowedIndex <;> assumption
    | solve | apply HasType.back <;> assumption
    | solve | apply HasType.give <;> assumption
    | solve | apply HasType.take <;> assumption
    | solve | apply HasType.foldOwned <;> assumption
    | solve | apply HasType.dataElim <;> assumption
    | solve | apply HasType.drop <;> assumption
    | solve | apply HasType.refOwned <;> assumption
    | solve | apply HasType.ghostBorrowOwned <;> assumption
    | solve | apply HasType.ghostDerefOwned <;> assumption
    | solve | apply HasType.view <;> assumption
    | solve | apply HasType.convert <;> assumption
    | solve | apply Arguments.nil <;> assumption
    | solve | apply Arguments.cons <;> assumption
    | solve | apply Cases.nil
    | solve | apply Cases.cons <;> assumption
    | solve | apply BranchTypes.nil
    | solve | apply BranchTypes.cons <;> assumption

theorem binder_ofEnvironment (source : Environment.Binder env ctx erased domain sort) :
    Binder env loans ctx erased domain sort := by
  cases source with
  | intro typed allowed => exact .intro (ofEnvironment typed) allowed

theorem arguments_ofEnvironment (source : Environment.Arguments env ctx mode data telescope values result) :
    Arguments env loans ctx mode data telescope values result := by
  apply Environment.Arguments.rec (t := source)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun ctx mode data telescope values result _ => Arguments env loans ctx mode data telescope values result)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first
    | trivial
    | solve | apply Arguments.nil <;> assumption
    | solve | apply Arguments.cons <;> first | assumption | exact ofEnvironment (by assumption)

theorem cases_ofEnvironment (source : Environment.Cases env ctx motive signatures branches) :
    Cases env loans ctx motive signatures branches := by
  apply Environment.Cases.rec (t := source)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun ctx motive signatures branches _ => Cases env loans ctx motive signatures branches)
    (motive_5 := fun _ _ _ _ _ => True)
  all_goals intros
  all_goals first
    | trivial
    | solve | apply Cases.nil <;> assumption
    | solve | apply Cases.cons <;> first | assumption | exact ofEnvironment (by assumption)

theorem branches_ofEnvironment (source : Environment.BranchTypes env ctx mode types branches) :
    BranchTypes env loans ctx mode types branches := by
  apply Environment.BranchTypes.rec (t := source)
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun ctx mode types branches _ => BranchTypes env loans ctx mode types branches)
  all_goals intros
  all_goals first
    | trivial
    | solve | apply BranchTypes.nil <;> assumption
    | solve | apply BranchTypes.cons <;> first | assumption | exact ofEnvironment (by assumption)

end Jihoo.NativeKernel.Environment.LoanTyping
