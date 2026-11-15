import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanGhostPromotion

namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem HasType.bufferSize (typed : HasType env loans ctx mode term type) :
    ∀ n, term = .buffer n → HasType env [] ctx true n .u64 := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ context _ expression _ _ =>
      ∀ n, expression = .buffer n → HasType env [] context true n .u64)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case convert =>
    rename_i stack context ghost expression original target prior converted ih n matched
    exact ih n matched
  case buffer =>
    rename_i stack context size sizeTyped ih n matched
    cases matched
    exact sizeTyped.ghost []
  case dataElim =>
    rename_i family entry analysis stack context motive proof ghost scrutinee indices types branches
      found isData boxed size motiveTyped scrutineeTyped generated branchesTyped allowed ihMotive ihScrutinee ihBranches n matched
    cases analysis <;> cases matched
  all_goals rename_i n matched
  all_goals cases matched

theorem HasType.bufferView (typed : HasType env loans ctx mode (.buffer n) type) :
    HasType env [] ctx true n .u64 ∧ Conversion.Conv env (.univ 0) type :=
  ⟨typed.bufferSize n rfl,typed.principalView⟩

end Jihoo.NativeKernel.Environment.LoanTyping
