import Jihoo.NativeLoanConversionAlgebra
import Jihoo.NativeLoanUniquenessSubstitutions
import Jihoo.NativeEnvironmentUniquenessAlgebra

/-! Determinism of actual constructor argument telescopes for the full loan
judgment, across arbitrary source stacks, contexts and modes. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

theorem Arguments.result_unique (args : Arguments env loans ctx mode data telescope xs result)
    (wf : UnifiedProgram.EnvWellFormed env) :
    ∀ (loans' : Loans.Stack) (ctx' : Context) (mode' data' : Bool) (telescope' result' : Term),
    Arguments env loans' ctx' mode' data' telescope' xs result' → Conv env telescope telescope' → Conv env result result' := by
  apply Arguments.rec (t := args)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ telescope xs result _ =>
      ∀ (loans' : Loans.Stack) (ctx' : Context) (mode' data' : Bool) (telescope' result' : Term),
      Arguments env loans' ctx' mode' data' telescope' xs result' → Conv env telescope telescope' → Conv env result result')
    (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case nil =>
    rename_i loans ctx mode data telescope result converted loans' ctx' mode' data' telescope' result' other same
    cases other with
    | nil converted' => exact .trans (.symm converted) (.trans same converted')
  case cons =>
    rename_i telescope erased domain rest loans ctx mode data argument arguments result converted typed tail _ ihtail loans' ctx' mode' data' telescope' result' other same
    cases other with
    | cons converted' typed' tail' =>
      have bodies := ((RawLend.Conv.trans (.symm converted) (.trans same converted')).pi_injective wf.admissible).2.2
      exact ihtail _ _ _ _ _ _ tail' (bodies.substitution (single argument) wf.closed)

end Jihoo.NativeKernel.Environment.LoanTyping
