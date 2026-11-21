import Jihoo.NativeBindingMachineLoanTyping
import Jihoo.NativeLoanFoldUnrolling
import Jihoo.NativeLoanObservedSubtractionConversion

/-! Iteration retains the exact closing origins of its entering value and
its callback, including captures. At every observed iteration index this
recovers the ghost type of the accumulator's original expression. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine

open Semantics.LoanArithmetic (Numeric)

theorem LoanSourceTyped.fold_prefix_origin
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .fold count seed body)
    (observed : Numeric env (code.child count).origin n) (bound : n < 2^64)
    (i : Nat) (within : i ≤ n) :
    LoanTyping.HasType env [] [] true (LoanTyping.ProofLoop.unroll n (code.child seed).origin (code.child body).origin i) type := by
  have closed : LoanTyping.HasType env [] [] true
      (.fold (code.child count).origin (code.child seed).origin (code.child body).origin) type := by
    simpa [Code.origin,Code.child,shape,Term.fold,Term.subst,substArgs,Op.binders,liftSub] using typed.closed history
  exact LoanTyping.FoldUnrolling.unroll_preserves closed (observed.to_literal bound) bound i within

theorem LoanSourceTyped.loop_prefix_origin
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .loop count motive seed body)
    (observed : Numeric env (code.child count).origin n) (bound : n < 2^64)
    (i : Nat) (within : i ≤ n) :
    LoanTyping.HasType env [] [] true (LoanTyping.ProofLoop.unroll n (code.child seed).origin (code.child body).origin i)
      (.app (code.child motive).origin (.natural i)) := by
  have closed : LoanTyping.HasType env [] [] true
      (.loop (code.child count).origin (code.child motive).origin (code.child seed).origin (code.child body).origin) type := by
    simpa [Code.origin,Code.child,shape,Term.loop,Term.subst,substArgs,Op.binders,liftSub] using typed.closed history
  exact LoanTyping.ProofLoop.unroll_prefix_typed history.wellFormed closed (observed.to_literal bound) bound i within

end Jihoo.NativeKernel.Environment.BindingMachine
