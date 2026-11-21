import Jihoo.NativeLoanNumericalEvidence
import Jihoo.NativeBindingMachineMutableUnsignedSubtraction
import Jihoo.NativeBindingMachineMutableNumeric

/-! Interpreted numeric observations connect Loan64's original unsigned
subtraction bound to the actual machine return frame. -/

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open Semantics.LoanArithmetic (Numeric Order ObservedEvidence observed_evidence_order)
open CodeKinds

/-- At the existing subtraction return frame, the original erased proof
and the observed operand values rule out underflow. The frame installs the
result at the original closed source type and restores the saved stack. -/
theorem checked_observed_usub_return (program : Term) (ticks : Nat)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .usub numerator denominator evidence)
    (proofObserved : ObservedEvidence env meanings evidence)
    (numeratorValue : Numeric env (numerator.subst meanings) left)
    (denominatorValue : Numeric env (denominator.subst meanings) right)
    (returning : (run ticks (initial program)).state.control = .returned (.natural right))
    (noTemporary : (run ticks (initial program)).state.stack = [])
    (waitingRight : (run ticks (initial program)).state.pending = (.usubRight left,saved) :: rest) :
    let state := (run ticks (initial program)).state
    step state = some (⟨state.heap,.returned (.natural (left-right)),saved,rest⟩,none) ∧
      LoanTyping.HasType env [] [] false (.natural (left-right)) type := by
  obtain ⟨_,_,source,converted⟩ := typed
  rw [shape] at source
  have evidenceTyped := source.usub_inputs.2.2
  have interpreted : Order env (.lt (denominator.subst meanings) (.uadd (numerator.subst meanings) (.natural 1))) := by
    simpa only [Term.lt,Term.uadd,Term.natural,Term.subst,substArgs,Op.binders,liftSub] using
      observed_evidence_order history.wellFormed evidenceTyped proofObserved
  have ordered := interpreted.reflect history.wellFormed.admissible denominatorValue
    (numeratorValue.add (Numeric.natural env 1))
  have safe : right ≤ left := by omega
  have pending := (initial_run_numbers program ticks).pending
  rw [waitingRight] at pending
  have leftBound : left < 2^64 := (pending _ List.mem_cons_self).1
  have inferred : LoanTyping.Conversion.Conv env .u64 type := by
    simpa only [Term.subst,substArgs] using
      (source.principalView.substitution meanings history.wellFormed.closed).trans converted
  refine ⟨?_,(LoanTyping.HasType.natural (Nat.lt_of_le_of_lt (Nat.sub_le _ _) leftBound)).convert inferred⟩
  simp only [step,returning,noTemporary,returnAction,waitingRight,resumeBuffer,ite_eq_left safe]

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
