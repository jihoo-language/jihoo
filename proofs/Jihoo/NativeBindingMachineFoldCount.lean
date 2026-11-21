import Jihoo.NativeBindingMachineIterationDemand
import Jihoo.NativeBindingMachineMutableLoanedArithmeticProgress
import Jihoo.NativeLoanFoldUnrolling

/-! The actual Fold typing and resource projection determine the count
operand. The existing binding machine evaluates a checked word expression
into a numeral without changing captured owners or pending frames. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open Jihoo.Quantity NativeQuantity
open LoanTyping.ResourceQuantity (projectRaw fold_receipts)

private theorem same_captures (operand : UnsignedOperand) :
    operand.CapturesMatch code code id := by
  induction operand with
  | literal => trivial
  | captured => rfl
  | add _ _ first second => exact ⟨first,second⟩

/-- A supported computed count with representable unsigned sums reaches
its numeral under the original Fold's source and resource checks. The
numeric value and the empty event prefix follow from that execution. -/
theorem checked_fold_count (operand : UnsignedOperand)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (shape : code.term = .fold operand.term seed callback)
    (typed : LoanClosingTyped env loans false code meanings type)
    (context : ValueContext env code meanings) (aligned : CodeAligned code)
    (checked : projectRaw (fuel+1) env loans code.context code.term = some receipt)
    (bounded : operand.SumsFit meanings) :
    let number := operand.sum meanings
    number < 2^64 ∧
      LoanTyping.Conversion.Conv env (operand.term.subst meanings) (.natural number) ∧
      ∀ (heap : SizedBufferHeap.IndexedState) (stack : List Frame) (pending : List (BufferFrame × List Frame)),
        run operand.ticks ⟨heap,.evaluate (code.child operand.term),stack,pending⟩ =
          ⟨⟨heap,.returned (.natural number),stack,pending⟩,[],operand.ticks⟩ := by
  obtain ⟨closing,_,source,_⟩ := typed
  rw [shape] at source checked
  obtain ⟨_,count,_,_,_⟩ := LoanTyping.FoldUnrolling.fold_inputs source
  have closedCount : LoanClosingTyped env loans false (code.child operand.term) meanings .u64 := by
    refine ⟨closing,.u64,count,?_⟩
    simp only [Term.subst,substArgs]
    exact .refl _
  obtain ⟨setup,_,setupChecked,_,_⟩ := fold_receipts checked
  simp only [fields,fetch,List.getElem?_cons_zero,Option.bind_some] at setupChecked
  obtain ⟨countReceipt,countChecked,_⟩ := Option.bind_eq_some_iff.mp setupChecked
  have observed := operand.checked_value history count context aligned bounded
  obtain ⟨range,converted,_,ran⟩ := operand.checked_run_captures (indices := id) (actual := code) (source := code)
    history (same_captures operand) (by simpa only [Term.rename_id] using closedCount) context aligned
    (by simpa only [Term.rename_id] using countChecked) (by simpa only [Function.comp_id] using observed)
  exact ⟨range,by simpa only [Term.rename_id] using converted,ran⟩

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
