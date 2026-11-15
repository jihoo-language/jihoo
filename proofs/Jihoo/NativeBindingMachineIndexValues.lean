import Jihoo.NativeBindingMachineNumeric
import Jihoo.NativeBindingMachineDynamicIndex
import Jihoo.NativeLoanTypeUniqueness

/-! Original-type interpretation of actual Index integers. Runtime numeric
bounds are derived from execution, and the full Loan64 input judgment supplies
result conversion. No caller-provided output typing or realization is used. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

theorem HasType.ifLt_index_result (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode
      (.ifLt left right (.index reference offset evidence) no) type) :
    Conversion.Conv env .i64 type := by
  obtain ⟨result,leftTyped,rightTyped,yesTyped,noTyped⟩ := typed.ifLt_inputs
  have rebuilt : HasType env loans ctx mode (.ifLt left right (.index reference offset evidence) no) result :=
    .ifLt leftTyped rightTyped yesTyped noTyped
  have original := rebuilt.unique wf typed
  have shifted : Conversion.Conv env .i64 (result.rename Nat.succ) := yesTyped.principalView
  have unshifted : Conversion.Conv env .i64 result := by
    simpa only [Term.shift_subst_single,Term.subst,substArgs] using
      shifted.substitution (single (.natural 0)) wf.closed
  exact unshifted.trans original

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine

theorem LoanSourceTyped.index_conversion
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .index reference offset evidence) : LoanTyping.Conversion.Conv env .i64 type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  have principal : LoanTyping.Conversion.Conv env .i64 localType := source.principalView
  have closed : LoanTyping.Conversion.Conv env .i64 (localType.subst code.origins) := by
    simpa only [Term.subst,substArgs] using principal.substitution code.origins history.wellFormed.closed
  exact closed.trans converted

theorem LoanSourceTyped.ifLt_index_conversion
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .ifLt left right (.index reference offset evidence) no) :
    LoanTyping.Conversion.Conv env .i64 type := by
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  have principal := source.ifLt_index_result history.wellFormed
  have closed : LoanTyping.Conversion.Conv env .i64 (localType.subst code.origins) := by
    simpa only [Term.subst,substArgs] using principal.substitution code.origins history.wellFormed.closed
  exact closed.trans converted

/-- Actual reachable heap contents construct a value at the input Index's
exact original closed type, with arbitrary result conversion and source bounds. -/
theorem reachable_index_integer_typed (term : Term) (fuel object : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .index reference offset evidence) :
    LoanTyping.HasType env [] [] true
      (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))) type :=
  (initial_run_decoded_integer_typed term fuel object).convert (typed.index_conversion history shape)

theorem reachable_ifLt_index_integer_typed (term : Term) (fuel object : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .ifLt left right (.index reference offset evidence) no) :
    LoanTyping.HasType env [] [] true
      (.integer (decodeInteger ((run fuel (initial term)).state.heap.heap.payload object))) type :=
  (initial_run_decoded_integer_typed term fuel object).convert (typed.ifLt_index_conversion history shape)

/-- A real pending read derives lease authority from the reachable reader
inventory. Its actual result has the exact input source type; an out-of-bounds
fault remains explicit until general proof/heap interpretation excludes it.
Neither a successful read nor output typing is a premise. -/
theorem reachable_pending_index (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .index reference offset evidence)
    (controlShape : (run fuel (initial term)).state.control = .returned (.natural index))
    (stackShape : (run fuel (initial term)).state.stack = .indexOffset token :: rest)
    (member : frame ∈ rest) (descriptor : frame.reader? = some (token,object,name)) :
    if index < (run fuel (initial term)).state.heap.length object then
      ∃ value : Int, LoanTyping.HasType env [] [] true (.integer value) type ∧
        step (run fuel (initial term)).state = some
          (⟨(run fuel (initial term)).state.heap,.returned (.integer value),rest⟩,
            some (.heap (.read token index ((run fuel (initial term)).state.heap.heap.payload object))))
    else step (run fuel (initial term)).state = some
      (⟨(run fuel (initial term)).state.heap,.fault .indexBounds,rest⟩,none) := by
  have readers := initial_run_readers_live term fuel
  have frameMember : frame ∈ (run fuel (initial term)).state.stack := by
    rw [stackShape]
    exact List.mem_cons_of_mem _ member
  have leased := readers frame frameMember token object name descriptor
  by_cases bound : index < (run fuel (initial term)).state.heap.length object
  · simp only [bound,↓reduceIte]
    refine ⟨_,reachable_index_integer_typed term fuel object history typed shape,?_⟩
    simp only [step,action,controlShape,stackShape,returnAction,Option.map_some,execute,leased,bound,ite_true]
  · simp only [bound,↓reduceIte]
    simp only [step,action,controlShape,stackShape,returnAction,Option.map_some,execute,leased,bound,ite_false]

end Jihoo.NativeKernel.Environment.BindingMachine
