import Jihoo.NativeBindingMachineMutableObservedUnsigned
import Jihoo.NativeBindingMachineMutableFreeContinuation

/-! The machine evaluates unsigned subtraction operands in order and
replays their heap events. The erased bound justifies the return step. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

open CodeKinds
open Semantics.LoanArithmetic (Numeric ObservedEvidence)

/-- When both actual operand visits return their interpreted words, the
complete source subtraction has the original result type. The only events
are those of the two operands in their evaluation order. -/
theorem checked_observed_usub_phases (program : Term) (ticks leftFuel rightFuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions declarations env)
    (typed : LoanClosingTyped env loans false code meanings type)
    (shape : code.term = .usub numerator denominator evidence)
    (proofObserved : ObservedEvidence env meanings evidence)
    (numeratorValue : Numeric env (numerator.subst meanings) left)
    (denominatorValue : Numeric env (denominator.subst meanings) right)
    (entry : (run ticks (initial program)).state.control = .evaluate code)
    (leftExecuted : let state := (run ticks (initial program)).state
      run leftFuel ⟨state.heap,.evaluate (code.child numerator),[],
          (.usubLeft (code.child denominator),state.stack) :: state.pending⟩ =
        ⟨⟨leftHeap,.returned (.natural left),[],
          (.usubLeft (code.child denominator),state.stack) :: state.pending⟩,leftEvents,leftSteps⟩)
    (rightExecuted : let state := (run ticks (initial program)).state
      run rightFuel ⟨leftHeap,.evaluate (code.child denominator),[],(.usubRight left,state.stack) :: state.pending⟩ =
        ⟨⟨rightHeap,.returned (.natural right),[],(.usubRight left,state.stack) :: state.pending⟩,rightEvents,rightSteps⟩) :
    let state := (run ticks (initial program)).state
    run (1+leftFuel+1+rightFuel+1) state =
      ⟨⟨rightHeap,.returned (.natural (left-right)),state.stack,state.pending⟩,
        leftEvents ++ rightEvents,1+leftSteps+1+rightSteps+1⟩ ∧
      LoanTyping.HasType env [] [] false (.natural (left-right)) type := by
  let state := (run ticks (initial program)).state
  let leftStart : State := ⟨state.heap,.evaluate (code.child numerator),[],
    (.usubLeft (code.child denominator),state.stack) :: state.pending⟩
  let leftReturn : State := ⟨leftHeap,.returned (.natural left),[],
    (.usubLeft (code.child denominator),state.stack) :: state.pending⟩
  let rightStart : State := ⟨leftHeap,.evaluate (code.child denominator),[],(.usubRight left,state.stack) :: state.pending⟩
  let rightReturn : State := ⟨rightHeap,.returned (.natural right),[],(.usubRight left,state.stack) :: state.pending⟩
  have entered : run 1 state = ⟨leftStart,[],1⟩ := by
    change state.control = _ at entry
    simp only [run,step,entry,shape,leftStart,Option.toList_none,List.nil_append,Nat.zero_add]
  have enteredRight : run 1 leftReturn = ⟨rightStart,[],1⟩ := by rfl
  change run leftFuel leftStart = ⟨leftReturn,leftEvents,leftSteps⟩ at leftExecuted
  change run rightFuel rightStart = ⟨rightReturn,rightEvents,rightSteps⟩ at rightExecuted
  have phases : run (1+leftFuel+1+rightFuel) state =
      ⟨rightReturn,leftEvents ++ rightEvents,1+leftSteps+1+rightSteps⟩ := by
    rw [run_add (1+leftFuel+1) rightFuel,run_add (1+leftFuel) 1,run_add 1 leftFuel,entered]
    dsimp only
    rw [leftExecuted,enteredRight]
    dsimp only
    rw [rightExecuted]
    simp only [List.nil_append,List.append_nil]
  let total := ticks+(1+leftFuel+1+rightFuel)
  have reached : (run total (initial program)).state = rightReturn := by
    change (run (ticks+(1+leftFuel+1+rightFuel)) (initial program)).state = rightReturn
    rw [run_add ticks (1+leftFuel+1+rightFuel)]
    change (run (1+leftFuel+1+rightFuel) state).state = rightReturn
    rw [phases]
  obtain ⟨finished,typedResult⟩ := checked_observed_usub_return program total history typed shape
    proofObserved numeratorValue denominatorValue (by rw [reached]) (by rw [reached])
    (saved := state.stack) (rest := state.pending) (by rw [reached])
  rw [reached] at finished
  have finishedRun : run 1 rightReturn =
      ⟨⟨rightHeap,.returned (.natural (left-right)),state.stack,state.pending⟩,[],1⟩ := by
    simp only [run,finished,rightReturn,Option.toList_none,List.nil_append,Nat.zero_add]
  refine ⟨?_,typedResult⟩
  rw [run_add,phases]
  dsimp only
  rw [finishedRun]
  simp only [List.append_nil]
  rfl

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
