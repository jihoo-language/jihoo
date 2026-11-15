import Jihoo.NativeBindingMachineAlignment
import Jihoo.NativeBindingMachineIndexBounds

/-! Actual comparison-guarded dynamic Index, with the full Loan64 input
judgment and retained runtime scalar/owner slots. The numerical read guard is
derived from the selected branch; general state interpretation remains open. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def LessInputs (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Prop
  | .ifLt left right yes no => ∃ result,
      HasType env loans ctx mode left .u64 ∧ HasType env loans ctx mode right .u64 ∧
      HasType env loans (⟨.lt left right,true⟩ :: ctx) mode yes (result.rename Nat.succ) ∧
      HasType env loans ctx mode no result
  | _ => True

private theorem less_inputs_rule (typed : HasType env loans ctx mode term type) :
    LessInputs env loans ctx mode term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun loans ctx mode term _ _ => LessInputs env loans ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case ifLt => exact ⟨_,by assumption,by assumption,by assumption,by assumption⟩
  case dataElim => split <;> trivial

theorem HasType.ifLt_inputs
    (typed : HasType env loans ctx mode (.ifLt left right yes no) type) :
    ∃ result,
      HasType env loans ctx mode left .u64 ∧ HasType env loans ctx mode right .u64 ∧
      HasType env loans (⟨.lt left right,true⟩ :: ctx) mode yes (result.rename Nat.succ) ∧
      HasType env loans ctx mode no result := less_inputs_rule typed

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- The source yes-arm uses the actual erased comparison hypothesis, and its
runtime index and named owner retain their original slots below that binder. -/
def dynamicRead (owner index : Nat) : Term :=
  .index (.borrow (.var (owner+1))) (.var (index+1)) (.var 0)

private theorem guarded_read_ten_steps (heap : SizedBufferHeap.State) (code : Code) (stack : List Frame)
    (shape : code.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (storedOwner : code.values[owner]? = some (some (.owner object)))
    (found : activeLease (code.context.length-owner) object stack = some token)
    (leased : heap.heap.lease token = some object) (size : heap.length object = count)
    (compared : offset < count) :
    run 10 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),stack⟩,
        [.heap (.read token offset (heap.heap.payload object))],10⟩ := by
  simp only [run,step,action,evaluateAction,shape,Code.child,storedIndex,storedLength,storedOwner,
    returnAction,execute,branchCode,dynamicRead,List.getElem?_cons_succ,List.length_cons,
    Nat.add_sub_add_right,activeLease,readerFor,Frame.reader?,bind,Option.bind,Option.orElse_none,
    found,leased,size,compared,decide_true,Bool.false_eq_true,↓reduceIte,Option.map_some]
  rfl

private theorem guarded_read_else_five_steps (heap : SizedBufferHeap.State) (code : Code) (stack : List Frame)
    (shape : code.term = .ifLt (.var index) (.var length) yes no)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count))) (compared : ¬ offset < count) :
    run 5 ⟨heap,.evaluate code,stack⟩ = ⟨⟨heap,.evaluate (code.child no),stack⟩,[],5⟩ := by
  simp only [run,step,action,evaluateAction,shape,Code.child,storedIndex,storedLength,
    returnAction,execute,compared,decide_false,Bool.false_eq_true,↓reduceIte,Option.map_some]
  rfl

/-- Complete source typing supplies named Borrow permission under the erased
comparison binder; the original slot has the same permission before entry. -/
theorem typed_dynamic_read_permission {code : Code}
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no)
    (entered : Loans.Entered code.context.length loans) :
    Loans.active code.context.length loans owner = true := by
  rw [shape] at typed
  obtain ⟨result,left,right,yes,no⟩ := typed.ifLt_inputs
  obtain ⟨count,reference,indexTyped,evidence⟩ := yes.index_inputs
  have permission : Loans.active (code.context.length+1) loans (owner+1) = true := by
    rcases reference with reference | reference
    all_goals simpa only [dynamicRead,LoanTyping.BorrowPermission,Loans.borrowAllowed,
      Bool.false_or,List.length_cons] using reference.borrow_permission
  simpa only [Loans.active_weaken entered] using permission

/-- Dynamic scalar slots select the branch. In the yes branch, full source
Borrow permission, exact allocation length and the real reader inventory
construct the entire read. Neither a numerical bound nor successful execution
is a premise. Allocation/slot and source-control association are still local
entry invariants to derive in the whole-program fundamental theorem. -/
theorem allocated_dynamic_index_executes
    (valid : SizedBufferHeap.Valid before)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (allocated : state.heap = SizedBufferHeap.allocate before count fill) (fuel : Nat)
    (code : Code) (evaluating : (run fuel state).state.control = .evaluate code)
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .ifLt (.var index) (.var length) (dynamicRead owner index) no)
    (entered : Loans.Entered code.context.length loans)
    (slots : LoanSlots code loans (run fuel state).state.stack)
    (storedIndex : code.values[index]? = some (some (.natural offset)))
    (storedLength : code.values[length]? = some (some (.natural count)))
    (storedOwner : code.values[owner]? = some (some (.owner before.heap.nextObject))) :
    if offset < count then
      ∃ token, run 10 (run fuel state).state =
        ⟨⟨(run fuel state).state.heap,
          .returned (.integer (decodeInteger ((run fuel state).state.heap.heap.payload before.heap.nextObject))),
          (run fuel state).state.stack⟩,
          [.heap (.read token offset ((run fuel state).state.heap.heap.payload before.heap.nextObject))],10⟩
    else run 5 (run fuel state).state =
      ⟨⟨(run fuel state).state.heap,.evaluate (code.child no),(run fuel state).state.stack⟩,[],5⟩ := by
  have stateShape : (run fuel state).state =
      ⟨(run fuel state).state.heap,.evaluate code,(run fuel state).state.stack⟩ := by
    cases current : (run fuel state).state with
    | mk heap control stack => simpa only [current] using congrArg (State.mk heap · stack) evaluating
  by_cases compared : offset < count
  · simp only [compared,↓reduceIte]
    have permission := typed_dynamic_read_permission typed shape entered
    obtain ⟨object,stored,present⟩ := slots owner permission
    rw [storedOwner] at stored
    cases stored
    obtain ⟨token,found⟩ := activeLease_complete present
    obtain ⟨frame,member,descriptor⟩ := activeLease_sound found
    have allocationValid : SizedBufferHeap.Valid state.heap := by
      rw [allocated]
      exact SizedBufferHeap.step_valid valid .alloc
    have readers := (run_reader_inventory allocationValid inventory fuel).readersLive
    have leased := readers frame member token before.heap.nextObject
      (some (code.context.length-owner)) descriptor
    refine ⟨token,?_⟩
    rw [stateShape]
    exact guarded_read_ten_steps _ code _ shape storedIndex storedLength storedOwner found leased
      (run_allocation_length valid allocated fuel) compared
  · simp only [compared,↓reduceIte]
    rw [stateShape]
    exact guarded_read_else_five_steps _ code _ shape storedIndex storedLength compared

end Jihoo.NativeKernel.Environment.BindingMachine
