import Jihoo.NativeBindingMachineReaderState
import Jihoo.NativeLoanPrincipalInversion

/-! Source-derived bounds for Decide evidence in the complete Loan64 judgment,
and actual reader reads from a concrete allocation state. General evidence
interpretation and preservation of source/control alignment remain open. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def DecideTruth (env : Environment) : Term → Prop
  | .decide left right => ∃ first second : Nat,
      Conversion.Conv env left (.natural first) ∧
      Conversion.Conv env right (.natural second) ∧ first < 2^64 ∧ second < 2^64 ∧ first < second
  | _ => True

private theorem decide_truth_rule (typed : HasType env loans ctx mode term type) : DecideTruth env term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ term _ _ => DecideTruth env term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case decide => exact ⟨_,_,.refl _,.refl _,by assumption,by assumption,by assumption⟩
  case decideConverted => exact ⟨_,_,by assumption,by assumption,by assumption,by assumption,by assumption⟩
  case dataElim => split <;> trivial

theorem HasType.decide_truth
    (typed : HasType env loans ctx mode (.decide left right) type) :
    ∃ first second : Nat, Conversion.Conv env left (.natural first) ∧
      Conversion.Conv env right (.natural second) ∧ first < 2^64 ∧ second < 2^64 ∧ first < second :=
  decide_truth_rule typed

/-- No truth certificate is supplied by the caller: actual Decide typing,
including its normalized-operand rule, supplies the strict numerical bound. -/
theorem HasType.literal_decide_limits (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.decide (.natural first) (.natural second)) type) :
    first < 2^64 ∧ second < 2^64 ∧ first < second := by
  obtain ⟨a,b,left,right,leftBound,rightBound,ordered⟩ := typed.decide_truth
  have sameLeft := left.natural_injective wf.admissible
  have sameRight := right.natural_injective wf.admissible
  exact ⟨by omega,by omega,by omega⟩

private def IndexInputs (env : Environment) (loans : Loans.Stack) (ctx : Context)
    (mode : Bool) : Term → Prop
  | .index reference offset evidence => ∃ count,
      (HasType env loans ctx mode reference (.array count) ∨
        HasType env loans ctx mode reference (.ref (.buffer count))) ∧
      HasType env loans ctx mode offset .u64 ∧ HasType env loans ctx true evidence (.lt offset count)
  | _ => True

private theorem index_inputs_rule (typed : HasType env loans ctx mode term type) :
    IndexInputs env loans ctx mode term := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun loans ctx mode term _ _ => IndexInputs env loans ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | assumption | skip
  case index => exact ⟨_,Or.inl (by assumption),by assumption,by assumption⟩
  case borrowedIndex => exact ⟨_,Or.inr (by assumption),by assumption,by assumption⟩
  case dataElim => split <;> trivial

theorem HasType.index_inputs
    (typed : HasType env loans ctx mode (.index reference offset evidence) type) :
    ∃ count,
      (HasType env loans ctx mode reference (.array count) ∨
        HasType env loans ctx mode reference (.ref (.buffer count))) ∧
      HasType env loans ctx mode offset .u64 ∧ HasType env loans ctx true evidence (.lt offset count) :=
  index_inputs_rule typed

theorem HasType.index_evidence
    (typed : HasType env loans ctx mode (.index reference offset evidence) type) :
    ∃ count, HasType env loans ctx true evidence (.lt offset count) := by
  obtain ⟨count,reference,index,evidence⟩ := typed.index_inputs
  exact ⟨count,evidence⟩

/-- Both array and borrowed-buffer Index rules expose the same erased source
bound evidence, including arbitrary conversion of the requested result type. -/
theorem HasType.literal_index_bound {index count : Nat} (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode
      (.index reference (.natural index) (.decide (.natural index) (.natural count))) type) :
    index < count := by
  obtain ⟨size,evidence⟩ := typed.index_evidence
  exact (evidence.literal_decide_limits wf).2.2

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine

/-- Exact allocation lengths survive every actual machine prefix, including
prefixes that return/fault or exhaust their fuel. -/
theorem run_allocation_length_valid (valid : SizedBufferHeap.Valid state.heap)
    (allocated : state.heap = SizedBufferHeap.allocate before count fill) (fuel : Nat) :
    (run fuel state).state.heap.length before.heap.nextObject = count := by
  have objectBound : before.heap.nextObject < state.heap.heap.nextObject := by
    simp only [allocated,SizedBufferHeap.allocate]
    omega
  have preserved := SizedBufferHeap.lengths_preserved objectBound (run_heap_steps valid fuel)
  rw [allocated,SizedBufferHeap.allocation_length] at preserved
  exact preserved.2

theorem run_allocation_length (valid : SizedBufferHeap.Valid before)
    (allocated : state.heap = SizedBufferHeap.allocate before count fill) (fuel : Nat) :
    (run fuel state).state.heap.length before.heap.nextObject = count := by
  apply run_allocation_length_valid (state := state) ?_ allocated fuel
  rw [allocated]
  exact SizedBufferHeap.step_valid valid .alloc

/-- A pending literal Index read derives its bound from full source typing,
its exact length from an allocation state and subsequent execution, and its live lease from the
reader inventory. No bound, successful-read or output-typing oracle is used.
The source/control/reader shapes are local inputs; a whole-typing invariant
must still construct these at every read in an admitted program. -/
theorem allocated_reader_index_step
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (valid : SizedBufferHeap.Valid before)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (allocated : state.heap = SizedBufferHeap.allocate before count fill) (fuel : Nat)
    (typed : LoanTyping.HasType env loans ctx false
      (.index reference (.natural index) (.decide (.natural index) (.natural count))) type)
    (controlShape : (run fuel state).state.control = .returned (.natural index))
    (stackShape : (run fuel state).state.stack = .indexOffset token :: rest)
    (member : frame ∈ rest) (descriptor : frame.reader? = some (token,before.heap.nextObject,name)) :
    step (run fuel state).state = some
      (⟨(run fuel state).state.heap,
        .returned (.integer (decodeInteger ((run fuel state).state.heap.heap.payload before.heap.nextObject))),rest⟩,
        some (.heap (.read token index ((run fuel state).state.heap.heap.payload before.heap.nextObject)))) := by
  have allocationValid : SizedBufferHeap.Valid state.heap := by
    rw [allocated]
    exact SizedBufferHeap.step_valid valid .alloc
  have readers := (run_reader_inventory allocationValid inventory fuel).readersLive
  have frameMember : frame ∈ (run fuel state).state.stack := by
    rw [stackShape]
    exact List.mem_cons_of_mem _ member
  have leased := readers frame frameMember token before.heap.nextObject name descriptor
  have bound : index < (run fuel state).state.heap.length before.heap.nextObject := by
    rw [run_allocation_length valid allocated fuel]
    exact typed.literal_index_bound history.wellFormed
  simp only [step,action,controlShape,stackShape,returnAction,Option.map_some,execute,leased,bound,ite_true]

private theorem named_index_five_steps (heap : SizedBufferHeap.State) (code : Code) (stack : List Frame)
    (shape : code.term = .index (.borrow (.var owner)) (.natural offset) evidence)
    (stored : code.values[owner]? = some (some (.owner object)))
    (found : activeLease (code.context.length-owner) object stack = some token)
    (leased : heap.heap.lease token = some object)
    (literalBound : offset < 2^64) (readBound : offset < heap.length object) :
    run 5 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨heap,.returned (.integer (decodeInteger (heap.heap.payload object))),stack⟩,
        [.heap (.read token offset (heap.heap.payload object))],5⟩ := by
  simp only [run,step,action,evaluateAction,shape,Code.child,stored,returnAction,execute,
    literalBound,readBound,leased,ite_true,Option.map_some,borrowLease,Option.orElse_some,activeLease,readerFor,Frame.reader?,
    bind,Option.bind,Option.orElse_none,found]
  rfl

/-- The complete five-transition source Index execution follows from its full
Loan64 derivation, owner-slot permissions, and a concrete allocation state.
The erased literal Decide supplies both numerical bounds. The runtime owner
slot's allocation identity and source/slot alignment remain explicit inputs,
not a claimed whole-program fundamental theorem. -/
theorem allocated_named_index_executes_valid
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (valid : SizedBufferHeap.Valid state.heap)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (allocated : state.heap = SizedBufferHeap.allocate before count fill) (fuel : Nat)
    (evaluating : (run fuel state).state.control = .evaluate code)
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .index (.borrow (.var owner)) (.natural offset)
      (.decide (.natural offset) (.natural count)))
    (slots : LoanSlots code loans (run fuel state).state.stack)
    (stored : code.values[owner]? = some (some (.owner before.heap.nextObject))) :
    ∃ token,
      run 5 (run fuel state).state =
        ⟨⟨(run fuel state).state.heap,
          .returned (.integer (decodeInteger ((run fuel state).state.heap.heap.payload before.heap.nextObject))),
          (run fuel state).state.stack⟩,
          [.heap (.read token offset ((run fuel state).state.heap.heap.payload before.heap.nextObject))],5⟩ := by
  have source := typed
  rw [shape] at source
  obtain ⟨size,reference,offsetTyped,evidence⟩ := source.index_inputs
  have permission : Loans.active code.context.length loans owner = true := by
    rcases reference with reference | reference
    all_goals simpa only [LoanTyping.BorrowPermission,Loans.borrowAllowed,Bool.false_or]
      using reference.borrow_permission
  obtain ⟨object,slot,present⟩ := slots owner permission
  rw [stored] at slot
  cases slot
  obtain ⟨token,found⟩ := activeLease_complete present
  obtain ⟨frame,member,descriptor⟩ := activeLease_sound found
  have readers := (run_reader_inventory valid inventory fuel).readersLive
  have leased := readers frame member token before.heap.nextObject
    (some (code.context.length-owner)) descriptor
  have limits := evidence.literal_decide_limits history.wellFormed
  have readBound : offset < (run fuel state).state.heap.length before.heap.nextObject := by
    rw [run_allocation_length_valid valid allocated fuel]
    exact limits.2.2
  refine ⟨token,?_⟩
  have stateShape : (run fuel state).state =
      ⟨(run fuel state).state.heap,.evaluate code,(run fuel state).state.stack⟩ := by
    cases current : (run fuel state).state with
    | mk heap control stack => simpa only [current] using congrArg (State.mk heap · stack) evaluating
  rw [stateShape]
  exact named_index_five_steps _ code _ shape stored found leased limits.1 readBound

theorem allocated_named_index_executes
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (valid : SizedBufferHeap.Valid before)
    (inventory : ReaderInventory state.heap (readerFrames state.stack))
    (allocated : state.heap = SizedBufferHeap.allocate before count fill) (fuel : Nat)
    (evaluating : (run fuel state).state.control = .evaluate code)
    (typed : LoanTyping.HasType env loans code.context false code.term type)
    (shape : code.term = .index (.borrow (.var owner)) (.natural offset)
      (.decide (.natural offset) (.natural count)))
    (slots : LoanSlots code loans (run fuel state).state.stack)
    (stored : code.values[owner]? = some (some (.owner before.heap.nextObject))) :
    ∃ token,
      run 5 (run fuel state).state =
        ⟨⟨(run fuel state).state.heap,
          .returned (.integer (decodeInteger ((run fuel state).state.heap.heap.payload before.heap.nextObject))),
          (run fuel state).state.stack⟩,
          [.heap (.read token offset ((run fuel state).state.heap.heap.payload before.heap.nextObject))],5⟩ := by
  apply allocated_named_index_executes_valid history ?_ inventory allocated fuel evaluating typed shape slots stored
  rw [allocated]
  exact SizedBufferHeap.step_valid valid .alloc

end Jihoo.NativeKernel.Environment.BindingMachine
