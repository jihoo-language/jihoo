import Jihoo.NativeBindingMachineOwnerProvenance
import Jihoo.NativeBindingMachineOwnedReaderExecution
import Jihoo.NativeBindingMachineLendValues

/-! A fresh owned reader result is retained by the outer continuation, lent
again, and read through a real named Borrow. Source Loan64 typing supplies
Index bounds; actual allocation supplies the concrete identity and length.
The general admission/control/value/resource fundamental theorem remains open. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine
open CodeKinds
variable {control : Jihoo.Quantity.Control}

/-- The outer continuation retains owner/result slots zero/one. The inner
reader retains its reference binder and borrows that same result at slot two. -/
def returnedBufferRead (domain : Term) (offset count : Nat) (first again body : Term) : Term :=
  .lend (.var 1)
    (.lam false domain (.index (.borrow (.var 2)) (.natural offset) (.decide (.natural offset) (.natural count))))
    (.lam false first (.lam false again body))

/-- The full input derivation, including specialized callbacks and arbitrary
result conversions, supplies all literal widths and the actual inner reader's
bound/type. No generic callback, output typing or true-evidence oracle is an
input. The heap/value association is constructed by the execution theorem. -/
theorem LoanSourceTyped.returned_read_limits
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans mode code type)
    (shape : code.term = .lend owner (.lam false domain (.alloc (.natural count) (.integer fill)))
      (.lam false first (.lam false again (returnedBufferRead readDomain offset count innerFirst innerAgain innerBody)))) :
    count < 2^64 ∧ ValueReduction.signed64 fill ∧ offset < 2^64 ∧ offset < count ∧
      ∃ readerType, LoanTyping.Outlived env readerType ∧
        LoanTyping.HasType env [] [] true
          (.index (.borrow (.alloc (.natural count) (.integer fill))) (.natural offset)
            (.decide (.natural offset) (.natural count))) readerType ∧
        LoanTyping.HasType env [] [] true (.integer fill) readerType := by
  obtain ⟨allocationType,allocationTyped,allocationOutlived⟩ := typed_explicit_reader_origin history typed shape 0
  have allocation : LoanTyping.HasType env [] [] true (.alloc (.natural count) (.integer fill))
      (allocationType.subst code.origins) := by
    simpa only [Code.origin,enter,Term.subst,substArgs,Op.binders,liftSub] using allocationTyped
  have countBound := allocation.alloc_inputs.1.natural_bound
  have fillBound := allocation.alloc_inputs.2.integer_bound
  have nested := typed_explicit_continuation_origin history typed shape 0 (.owner 0)
  simp only [Code.origin,enter,returnedBufferRead,Term.subst,substArgs,Op.binders,liftSub] at nested
  obtain ⟨ownerType,readerType,ownerTyped,owned,readTyped,outlived⟩ :=
    nested.explicitLendInputs history.wellFormed
  simp only [Lending.read,Term.subst,substArgs,Op.binders,liftSub] at readTyped
  have bound := readTyped.literal_index_bound history.wellFormed
  obtain ⟨size,referenceTyped,indexTyped,evidenceTyped⟩ := readTyped.index_inputs
  have indexBound := indexTyped.natural_bound
  have converted : LoanTyping.Conversion.Conv env .i64 readerType := readTyped.principalView
  exact ⟨countBound,fillBound,indexBound,bound,readerType,outlived,
    by simpa only [Term.subst,substArgs,Op.binders,liftSub,consValues,liftSubOne,single,
      Term.rename,renameArgs,liftRenaming] using readTyped,
    (LoanTyping.HasType.integer fillBound.1 fillBound.2).convert converted⟩

set_option linter.unusedSimpArgs false in
private theorem allocating_reader_suffix (heap : SizedBufferHeap.State) (code : Code)
    (shape : code.term = .alloc (.natural count) (.integer fill))
    (countBound : count < 2^64) (fillBound : ValueReduction.signed64 fill)
    (fits : count*8+8 < 2^64) (stack : List Frame) (fuel : Nat) :
    run (fuel+5) ⟨heap,.evaluate code,stack⟩ =
      let result := run fuel ⟨SizedBufferHeap.allocate heap count (encodeInteger fill),
        .returned (.owner heap.heap.nextObject),stack⟩
      ⟨result.state,.heap (.alloc heap.heap.nextObject count (encodeInteger fill)) :: result.events,result.steps+5⟩ := by
  simp only [run,step,action,evaluateAction,shape,returnAction,execute,Code.child,
    countBound,fillBound,fits,↓reduceIte,Option.map_some]
  rfl

set_option linter.unusedSimpArgs false in
private theorem close_continue_suffix (heap : SizedBufferHeap.State) (code : Code)
    (leased : heap.heap.lease token = some object)
    (first again body ownerOrigin resultOrigin : Term) (result : Value) (name : Option Nat)
    (stack : List Frame) (fuel : Nat) :
    run (fuel+5) ⟨heap,.returned result,
      .lendFinish token object name ownerOrigin resultOrigin
        (code.child (.lam false first (.lam false again body))) :: stack⟩ =
      let rest := run fuel ⟨SizedBufferHeap.close heap token,
        .evaluate (restoredContinuation code first again body ownerOrigin resultOrigin object result),stack⟩
      ⟨rest.state,[.heap (.close token),.activate false (.lam false again body) resultOrigin,
        .activate false body ownerOrigin] ++ rest.events,rest.steps+5⟩ := by
  simp only [run,step,action,returnAction,execute,leased,↓reduceIte,evaluateAction,
    Code.child,applyValue,enter,restoredContinuation,Option.map_some]
  rfl

def returnedIndexCode (code : Code) (readDomain : Term) (offset count token : Nat) : Code :=
  enter false readDomain (.index (.borrow (.var 2)) (.natural offset) (.decide (.natural offset) (.natural count)))
    code.context code.origins code.values (.borrow ((Term.var 1).subst code.origins)) (some (.reference token))

/-- Ghost metadata agrees with the original allocating reader; the machine
retains both closures and never executes this substituted origin as CODE. -/
theorem returned_allocated_index_origin (code : Code) (domain first again body ownerOrigin readDomain : Term)
    (count offset oldObject fresh oldToken nextToken : Nat) (fill : Int) :
    (returnedIndexCode (restoredContinuation code first again body ownerOrigin
      (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
        (.borrow ownerOrigin) (some (.reference oldToken))).origin oldObject (.owner fresh))
      readDomain offset count nextToken).origin =
      .index (.borrow (.alloc (.natural count) (.integer fill))) (.natural offset)
        (.decide (.natural offset) (.natural count)) := by
  simp only [returnedIndexCode,restoredContinuation,Code.origin,enter,Term.subst,substArgs,
    Op.binders,liftSub,consValues]

set_option linter.unusedSimpArgs false in
private theorem lend_result_index_ten_steps (heap : SizedBufferHeap.State) (code : Code)
    (shape : code.term = returnedBufferRead readDomain offset count first again body)
    (stored : code.values[1]? = some (some (.owner object)))
    (live : heap.heap.live object = true) (size : heap.length object = count)
    (indexBound : offset < 2^64) (bound : offset < count) (stack : List Frame) :
    run 10 ⟨heap,.evaluate code,stack⟩ =
      ⟨⟨SizedBufferHeap.lend heap object,.returned (.integer (decodeInteger (heap.heap.payload object))),
        .lendFinish heap.heap.nextLease object (some (code.context.length-1))
          ((Term.var 1).subst code.origins) (returnedIndexCode code readDomain offset count heap.heap.nextLease).origin
          (code.child (.lam false first (.lam false again body))) :: stack⟩,
        [.heap (.beginLease heap.heap.nextLease object),
          .activate false (.index (.borrow (.var 2)) (.natural offset) (.decide (.natural offset) (.natural count)))
            (.borrow ((Term.var 1).subst code.origins)),
          .heap (.read heap.heap.nextLease offset (heap.heap.payload object))],10⟩ := by
  have key : code.context.length+1-2 = code.context.length-1 := by omega
  simp only [run,step,action,evaluateAction,shape,returnedBufferRead,returnAction,execute,Code.child,
    applyValue,enter,returnedIndexCode,stored,live,indexBound,SizedBufferHeap.lend,HeapLeases.put,
    List.getElem?_cons_succ,List.getElem?_cons_zero,List.length_cons,key,
    activeLease,readerFor,Frame.reader?,bind,Option.bind,Option.orElse_none,Option.orElse_some,and_true,
    size,bound,↓reduceIte,Option.map_some]
  rfl

/-- Compose actual allocation, outer continuation bindings, a new Lend and a
named Borrow/Index. Every read guard and the fresh-result slot are constructed;
the actual resource check supplies the declared Buffer interpretation. The
current source/control/reader association remains a local premise. -/
theorem reachable_returned_buffer_read (term : Term) (fuel : Nat) (code : Code)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanSourceTyped env loans false code type)
    (shape : code.term = .lend (.var owner) (.lam false domain (.alloc (.natural count) (.integer fill)))
      (.lam false (.buffer size) (.lam false again
        (returnedBufferRead readDomain offset count innerFirst innerAgain innerBody))))
    (checked : LoanTyping.ResourceQuantity.project (resourceFuel+1) env loans code.context code.term = some control)
    (evaluating : (run fuel (initial term)).state.control = .evaluate
      (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name ((Term.var owner).subst code.origins)
        (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
          (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
        (code.child (.lam false (.buffer size) (.lam false again
          (returnedBufferRead readDomain offset count innerFirst innerAgain innerBody)))) :: stack) :
    let heap := (run fuel (initial term)).state.heap
    let fresh := heap.heap.nextObject
    let nextToken := heap.heap.nextLease
    let allocated := SizedBufferHeap.allocate heap count (encodeInteger fill)
    let closed := SizedBufferHeap.close allocated token
    let body := returnedBufferRead readDomain offset count innerFirst innerAgain innerBody
    let ownerOrigin := (Term.var owner).subst code.origins
    let resultOrigin := (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
      (.borrow ownerOrigin) (some (.reference token))).origin
    let bodyCode := restoredContinuation code (.buffer size) again body ownerOrigin resultOrigin object (.owner fresh)
    let indexCode := returnedIndexCode bodyCode readDomain offset count nextToken
    ∃ readerType, LoanTyping.Outlived env readerType ∧
      LoanTyping.HasType env [] [] true (.integer fill) readerType ∧ fresh ≠ object ∧
      if count*8+8 < 2^64 then
        BufferValue env allocated (.owner fresh) ((Term.buffer size).subst code.origins) ∧
        LoanTyping.HasType env [] [] true indexCode.origin readerType ∧
        nextToken ≠ token ∧
        (SizedBufferHeap.lend closed fresh).heap.lease token = none ∧
        (SizedBufferHeap.lend closed fresh).heap.lease nextToken = some fresh ∧
        run 20 (run fuel (initial term)).state =
          ⟨⟨SizedBufferHeap.lend closed fresh,.returned (.integer fill),
            .lendFinish nextToken fresh (some (bodyCode.context.length-1))
              ((Term.var 1).subst bodyCode.origins) indexCode.origin
              (bodyCode.child (.lam false innerFirst (.lam false innerAgain innerBody))) :: stack⟩,
            [.heap (.alloc fresh count (encodeInteger fill)),.heap (.close token),
              .activate false (.lam false again body) resultOrigin,.activate false body ownerOrigin,
              .heap (.beginLease nextToken fresh),
              .activate false (.index (.borrow (.var 2)) (.natural offset) (.decide (.natural offset) (.natural count)))
                (.borrow ((Term.var 1).subst bodyCode.origins)),
              .heap (.read nextToken offset (encodeInteger fill))],20⟩
      else run 5 (run fuel (initial term)).state =
        ⟨⟨heap,.fault .allocationOverflow,(run fuel (initial term)).state.stack⟩,[],5⟩ := by
  obtain ⟨countBound,fillBound,indexBound,bound,readerType,outlived,originTyped,valueTyped⟩ := typed.returned_read_limits history shape
  have inputs := typed.allocating_first history shape checked
  have inventory := initial_reader_inventory term fuel
  rw [stackShape] at inventory
  change ReaderInventory _ ((token,object,name) :: readerFrames stack) at inventory
  have leased := inventory.live _ List.mem_cons_self
  have valid := initial_run_heap_valid term fuel
  have fresh := allocated_reader_fresh valid leased count (encodeInteger fill)
  have different : (run fuel (initial term)).state.heap.heap.nextLease ≠ token := by
    have earlier := (valid.leased token object leased).1
    omega
  refine ⟨readerType,outlived,valueTyped,fresh.1,?_⟩
  by_cases fits : count*8+8 < 2^64
  · simp only [fits,↓reduceIte]
    refine ⟨BufferValue.allocate inputs.2.2,?_,different,?_,?_,?_⟩
    · rw [returned_allocated_index_origin]
      exact originTyped
    · simp [SizedBufferHeap.lend,SizedBufferHeap.close,SizedBufferHeap.allocate,HeapLeases.put,Ne.symm different]
    · simp [SizedBufferHeap.lend,SizedBufferHeap.close,SizedBufferHeap.allocate,HeapLeases.put]
    · let readerCode := enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
        (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))
      let allocated := SizedBufferHeap.allocate (run fuel (initial term)).state.heap count (encodeInteger fill)
      let closed := SizedBufferHeap.close allocated token
      let body := returnedBufferRead readDomain offset count innerFirst innerAgain innerBody
      let bodyCode := restoredContinuation code (.buffer size) again body ((Term.var owner).subst code.origins)
        readerCode.origin object (.owner (run fuel (initial term)).state.heap.heap.nextObject)
      have live : closed.heap.live (run fuel (initial term)).state.heap.heap.nextObject = true := by
        simp [closed,allocated,SizedBufferHeap.close,SizedBufferHeap.allocate,HeapLeases.put]
      have length : closed.length (run fuel (initial term)).state.heap.heap.nextObject = count :=
        SizedBufferHeap.allocation_length (v := encodeInteger fill)
      have payload : closed.heap.payload (run fuel (initial term)).state.heap.heap.nextObject = encodeInteger fill := by
        simp [closed,allocated,SizedBufferHeap.close,SizedBufferHeap.allocate,HeapLeases.put]
      have ten := lend_result_index_ten_steps closed bodyCode rfl rfl live length indexBound bound stack
      simp only [payload,encode_decode_integer fillBound] at ten
      have fifteen := close_continue_suffix allocated code leased (.buffer size) again body
        ((Term.var owner).subst code.origins) readerCode.origin
        (.owner (run fuel (initial term)).state.heap.heap.nextObject) name stack 10
      rw [ten] at fifteen
      have executed := allocating_reader_suffix (run fuel (initial term)).state.heap readerCode rfl countBound fillBound fits
        (run fuel (initial term)).state.stack 15
      rw [stackShape,fifteen] at executed
      have stateShape : (run fuel (initial term)).state =
          ⟨(run fuel (initial term)).state.heap,.evaluate readerCode,
            .lendFinish token object name ((Term.var owner).subst code.origins)
              (enter false domain (.alloc (.natural count) (.integer fill)) code.context code.origins code.values
                (.borrow ((Term.var owner).subst code.origins)) (some (.reference token))).origin
              (code.child (.lam false (.buffer size) (.lam false again
                (returnedBufferRead readDomain offset count innerFirst innerAgain innerBody)))) :: stack⟩ := by
        cases state : (run fuel (initial term)).state
        simp_all [readerCode]
      dsimp only at executed
      rw [← stateShape] at executed
      exact executed
  · simp only [fits,↓reduceIte]
    obtain ⟨allocationType,allocationOutlived,sourceCount,sourceFill,other,executed⟩ :=
      reachable_allocating_reader term fuel code history typed shape evaluating stackShape
    simpa only [fits,↓reduceIte] using executed

end Jihoo.NativeKernel.Environment.BindingMachine
