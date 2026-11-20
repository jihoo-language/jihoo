import Jihoo.NativeBindingMachineMutableComputedReaderClose

/-! Independent traces for signed reader expressions. A trace records the
executed read events and the precise residue of the arithmetic stack on
overflow, so an unsuccessful left operand prevents every right-side read. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

inductive ArithmeticReader where
  | literal (number : Int)
  | read (offset count : Nat)
  | arithmetic (op : Arith) (left right : ArithmeticReader)

namespace ArithmeticReader

def term : ArithmeticReader → Term
  | .literal number => .integer number
  | .read offset count => .index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))
  | .arithmetic op left right => .arith op left.term right.term

def Ready (length : Nat) : ArithmeticReader → Prop
  | .literal number => ValueReduction.signed64 number
  | .read offset _ => offset < 2^64 ∧ offset < length
  | .arithmetic _ left right => left.Ready length ∧ right.Ready length

inductive Outcome where
  | integer (number : Int)
  | overflow (remaining : List Frame)

structure Trace where
  outcome : Outcome
  events : List Event
  ticks : Nat

def Trace.result (trace : Trace) (heap : SizedBufferHeap.IndexedState) (stack : List Frame)
    (pending : List (BufferFrame × List Frame)) : Result :=
  let state : State := match trace.outcome with
    | .integer number => ⟨heap,.returned (.integer number),stack,pending⟩
    | .overflow remaining => ⟨heap,.fault .arithmeticOverflow,remaining,pending⟩
  ⟨state,trace.events,trace.ticks⟩

def replay (code : Code) (heap : SizedBufferHeap.IndexedState) (token object : Nat) :
    ArithmeticReader → List Frame → Trace
  | .literal number, _ => ⟨.integer number,[],1⟩
  | .read offset _, _ =>
      let payload := heap.cell object offset
      ⟨.integer (decodeInteger payload),[.legacy (.heap (.read token offset payload))],5⟩
  | .arithmetic op left right, stack =>
      let leftTrace := replay code heap token object left (.arithmeticLeft op (code.child right.term) :: stack)
      match leftTrace.outcome with
      | .overflow _ => { leftTrace with ticks := leftTrace.ticks+1 }
      | .integer leftValue =>
          let rightTrace := replay code heap token object right (.arithmeticRight op leftValue :: stack)
          let events := leftTrace.events ++ rightTrace.events
          match rightTrace.outcome with
          | .overflow _ => ⟨rightTrace.outcome,events,leftTrace.ticks+(rightTrace.ticks+1)+1⟩
          | .integer rightValue =>
              let answer := ValueReduction.arithmetic op leftValue rightValue
              let outcome := if ValueReduction.signed64 answer then .integer answer else .overflow stack
              ⟨outcome,events,leftTrace.ticks+((rightTrace.ticks+1)+1)+1⟩

private theorem prepend_step (started : step initialState = some (next,none))
    (rest : run ticks next = result) :
    run (ticks+1) initialState = { result with steps := result.steps+1 } := by
  rw [run,started]
  dsimp only
  rw [rest]
  rfl

private theorem concatenate_runs (first : run ticks initialState = ⟨middle,events,ticks⟩)
    (second : run following middle = ⟨last,later,following⟩) :
    run (ticks+following) initialState = ⟨last,events ++ later,ticks+following⟩ := by
  rw [run_add,first]
  dsimp only
  rw [second]

private theorem finish_arithmetic (heap : SizedBufferHeap.IndexedState) (pending : List (BufferFrame × List Frame))
    (stack : List Frame) (op : Arith) (left right : Int) :
    let answer := ValueReduction.arithmetic op left right
    let outcome := if ValueReduction.signed64 answer then Outcome.integer answer else .overflow stack
    run 1 ⟨heap,.returned (.integer right),.arithmeticRight op left :: stack,pending⟩ =
      Trace.result ⟨outcome,[],1⟩ heap stack pending := by
  by_cases fit : ValueReduction.signed64 (ValueReduction.arithmetic op left right)
  all_goals simp only [run,step,returnAction,executeLegacy,execute,fit,↓reduceIte,Trace.result,fault]
  all_goals rfl

set_option linter.unusedSimpArgs false in
private theorem read_steps (heap : SizedBufferHeap.IndexedState) (pending : List (BufferFrame × List Frame))
    (code : Code) (stack : List Frame)
    (argument : code.values[0]? = some (some (.reference token)))
    (leased : heap.metadata.heap.lease token = some object)
    (offsetBound : offset < 2^64) (within : offset < heap.metadata.length object) :
    let reader := ArithmeticReader.read offset count
    run 5 ⟨heap,.evaluate (code.child reader.term),stack,pending⟩ =
      (replay code heap token object reader stack).result heap stack pending := by
  have read : heap.read token offset = some (heap.cell object offset) := by
    unfold SizedBufferHeap.IndexedState.read
    rw [leased]
    change (if offset < heap.metadata.length object then some (heap.cell object offset) else none) = _
    rw [ite_eq_left within]
  simp only [term,replay,Trace.result,run,step,Code.child,evaluateAction,executeLegacy,execute,
    returnAction,argument,offsetBound,read,ite_true,Option.map_none,Option.map_some]
  rfl

/-- The independent syntax-tree trace describes the exact mutable evaluator
prefix. Reads occur in source order, and overflow records only frames already
entered by that prefix. The heap and suspended frames are retained. -/
theorem replay_executes (reader : ArithmeticReader) (heap : SizedBufferHeap.IndexedState)
    (pending : List (BufferFrame × List Frame)) (code : Code) (stack : List Frame)
    (argument : code.values[0]? = some (some (.reference token)))
    (leased : heap.metadata.heap.lease token = some object) (ready : reader.Ready (heap.metadata.length object)) :
    let trace := replay code heap token object reader stack
    run trace.ticks ⟨heap,.evaluate (code.child reader.term),stack,pending⟩ = trace.result heap stack pending := by
  induction reader generalizing stack with
  | literal number =>
      have bounded : ValueReduction.signed64 number := ready
      simp only [replay,Trace.result,term,run,step,evaluateAction,Code.child,bounded,ite_true,
        executeLegacy,execute,Option.map_none]
      rfl
  | read offset count => exact read_steps (count := count) heap pending code stack argument leased ready.1 ready.2
  | arithmetic op left right leftRec rightRec =>
      let leftStack := .arithmeticLeft op (code.child right.term) :: stack
      let before : State := ⟨heap,.evaluate (code.child (.arith op left.term right.term)),stack,pending⟩
      have entered : step before = some (⟨heap,.evaluate (code.child left.term),leftStack,pending⟩,none) := rfl
      have leftExecuted := leftRec leftStack ready.1
      dsimp only at leftExecuted
      cases leftTrace : replay code heap token object left leftStack with
      | mk leftOutcome leftEvents leftTicks =>
          rw [leftTrace] at leftExecuted
          dsimp only [leftStack] at leftTrace
          cases leftOutcome with
          | overflow remaining =>
              change run _ before = _
              simp only [replay,leftTrace,Trace.result]
              exact prepend_step entered leftExecuted
          | integer lhs =>
              let rightStack := .arithmeticRight op lhs :: stack
              have advanced : step ⟨heap,.returned (.integer lhs),leftStack,pending⟩ =
                  some (⟨heap,.evaluate (code.child right.term),rightStack,pending⟩,none) := rfl
              have rightExecuted := rightRec rightStack ready.2
              dsimp only at rightExecuted
              cases rightTrace : replay code heap token object right rightStack with
              | mk rightOutcome rightEvents rightTicks =>
                  rw [rightTrace] at rightExecuted
                  dsimp only [rightStack] at rightTrace
                  cases rightOutcome with
                  | overflow remaining =>
                      have afterLeft := prepend_step advanced rightExecuted
                      have complete := concatenate_runs leftExecuted afterLeft
                      change run _ before = _
                      simp only [replay,leftTrace,rightTrace,Trace.result]
                      exact prepend_step entered complete
                  | integer rhs =>
                      have finished := finish_arithmetic heap pending stack op lhs rhs
                      have afterRight := concatenate_runs rightExecuted finished
                      have afterLeft := prepend_step advanced afterRight
                      have complete := concatenate_runs leftExecuted afterLeft
                      change run _ before = _
                      simp only [replay,leftTrace,rightTrace,Trace.result]
                      simpa only [Nat.add_assoc,List.append_nil] using prepend_step entered complete

theorem checked_ready (reader : ArithmeticReader)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (closing : LoanTyping.Ghost.Substitution env original.context [] meanings)
    (sizes : OwnerSizes env heap original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (typed : LoanTyping.HasType env [] original.context true (Lending.read (.var owner) reader.term) type) :
    reader.Ready (heap.length object) ∧ LoanTyping.Conversion.Conv env .i64 type := by
  induction reader generalizing type with
  | literal number =>
      simp only [term,Lending.read,Term.subst,substArgs] at typed
      exact ⟨typed.integer_bound,typed.principalView⟩
  | read offset count =>
      simp only [term,Lending.read,Term.subst,substArgs,Op.binders,liftSub,single] at typed
      obtain ⟨size,ownerTyped,_,evidence⟩ := typed.named_index_owner history.wellFormed
      obtain ⟨offsetBound,_,ordered⟩ := evidence.literal_decide_limits history.wellFormed
      have indexedSize := sizes.typed_variable history ownerTyped stored
      have bufferSize : OwnerSize env heap object (.buffer (size.subst meanings)) := by
        simpa only [Term.subst,substArgs,Op.binders,liftSub] using indexedSize
      have closedEvidence := evidence.ghostSubstitution history.wellFormed closing
      have evidenceTyped : LoanTyping.HasType env [] [] true (.decide (.natural offset) (.natural count))
          (.lt (.natural offset) (size.subst meanings)) := by
        simpa only [Term.subst,substArgs,Op.binders,liftSub] using closedEvidence
      have checked := (evidenceTyped.principalView.lt_injective history.wellFormed.admissible).2
      have length : heap.length object = count :=
        ((bufferSize.buffer_length history).trans checked.symm).natural_injective history.wellFormed.admissible
      exact ⟨⟨offsetBound,length.symm ▸ ordered⟩,typed.principalView⟩
  | arithmetic op left right leftRec rightRec =>
      simp only [term,Lending.read,Term.subst,substArgs,Op.binders,liftSub] at typed
      obtain ⟨leftTyped,rightTyped⟩ := typed.arith_inputs
      exact ⟨⟨(leftRec leftTyped).1,(rightRec rightTyped).1⟩,typed.principalView⟩

end ArithmeticReader

/-- A real replay returning a scalar can close its reader at the original
continuation annotation. The numeric invariant of the reached machine state
supplies the signed width. On overflow the interpreter has already stopped. -/
theorem reachable_replayed_integer_close (term : Term) (fuel : Nat) (trace : ArithmeticReader.Trace)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode original meanings type)
    (originalShape : original.term = .lend (.var owner) (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (observedType : LoanTyping.Conversion.Conv env .i64 (first.subst meanings))
    (stackShape : (run fuel (initial term)).state.stack = .lendFinish token object name
      ((Term.var owner).subst original.origins) resultOrigin
      (original.child (.lam false first (.lam false again body))) :: stack)
    (leased : (run fuel (initial term)).state.heap.metadata.heap.lease token = some object)
    (executed : let state := (run fuel (initial term)).state
      run trace.ticks state = trace.result state.heap state.stack state.pending) :
    let state := (run fuel (initial term)).state
    let result := run trace.ticks state
    match trace.outcome with
    | .integer number =>
        let closed := SizedBufferHeap.close state.heap.metadata token
        let next : State := ⟨⟨closed,state.heap.cell⟩,.evaluate (original.child (.lam false first (.lam false again body))),
          .lendContinuation object ((Term.var owner).subst original.origins) resultOrigin (.integer number) :: stack,
          state.pending⟩
        LoanTyping.HasType env [] [] true (.integer number) (first.subst meanings) ∧
          step result.state = some (next,some (.legacy (.heap (.close token)))) ∧
          ¬ StateReferenceOccurs token next ∧ closed.heap.lease token = none ∧
          (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
          ReaderInventory closed (readerFrames next.activeStack)
    | .overflow _ =>
        step result.state = none ∧ result.state.heap.metadata.heap.lease token = some object := by
  let state := (run fuel (initial term)).state
  have midpoint : (run (fuel+trace.ticks) (initial term)).state = (run trace.ticks state).state := by
    have fields := congrArg Result.state (run_add fuel trace.ticks (initial term))
    exact fields
  dsimp only at executed
  dsimp only
  cases outcome : trace.outcome with
  | overflow remaining =>
      rw [executed]
      simp only [ArithmeticReader.Trace.result,outcome,step]
      exact ⟨True.intro,leased⟩
  | integer number =>
      have returnedState : (run (fuel+trace.ticks) (initial term)).state =
          ⟨state.heap,.returned (.integer number),state.stack,state.pending⟩ := by
        rw [midpoint,executed]
        simp only [ArithmeticReader.Trace.result,outcome]
        rfl
      have returned := congrArg State.control returnedState
      have retained := congrArg State.stack returnedState
      have physical := congrArg State.heap returnedState
      have suspended := congrArg State.pending returnedState
      dsimp only at returned retained physical suspended
      have bounded := (initial_run_numbers term (fuel+trace.ticks)).legacy.2.1
      change ControlNumbers (run (fuel+trace.ticks) (initial term)).state.control at bounded
      rw [returned] at bounded
      have numeric := ValueNumbers.integerBound bounded
      have kind : ValueKind env (.integer number) (first.subst meanings) := observedType
      obtain ⟨closedStep,absent,retired,others,inventory⟩ := reachable_lend_return_nonescape term
        (fuel+trace.ticks) history typed originalShape returned kind (retained.trans stackShape)
      rw [physical,suspended,midpoint] at closedStep
      rw [physical,suspended] at absent inventory
      rw [physical] at retired others
      exact ⟨(LoanTyping.HasType.integer numeric.1 numeric.2).convert observedType,
        closedStep,absent,retired,others,inventory⟩

/-- The original Lend typing certifies every literal and read in any tree
of signed arithmetic. Its independent trace runs through the read values in
the current indexed heap. On success the result keeps the original callback
annotation and the very next step closes its lease without leaking a token.
On overflow the fault stack is exact, the token stays live, and execution
stops before any pending right-side subexpression. -/
theorem reachable_arithmetic_tree_lend_close (term : Term) (fuel : Nat) (reader : ArithmeticReader)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode original meanings type)
    (originalShape : original.term = .lend (.var owner) (.lam false domain reader.term)
      (.lam false first (.lam false again body)))
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate (enter false domain reader.term
      original.context original.origins original.values (.borrow ((Term.var owner).subst original.origins))
      (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack = .lendFinish token object
      (some (original.context.length-owner)) ((Term.var owner).subst original.origins) resultOrigin
      (original.child (.lam false first (.lam false again body))) :: stack) :
    let state := (run fuel (initial term)).state
    let entry := enter false domain reader.term original.context original.origins original.values
      (.borrow ((Term.var owner).subst original.origins)) (some (.reference token))
    let trace := reader.replay entry state.heap token object state.stack
    let result := run trace.ticks state
    result = trace.result state.heap state.stack state.pending ∧
    match trace.outcome with
    | .integer number =>
        let closed := SizedBufferHeap.close state.heap.metadata token
        let next : State := ⟨⟨closed,state.heap.cell⟩,.evaluate (original.child (.lam false first (.lam false again body))),
          .lendContinuation object ((Term.var owner).subst original.origins) resultOrigin (.integer number) :: stack,
          state.pending⟩
        LoanTyping.HasType env [] [] true (.integer number) (first.subst meanings) ∧
          step result.state = some (next,some (.legacy (.heap (.close token)))) ∧
          ¬ StateReferenceOccurs token next ∧ closed.heap.lease token = none ∧
          (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
          ReaderInventory closed (readerFrames next.activeStack)
    | .overflow _ =>
        step result.state = none ∧ result.state.heap.metadata.heap.lease token = some object := by
  let state := (run fuel (initial term)).state
  let entry := enter false domain reader.term original.context original.origins original.values
    (.borrow ((Term.var owner).subst original.origins)) (some (.reference token))
  let trace := reader.replay entry state.heap token object state.stack
  have ⟨closing,localType,source,converted⟩ := typed
  rw [originalShape] at source
  obtain ⟨_,valueType,_,readTyped,firstTyped,_⟩ := source.explicitLendValueDomains history.wellFormed
  have readyAndType := reader.checked_ready history closing sizes stored readTyped
  obtain ⟨ready,i64Type⟩ := readyAndType
  have observedType : LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
    simpa only [Term.subst,substArgs] using (i64Type.trans firstTyped.symm).substitution meanings history.wellFormed.closed
  have entries : ReaderInventory state.heap.metadata
      ((token,object,some (original.context.length-owner)) :: readerFrames (stack ++ state.pending.flatMap Prod.snd)) := by
    simpa only [state,State.activeStack,stackShape,List.cons_append,readerFrames,List.filterMap_cons,Frame.reader?]
      using (initial_run_invariant term fuel).2
  have leased := entries.live _ List.mem_cons_self
  have executed := reader.replay_executes state.heap state.pending entry state.stack (by rfl) leased ready
  change run trace.ticks ⟨state.heap,.evaluate entry,state.stack,state.pending⟩ =
    trace.result state.heap state.stack state.pending at executed
  change state.control = .evaluate entry at evaluating
  rw [← evaluating] at executed
  exact ⟨executed,reachable_replayed_integer_close term fuel trace history typed originalShape observedType
    stackShape leased executed⟩

namespace Examples

private def nestedArithmetic (rhs : Int) : Term :=
  let buffer := Term.buffer (.natural 2)
  let readBound := Term.decide (.natural 1) (.natural 2)
  let input := Term.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) readBound
  let reader := ArithmeticReader.arithmetic .add (.arithmetic .add (.read 0 2) (.literal rhs)) (.read 1 2)
  .lend input (.lam false (.ref buffer) reader.term)
    (.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1))))

private def readOffsets (events : List Event) : List Nat :=
  events.filterMap fun event => match event with
    | .legacy (.heap (.read _ offset _)) => some offset
    | _ => none

set_option maxRecDepth 4096 in
/-- A nested signed expression reads both cells in source order before
returning its value and allowing release of the original Buffer. -/
theorem nested_reader_executes_reads_in_order :
    LoanTyping.MixedProgram.checkDeclaration 32 64 .empty ⟨.i64,nestedArithmetic 5⟩ =
      some ⟨.i64,nestedArithmetic 5⟩ ∧
    let result := run 60 (initial (nestedArithmetic 5))
    readOffsets result.events = [0,1] ∧ observe result = .integer 15 ∧
      result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl⟩

set_option maxRecDepth 4096 in
/-- Overflow in the left subtree suppresses the still-pending right read
and does not close the active lease. -/
theorem nested_reader_overflow_skips_right_read :
    LoanTyping.MixedProgram.checkDeclaration 32 64 .empty ⟨.i64,nestedArithmetic 9223372036854775807⟩ =
      some ⟨.i64,nestedArithmetic 9223372036854775807⟩ ∧
    let result := run 60 (initial (nestedArithmetic 9223372036854775807))
    readOffsets result.events = [0] ∧ observe result = .fault .arithmeticOverflow ∧
      result.state.heap.metadata.heap.lease 0 = some 0 := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
