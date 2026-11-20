import Jihoo.NativeBindingMachineMutableOutlivedReferences
import Jihoo.NativeBindingMachineMutableNumeric
import Jihoo.NativeBindingMachineMutableFreeContinuation

/-! A computed reader result can use the same typed close as a variable.
The signed arithmetic case derives that result from the original Lend and
executes the read from the actual indexed cell before testing overflow. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private def SignedOperands (env : Environment) (loans : Loans.Stack) (ctx : Context) (mode : Bool) : Term → Prop
  | .arith _ left right => HasType env loans ctx mode left .i64 ∧ HasType env loans ctx mode right .i64
  | _ => True

private theorem signed_operands (typed : HasType env loans ctx mode term type) :
    SignedOperands env loans ctx mode term := by
  apply HasType.rec (t := typed) (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack ctx mode term _ _ => SignedOperands env stack ctx mode term)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case dataElim => split <;> trivial

theorem HasType.arith_inputs (typed : HasType env loans ctx mode (.arith op left right) type) :
    HasType env loans ctx mode left .i64 ∧ HasType env loans ctx mode right .i64 :=
  signed_operands typed

end Jihoo.NativeKernel.Environment.LoanTyping

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable

/-- A computed result at the original reader annotation closes the same
actual lease and excludes that token from every retained runtime location. -/
theorem reachable_lend_return_nonescape (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (originalTyped : LoanClosingTyped env loans mode original meanings type)
    (originalShape : original.term = .lend owner (.lam false domain readerBody)
      (.lam false first (.lam false again body)))
    (returned : (run fuel (initial term)).state.control = .returned value)
    (kind : ValueKind env value (first.subst meanings))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object name origin resultOrigin
        (original.child (.lam false first (.lam false again body))) :: stack) :
    let state := (run fuel (initial term)).state
    let closed := SizedBufferHeap.close state.heap.metadata token
    let next : State := ⟨⟨closed,state.heap.cell⟩,.evaluate (original.child (.lam false first (.lam false again body))),
      .lendContinuation object origin resultOrigin value :: stack,state.pending⟩
    step state = some (next,some (.legacy (.heap (.close token)))) ∧
      ¬ StateReferenceOccurs token next ∧ closed.heap.lease token = none ∧
      (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
      ReaderInventory closed (readerFrames next.activeStack) := by
  have allowed := originalTyped.reader_domain_outlived history originalShape
  have resultAbsent := kind.outlived_reference_absent history.wellFormed.admissible allowed token
  obtain ⟨continuationReady,outerReady,pendingReady⟩ := initial_run_finish_capture_bounds term fuel stackShape
  obtain ⟨executed,retired,others,inventory⟩ :=
    lend_close_step (initial_run_invariant term fuel).2 returned stackShape
  refine ⟨executed,?_,retired,others,inventory⟩
  intro occurs
  rcases occurs with (control | ⟨frame,member,occurs⟩) | pending
  · exact continuationReady.fresh_absent control
  · rcases List.mem_cons.mp member with rfl | member
    · exact resultAbsent occurs
    · exact outerReady.fresh_absent member occurs
  · exact pendingReady.fresh_absent pending

private def arithmeticReader (op : Arith) (offset count : Nat) (rhs : Int) : Term :=
  .arith op (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))) (.integer rhs)

private theorem original_arithmetic_reader_inputs
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode original meanings type)
    (sizes : OwnerSizes env heap original meanings)
    (shape : original.term = .lend (.var owner) (.lam false domain (arithmeticReader op offset count rhs))
      (.lam false first (.lam false again body)))
    (stored : original.values[owner]? = some (some (.owner object))) :
    offset < 2^64 ∧ offset < heap.length object ∧ ValueReduction.signed64 rhs ∧
      LoanTyping.Conversion.Conv env .i64 (first.subst meanings) := by
  obtain ⟨closing,_,source,_⟩ := typed
  rw [shape] at source
  obtain ⟨_,valueType,_,readTyped,firstConverted,_⟩ := source.explicitLendValueDomains history.wellFormed
  simp only [arithmeticReader,Lending.read,Term.subst,substArgs,Op.binders,liftSub,single] at readTyped
  obtain ⟨leftTyped,rightTyped⟩ := readTyped.arith_inputs
  obtain ⟨size,ownerTyped,_,evidence⟩ := leftTyped.named_index_owner history.wellFormed
  obtain ⟨offsetBound,_,ordered⟩ := evidence.literal_decide_limits history.wellFormed
  have indexedSize := sizes.typed_variable history ownerTyped stored
  have bufferSize : OwnerSize env heap object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using indexedSize
  have closedEvidence := evidence.ghostSubstitution history.wellFormed closing
  have evidenceTyped : LoanTyping.HasType env [] [] true (.decide (.natural offset) (.natural count))
      (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using closedEvidence
  have physical := bufferSize.buffer_length history
  have checked := (evidenceTyped.principalView.lt_injective history.wellFormed.admissible).2
  have length : heap.length object = count :=
    (physical.trans checked.symm).natural_injective history.wellFormed.admissible
  have readerType : LoanTyping.Conversion.Conv env .i64 valueType := readTyped.principalView
  have resultType := (readerType.trans firstConverted.symm).substitution meanings history.wellFormed.closed
  exact ⟨offsetBound,length.symm ▸ ordered,rightTyped.integer_bound,
    by simpa only [Term.subst,substArgs] using resultType⟩

set_option linter.unusedSimpArgs false in
private theorem arithmetic_reader_run (state : State) {original : Code}
    (evaluating : state.control = .evaluate (enter false domain (arithmeticReader op offset count rhs)
      original.context original.origins original.values (.borrow origin) (some (.reference token))))
    (offsetBound : offset < 2^64) (rhsBound : ValueReduction.signed64 rhs)
    (read : state.heap.read token offset = some (state.heap.cell object offset)) :
    let answer := ValueReduction.arithmetic op (decodeInteger (state.heap.cell object offset)) rhs
    run 9 state = ⟨{state with control :=
      if ValueReduction.signed64 answer then .returned (.integer answer) else .fault .arithmeticOverflow},
      [.legacy (.heap (.read token offset (state.heap.cell object offset)))],9⟩ := by
  by_cases fit : ValueReduction.signed64 (ValueReduction.arithmetic op (decodeInteger (state.heap.cell object offset)) rhs)
  all_goals simp only [run,step,evaluating,arithmeticReader,evaluateAction,Code.child,enter,List.getElem?_cons_zero,
    offsetBound,rhsBound,executeLegacy,execute,returnAction,read,fit,ite_true,↓reduceIte,Option.map_none,
    Option.map_some,fault]
  all_goals rfl

/-- At an actual named-reader entry, the original Lend derivation supplies the
literal Index and signed-operand guards. Nine steps read the current indexed
cell and compute the result or fault on overflow. A fitting result has the
original continuation annotation and closes only its own reader in one more
step. Overflow leaves that lease active and produces no close event. -/
theorem reachable_reference_arithmetic_lend_close (term : Term) (fuel : Nat)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans mode original meanings type)
    (originalShape : original.term = .lend (.var owner) (.lam false domain
      (.arith op (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))) (.integer rhs)))
      (.lam false first (.lam false again body)))
    (sizes : OwnerSizes env (run fuel (initial term)).state.heap.metadata original meanings)
    (stored : original.values[owner]? = some (some (.owner object)))
    (evaluating : (run fuel (initial term)).state.control = .evaluate (enter false domain
      (.arith op (.index (.var 0) (.natural offset) (.decide (.natural offset) (.natural count))) (.integer rhs))
      original.context original.origins original.values (.borrow ((Term.var owner).subst original.origins))
      (some (.reference token))))
    (stackShape : (run fuel (initial term)).state.stack =
      .lendFinish token object (some (original.context.length-owner)) ((Term.var owner).subst original.origins)
        resultOrigin (original.child (.lam false first (.lam false again body))) :: stack) :
    let state := (run fuel (initial term)).state
    let payload := state.heap.cell object offset
    let answer := ValueReduction.arithmetic op (decodeInteger payload) rhs
    let closed := SizedBufferHeap.close state.heap.metadata token
    let continuation := original.child (.lam false first (.lam false again body))
    let next : State := ⟨⟨closed,state.heap.cell⟩,.evaluate continuation,
      .lendContinuation object ((Term.var owner).subst original.origins) resultOrigin (.integer answer) :: stack,
      state.pending⟩
    offset < state.heap.metadata.length object ∧
    run 9 state = ⟨{state with control :=
      if ValueReduction.signed64 answer then .returned (.integer answer) else .fault .arithmeticOverflow},
      [.legacy (.heap (.read token offset payload))],9⟩ ∧
    if ValueReduction.signed64 answer then
      LoanTyping.HasType env [] [] true (.integer answer) (first.subst meanings) ∧
      run 10 state = ⟨next,[.legacy (.heap (.read token offset payload)),.legacy (.heap (.close token))],10⟩ ∧
      ¬ StateReferenceOccurs token next ∧ closed.heap.lease token = none ∧
      (∀ other, other ≠ token → closed.heap.lease other = state.heap.metadata.heap.lease other) ∧
      ReaderInventory closed (readerFrames next.activeStack)
    else
      run 10 state = run 9 state ∧ state.heap.metadata.heap.lease token = some object := by
  let state := (run fuel (initial term)).state
  let payload := state.heap.cell object offset
  let answer := ValueReduction.arithmetic op (decodeInteger payload) rhs
  obtain ⟨offsetBound,within,rhsBound,converted⟩ := original_arithmetic_reader_inputs history typed
    sizes originalShape stored
  have inventory := (initial_run_invariant term fuel).2
  have entries : ReaderInventory state.heap.metadata
      ((token,object,some (original.context.length-owner)) :: readerFrames (stack ++ state.pending.flatMap Prod.snd)) := by
    simpa only [state,State.activeStack,stackShape,List.cons_append,readerFrames,List.filterMap_cons,Frame.reader?]
      using inventory
  have leased := entries.live _ List.mem_cons_self
  have read : state.heap.read token offset = some payload := by
    unfold SizedBufferHeap.IndexedState.read
    rw [leased]
    change (if offset < state.heap.metadata.length object then some payload else none) = some payload
    rw [ite_eq_left within]
  have executed := arithmetic_reader_run state evaluating offsetBound rhsBound read
  refine ⟨within,executed,?_⟩
  have midpoint : (run (fuel+9) (initial term)).state = (run 9 state).state := by
    have fields := congrArg Result.state (run_add fuel 9 (initial term))
    exact fields
  have complete := run_add 9 1 state
  change run 9 state = ⟨{state with control := (if ValueReduction.signed64 answer then
    .returned (.integer answer) else .fault .arithmeticOverflow)},
    [.legacy (.heap (.read token offset payload))],9⟩ at executed
  by_cases fits : ValueReduction.signed64 answer
  · rw [ite_eq_left fits] at executed ⊢
    have returned : (run (fuel+9) (initial term)).state.control = .returned (.integer answer) := by
      rw [midpoint,executed]
    have stackAtReturn : (run (fuel+9) (initial term)).state.stack =
        .lendFinish token object (some (original.context.length-owner)) ((Term.var owner).subst original.origins)
          resultOrigin (original.child (.lam false first (.lam false again body))) :: stack := by
      rw [midpoint,executed]
      exact stackShape
    have kind : ValueKind env (.integer answer) (first.subst meanings) := converted
    obtain ⟨closedStep,absent,retired,others,nextInventory⟩ :=
      reachable_lend_return_nonescape term (fuel+9) history typed originalShape returned kind stackAtReturn
    rw [midpoint,executed] at closedStep absent retired others nextInventory
    refine ⟨(LoanTyping.HasType.integer fits.1 fits.2).convert converted,?_,absent,retired,others,nextInventory⟩
    change run 10 state = _
    rw [complete,executed]
    dsimp only
    rw [run,closedStep]
    rfl
  · rw [ite_eq_right fits] at executed ⊢
    refine ⟨?_,leased⟩
    change run 10 state = run 9 state
    rw [complete,executed]
    rfl

namespace Examples

private def writtenOperand (rhs : Int) : Term :=
  let buffer := Term.buffer (.natural 2)
  let readBound := Term.decide (.natural 1) (.natural 2)
  let input := Term.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) readBound
  .lend input (.lam false (.ref buffer) (arithmeticReader .add 1 2 rhs))
    (.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1))))

/-- The arithmetic consumes the written cell, and the resulting close
permits the original continuation to release the owner. -/
theorem signed_reader_uses_written_cell :
    LoanTyping.MixedProgram.checkDeclaration 32 64 .empty ⟨.i64,writtenOperand 5⟩ =
      some ⟨.i64,writtenOperand 5⟩ ∧
    let result := run 40 (initial (writtenOperand 5))
    observe result = .integer 12 ∧ result.state.heap.metadata.heap.lease 0 = none ∧
      result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl⟩

/-- Source typing admits signed arithmetic with a runtime overflow check.
Overflow cannot close the reader or enter its original continuation. -/
theorem signed_reader_overflow_keeps_lease :
    LoanTyping.MixedProgram.checkDeclaration 32 64 .empty ⟨.i64,writtenOperand 9223372036854775807⟩ =
      some ⟨.i64,writtenOperand 9223372036854775807⟩ ∧
    let result := run 40 (initial (writtenOperand 9223372036854775807))
    observe result = .fault .arithmeticOverflow ∧ result.state.heap.metadata.heap.lease 0 = some 0 := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
