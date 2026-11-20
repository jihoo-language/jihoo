import Jihoo.NativeBindingMachineMutableStoreCleanup

/-! A captured index and signed scalar expression drive the indexed Store
machine. The source evidence supplies the bound for the actual allocation. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity
open Jihoo.Quantity NativeQuantity

/-- Store visits the named owner, index, and value in that order. The
dependent bound proof is erased by the original resource projection. -/
theorem projectRaw_named_store_operands
    (checked : projectRaw (fuel+2) env loans ctx (.store (.var owner) index value evidence) = some receipt) :
    ∃ indexReceipt valueReceipt,
      projectRaw (fuel+1) env loans ctx index = some indexReceipt ∧
      projectRaw (fuel+1) env loans ctx value = some valueReceipt ∧
      receipt = .seq (.use owner) (.seq indexReceipt (.seq valueReceipt .pure)) := by
  simp only [projectRaw,Op.arity,runtimeFields,erasedNode,fields,fetch,
    List.length_cons,List.length_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
    bind,Option.bind,Nat.reduceAdd,bne_self_eq_false,Bool.false_eq_true,↓reduceIte] at checked
  cases selected : lookup ctx owner with
  | none => simp [selected] at checked
  | some binding =>
      cases erased : binding.erased with
      | true => simp [selected,erased] at checked
      | false =>
          cases indexProjected : projectRaw (fuel+1) env loans ctx index with
          | none => simp [selected,erased,indexProjected] at checked
          | some indexReceipt =>
              cases valueProjected : projectRaw (fuel+1) env loans ctx value with
              | none => simp [selected,erased,indexProjected,valueProjected] at checked
              | some valueReceipt =>
                  simp [selected,erased,indexProjected,valueProjected] at checked
                  exact ⟨indexReceipt,valueReceipt,rfl,rfl,checked.symm⟩

end Jihoo.NativeKernel.Environment.LoanTyping.ResourceQuantity

namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

inductive IntegerOperand where
  | literal (number : Int)
  | captured (slot : Nat)
  | arithmetic (op : Arith) (left right : IntegerOperand)

namespace IntegerOperand

def term : IntegerOperand → Term
  | .literal number => .integer number
  | .captured slot => .var slot
  | .arithmetic op left right => .arith op left.term right.term

def ticks : IntegerOperand → Nat
  | .literal _ | .captured _ => 1
  | .arithmetic _ left right => 1+(left.ticks+(1+(right.ticks+1)))

private def fit (number : Int) : Option Int :=
  if ValueReduction.signed64 number then some number else none

def value (meanings : Nat → Term) : IntegerOperand → Option Int
  | .literal number => fit number
  | .captured slot =>
      match meanings slot with
      | .integer number => fit number
      | _ => none
  | .arithmetic op left right => do
      let lhs ← value meanings left
      let rhs ← value meanings right
      fit (ValueReduction.arithmetic op lhs rhs)

private theorem fit_sound (observed : fit candidate = some number) :
    candidate = number ∧ ValueReduction.signed64 number := by
  unfold fit at observed
  split at observed
  · cases observed
    exact ⟨rfl,by assumption⟩
  · contradiction

end IntegerOperand

theorem noevent_step_run (selected : step before = some (after,none)) :
    run 1 before = ⟨after,[],1⟩ := by
  rw [run,selected]
  rfl

theorem join_runs (first : run ticks before = ⟨middle,left,ticks⟩)
    (second : run more middle = ⟨after,right,more⟩) :
    run (ticks+more) before = ⟨after,left ++ right,ticks+more⟩ := by
  rw [run_add,first]
  dsimp only
  rw [second]

private theorem integer_slot
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false (code.child (.var slot)) meanings .i64)
    (context : ValueContext env code meanings) (aligned : CodeAligned code) :
    ∃ number, code.values[slot]? = some (some (.integer number)) ∧ meanings slot = .integer number := by
  obtain ⟨value,stored,kind⟩ := (context.child (.var slot)).variable_kind history typed (aligned.child _) rfl
  obtain ⟨number,rfl⟩ := kind.integer_shape history.wellFormed.admissible
  exact ⟨number,stored,context.scalars.2 slot number stored⟩

/-- All successful arithmetic subexpressions run in order inside pending
frames. The result is checked against the captured source interpretation. -/
theorem IntegerOperand.checked_run (operand : IntegerOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (typed : LoanClosingTyped env loans false (code.child operand.term) meanings .i64)
    (context : ValueContext env code meanings) (aligned : CodeAligned code)
    (observed : operand.value meanings = some number)
    (heap : SizedBufferHeap.IndexedState) (stack : List Frame)
    (pending : List (BufferFrame × List Frame)) :
    ValueReduction.signed64 number ∧
    run operand.ticks ⟨heap,.evaluate (code.child operand.term),stack,pending⟩ =
      ⟨⟨heap,.returned (.integer number),stack,pending⟩,[],operand.ticks⟩ := by
  induction operand generalizing number stack with
  | literal candidate =>
      obtain ⟨rfl,bounded⟩ := IntegerOperand.fit_sound observed
      refine ⟨bounded,?_⟩
      simp only [IntegerOperand.term,IntegerOperand.ticks,run,step,Code.child,evaluateAction,bounded,
        ite_true,executeLegacy,execute,Option.map_none]
      rfl
  | captured slot =>
      obtain ⟨candidate,stored,meaning⟩ := integer_slot history typed context aligned
      simp only [IntegerOperand.value,meaning] at observed
      obtain ⟨rfl,bounded⟩ := IntegerOperand.fit_sound observed
      refine ⟨bounded,?_⟩
      simp only [IntegerOperand.term,IntegerOperand.ticks,run,step,Code.child,evaluateAction,stored,
        executeLegacy,execute,Option.map_none]
      rfl
  | arithmetic op left right leftRec rightRec =>
      obtain ⟨closing,_,source,_⟩ := typed
      obtain ⟨leftTyped,rightTyped⟩ := source.arith_inputs
      change (do
        let lhs ← left.value meanings
        let rhs ← right.value meanings
        IntegerOperand.fit (ValueReduction.arithmetic op lhs rhs)) = some number at observed
      obtain ⟨lhs,leftValue,afterLeft⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨rhs,rightValue,computed⟩ := Option.bind_eq_some_iff.mp afterLeft
      obtain ⟨answer,bounded⟩ := IntegerOperand.fit_sound computed
      let leftStack := .arithmeticLeft op (code.child right.term) :: stack
      let rightStack := .arithmeticRight op lhs :: stack
      have leftStart : step ⟨heap,.evaluate (code.child (.arith op left.term right.term)),stack,pending⟩ =
          some (⟨heap,.evaluate (code.child left.term),leftStack,pending⟩,none) := rfl
      have rightStart : step ⟨heap,.returned (.integer lhs),leftStack,pending⟩ =
          some (⟨heap,.evaluate (code.child right.term),rightStack,pending⟩,none) := rfl
      have finish : run 1 ⟨heap,.returned (.integer rhs),rightStack,pending⟩ =
          ⟨⟨heap,.returned (.integer number),stack,pending⟩,[],1⟩ := by
        simp only [rightStack,run,step,returnAction,answer,bounded,ite_true,executeLegacy,execute,Option.map_none]
        rfl
      have scalarType : LoanTyping.Conversion.Conv env (Term.i64.subst meanings) .i64 := by
        simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .i64 .i64 from .refl _)
      have leftRun := (leftRec ⟨closing,.i64,leftTyped,scalarType⟩ leftValue leftStack).2
      have rightRun := (rightRec ⟨closing,.i64,rightTyped,scalarType⟩ rightValue rightStack).2
      refine ⟨bounded,?_⟩
      exact join_runs (noevent_step_run leftStart) <|
        join_runs leftRun <| join_runs (noevent_step_run rightStart) <| join_runs rightRun finish

private theorem captured_store_entry (state : State)
    (evaluating : state.control = .evaluate code)
    (shape : code.term = .store (.var owner) (.var index) value evidence)
    (stored : code.values[owner]? = some (some (.owner object)))
    (indexStored : code.values[index]? = some (some (.natural offset))) :
    run 5 state = ⟨⟨state.heap,.evaluate (code.child value),[],
      (.value object offset,state.stack) :: state.pending⟩,[],5⟩ := by
  simp only [run,step,evaluating,shape,Code.child,evaluateAction,stored,indexStored,
    executeLegacy,execute,Option.map_none,returnAction,resumeBuffer]
  rfl

private theorem captured_store_steps (state : State) (value : IntegerOperand)
    (evaluating : state.control = .evaluate code)
    (shape : code.term = .store (.var owner) (.var index) value.term evidence)
    (stored : code.values[owner]? = some (some (.owner object)))
    (indexStored : code.values[index]? = some (some (.natural offset)))
    (computed : run value.ticks
      ⟨state.heap,.evaluate (code.child value.term),[],(.value object offset,state.stack) :: state.pending⟩ =
        ⟨⟨state.heap,.returned (.integer number),[],(.value object offset,state.stack) :: state.pending⟩,[],value.ticks⟩)
    (written : state.heap.store object offset (encodeInteger number) = some heap) :
    run (5+(value.ticks+1)) state = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
      [.store object offset (encodeInteger number)],5+(value.ticks+1)⟩ := by
  let finished : State :=
    ⟨state.heap,.returned (.integer number),[],(.value object offset,state.stack) :: state.pending⟩
  have selected := (pending_store_executes finished rfl rfl rfl written).1
  have finish : run 1 finished = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
      [.store object offset (encodeInteger number)],1⟩ := by
    rw [run,selected]
    rfl
  exact join_runs (captured_store_entry state evaluating shape stored indexStored) (join_runs computed finish)

theorem named_store_use
    (checked : LoanTyping.ResourceQuantity.projectRaw (fuel+2) env loans code.context
      (.store (.var owner) index value evidence) = some receipt)
    (world : OwnerDemandWorld heap code receipt) (complete : OwnerDemandWorld.Total code receipt)
    (stored : code.values[owner]? = some (some (.owner object))) :
    receipt.demand owner = some 1 := by
  obtain ⟨_,_,_,_,shape⟩ := LoanTyping.ResourceQuantity.projectRaw_named_store_operands checked
  obtain ⟨_,_,_,_,separate⟩ := (shape ▸ world).sequence (shape ▸ complete)
  have zero := separate owner owner object 0 stored stored (by simp [Control.demand])
  rw [shape]
  simp only [Control.demand] at zero ⊢
  rw [zero]
  simp

/-- A typed captured index and a successful scalar expression select the
physical cell of the named Buffer. Closed Decide evidence gives the bound,
the original resource projection supplies exclusive ownership, and the
actual returned Buffer retains its original dependent type. -/
theorem reachable_captured_store_owned_result (program : Term) (fuel : Nat) (value : IntegerOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .store (.var owner) (.var index) value.term evidence)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computed : value.value meanings = some number)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let state := (run fuel (initial program)).state
    let duration := 5+(value.ticks+1)
    ∃ object offset heap, code.values[owner]? = some (some (.owner object)) ∧
      code.values[index]? = some (some (.natural offset)) ∧
      meanings index = .natural offset ∧ offset < 2^64 ∧ offset < state.heap.metadata.length object ∧
      receipt.demand owner = some 1 ∧
      run duration state = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
        [.store object offset (encodeInteger number)],duration⟩ ∧
      heap.metadata = state.heap.metadata ∧
      OwnedResult env heap.metadata state.activeStack object (code.term.subst meanings) type ∧
      decodeInteger (heap.cell object offset) = number ∧
      (∀ queried slot, queried ≠ object ∨ slot ≠ offset → heap.cell queried slot = state.heap.cell queried slot) := by
  let state := (run fuel (initial program)).state
  have closed := typed.closed history
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨size,ownerTyped,indexTyped,valueTyped,evidenceTyped,principal⟩ := source.store_inputs
  have aligned := initial_run_code_aligned program fuel SizedBufferHeap.empty evaluating
  have closedOwner : LoanClosingTyped env loans false (code.child (.var owner)) meanings
      ((Term.buffer size).subst meanings) :=
    ⟨closing,.buffer size,ownerTyped,.refl _⟩
  obtain ⟨actual,stored,kind⟩ := (context.child _).variable_kind history closedOwner (aligned.child _) rfl
  have buffer : ValueKind env actual (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  have closedIndex : LoanClosingTyped env loans false (code.child (.var index)) meanings .u64 :=
    ⟨closing,.u64,indexTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)⟩
  obtain ⟨actualIndex,indexStored,indexKind⟩ :=
    (context.child _).variable_kind history closedIndex (aligned.child _) rfl
  obtain ⟨offset,rfl⟩ := indexKind.natural_shape history.wellFormed.admissible
  have indexMeaning := context.scalars.1 index offset indexStored
  have literalIndex : LoanTyping.HasType env [] [] true (.natural offset) .u64 := by
    simpa only [Code.child,Term.subst,indexMeaning] using closedIndex.closed history
  have ownerSize : OwnerSize env state.heap.metadata object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using sizes.typed_variable history ownerTyped stored
  have physical := ownerSize.buffer_length history
  have closedEvidence : LoanTyping.HasType env [] [] true (.decide left right)
      (.lt (.natural offset) (size.subst meanings)) := by
    simpa only [decideEvidence,Term.subst,substArgs,Op.binders,liftSub,indexMeaning] using
      evidenceTyped.ghostSubstitution history.wellFormed closing
  obtain ⟨proofOffset,proofSize,leftNumber,rightNumber,_,_,ordered⟩ := closedEvidence.decide_truth
  have arguments := closedEvidence.principalView.lt_injective history.wellFormed.admissible
  have sameOffset := (arguments.1.symm.trans leftNumber).natural_injective history.wellFormed.admissible
  have sameSize := ((physical.trans arguments.2.symm).trans rightNumber).natural_injective history.wellFormed.admissible
  have within : offset < state.heap.metadata.length object := sameOffset ▸ sameSize ▸ ordered
  have use := named_store_use (shape ▸ checked) world complete stored
  have inactive : Loans.active code.context.length loans owner = false := by
    apply Bool.eq_false_iff.mpr
    intro active
    have zero := budget owner active
    rw [use] at zero
    cases zero
  have live := (world.live_once owner object 0 stored use).1
  change state.heap.metadata.heap.live object = true at live
  have noReaders := coverage.inactive stored inactive
  have invariant := initial_run_invariant program fuel
  have guard := (invariant.2.free_guard_iff invariant.1).mpr noReaders
  change freeGuard state.heap.metadata object = true at guard
  let heap : SizedBufferHeap.IndexedState := { state.heap with
    cell := HeapLeases.put state.heap.cell object (HeapLeases.put (state.heap.cell object) offset (encodeInteger number)) }
  have written : state.heap.store object offset (encodeInteger number) = some heap := by
    simp [SizedBufferHeap.IndexedState.store,live,guard,within,heap]
  obtain ⟨_,_,_,metadata,newCell,otherCells⟩ := SizedBufferHeap.IndexedState.store_spec invariant.1 written
  have resultType : LoanTyping.Conversion.Conv env (.buffer (size.subst meanings)) type := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (principal.substitution meanings history.wellFormed.closed).trans converted
  have owned : OwnedResult env heap.metadata state.activeStack object (code.term.subst meanings) type :=
    ⟨closed,metadata.symm ▸ ownerSize.convert resultType,metadata.symm ▸ live,noReaders⟩
  have closedValue : LoanClosingTyped env loans false (code.child value.term) meanings .i64 :=
    ⟨closing,.i64,valueTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .i64 .i64 from .refl _)⟩
  obtain ⟨bounded,valueRun⟩ := value.checked_run history closedValue context aligned computed state.heap []
    ((.value object offset,state.stack) :: state.pending)
  refine ⟨object,offset,heap,stored,indexStored,indexMeaning,literalIndex.natural_bound,within,use,
    captured_store_steps state value evaluating shape stored indexStored valueRun written,metadata,owned,?_,otherCells⟩
  rw [newCell]
  exact encode_decode_integer bounded

private theorem free_operand_entry (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .free argument tail) :
    run 1 state = ⟨⟨state.heap,.evaluate (code.child argument),.free (code.child tail) :: state.stack,state.pending⟩,[],1⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,executeLegacy,execute,Option.map_none]
  rfl

private theorem free_operand_return (state : State) (invariant : Invariant state)
    (owned : OwnedResult env state.heap.metadata state.activeStack object source type)
    (returned : state.control = .returned (.owner object)) (frame : state.stack = .free tail :: stack) :
    run 1 state = ⟨⟨⟨SizedBufferHeap.release state.heap.metadata object,state.heap.cell⟩,
      .evaluate tail,stack,state.pending⟩,[.legacy (.heap (.free object))],1⟩ := by
  have selected := free_owned_result_step state invariant owned returned frame
  dsimp only at selected
  rw [run,selected]
  rfl

/-- A captured index and computed scalar can drive a Store whose returned
owner is consumed by Free. The full prefix leaves the actual tail at its
checked dependent type and preserves the cells and live ownership of all
separately demanded sibling objects. -/
theorem reachable_captured_store_then_free (program : Term) (fuel : Nat) (value : IntegerOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .free (.store (.var owner) (.var index) value.term evidence) tail)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computed : value.value meanings = some number)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt)
    (sibling : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code later)
    (separated : OwnerDemandSeparation code receipt later) :
    let state := (run fuel (initial program)).state
    let duration := 1+((5+(value.ticks+1))+1)
    let result := run duration state
    let next := code.child tail
    ∃ (object offset : Nat) (heap : SizedBufferHeap.IndexedState) (residual : Jihoo.Quantity.Control),
      code.values[owner]? = some (some (.owner object)) ∧ code.values[index]? = some (some (.natural offset)) ∧
      result = ⟨⟨⟨SizedBufferHeap.release state.heap.metadata object,heap.cell⟩,
        .evaluate next,state.stack,state.pending⟩,
        [.store object offset (encodeInteger number),.legacy (.heap (.free object))],duration⟩ ∧
      decodeInteger (result.state.heap.cell object offset) = number ∧
      LoanClosingTyped env loans false next meanings type ∧ ValueContext env next meanings ∧
      OwnerSizes env result.state.heap.metadata code meanings ∧
      LoanSlots code loans result.state.activeStack ∧ LoanCoverage code loans result.state.activeStack ∧
      LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans next.context next.term = some residual ∧
      LoanTyping.ResourceQuantity.LoanBudget next.context.length loans residual ∧
      OwnerDemandWorld result.state.heap.metadata next residual ∧ OwnerDemandWorld.Total next residual ∧
      (∀ alias, code.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0) ∧
      OwnerDemandSeparation next residual later ∧ OwnerDemandWorld result.state.heap.metadata code later ∧
      ∀ slot wanted uses, code.values[slot]? = some (some (.owner wanted)) → later.demand slot = some (uses+1) →
        .free wanted ∉ result.events.filterMap Event.lifecycle? ∧
        ∀ cell, result.state.heap.cell wanted cell = state.heap.cell wanted cell := by
  let state := (run fuel (initial program)).state
  let storeTerm := Term.store (.var owner) (.var index) value.term evidence
  let next := code.child tail
  let storeTicks := 5+(value.ticks+1)
  let duration := 1+(storeTicks+1)
  let entered := (run (fuel+1) (initial program)).state
  have started := free_operand_entry state evaluating shape
  have reached : entered = (run 1 state).state := by
    have observed := congrArg Result.state (run_add fuel 1 (initial program))
    exact observed
  have enteredState : entered = ⟨state.heap,.evaluate (code.child storeTerm),.free next :: state.stack,state.pending⟩ := by
    rw [reached,started]
  have evaluatingStore : entered.control = .evaluate (code.child storeTerm) :=
    congrArg State.control enteredState
  have enterHeap : entered.heap = state.heap := by
    have observed := congrArg State.heap enteredState
    exact observed
  have enterFrames : readerFrames entered.activeStack = readerFrames state.activeStack := by
    rw [enteredState]
    rfl
  obtain ⟨closing,localType,source,converted⟩ := typed
  rw [shape] at source
  obtain ⟨size,storeSource⟩ := source.free_owner_inputs
  have storeTyped : LoanClosingTyped env loans false (code.child storeTerm) meanings ((Term.buffer size).subst meanings) :=
    ⟨closing,.buffer size,storeSource,.refl _⟩
  have tailTyped : LoanClosingTyped env loans false next meanings type :=
    ⟨closing,localType,source.free_tail,converted⟩
  obtain ⟨storeReceipt,residual,storeChecked,tailChecked,receiptShape⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_free_operands (shape ▸ checked)
  obtain ⟨storeWorld,storeTotal,restWorld,restTotal,disjoint⟩ :=
    (receiptShape ▸ world).sequence (receiptShape ▸ complete)
  obtain ⟨tailWorld,tailTotal,_,_,_⟩ := restWorld.sequence restTotal
  have fullBudget := receiptShape ▸ budget
  have storeStart : OwnerDemandWorld state.heap.metadata (code.child storeTerm) storeReceipt :=
    ⟨storeWorld.live_once,storeWorld.exclusive⟩
  obtain ⟨object,offset,heap,stored,indexStored,_,_,_,used,storeRun,metadata,owned,newCell,otherCells⟩ :=
    reachable_captured_store_owned_result program (fuel+1) value history evaluatingStore rfl storeTyped
      (context.child _) (enterHeap.symm ▸ sizes.child _) ((coverage.child _).same_frames enterFrames.symm)
      decideEvidence computed storeChecked fullBudget.sequence.1 (enterHeap.symm ▸ storeStart) storeTotal
  let returned : State := ⟨heap,.returned (.owner object),entered.stack,entered.pending⟩
  change run storeTicks entered = ⟨returned,[.store object offset (encodeInteger number)],storeTicks⟩ at storeRun
  have ownedAtReturn : OwnedResult env returned.heap.metadata returned.activeStack object
      ((code.child storeTerm).term.subst meanings) ((Term.buffer size).subst meanings) := owned
  have completed : (run storeTicks entered).state = returned := by
    have observed := congrArg Result.state storeRun
    exact observed
  have invariant : Invariant returned :=
    completed ▸ run_invariant storeTicks (initial_run_invariant program (fuel+1))
  have frame : returned.stack = .free next :: state.stack := congrArg State.stack enteredState
  have freeRun := free_operand_return returned invariant ownedAtReturn rfl frame
  have fullRun : run duration state = ⟨⟨⟨SizedBufferHeap.release state.heap.metadata object,heap.cell⟩,
      .evaluate next,state.stack,state.pending⟩,
      [.store object offset (encodeInteger number),.legacy (.heap (.free object))],duration⟩ := by
    rw [← enteredState] at started
    have combined := join_runs started (join_runs storeRun freeRun)
    have pending : returned.pending = state.pending := by
      have observed := congrArg State.pending enteredState
      exact observed
    rw [pending] at combined
    change returned.heap.metadata = entered.heap.metadata at metadata
    rw [metadata,enterHeap] at combined
    exact combined
  have noTail (alias : Nat) (found : code.values[alias]? = some (some (.owner object))) :
      residual.demand alias = some 0 := by
    have zero := disjoint owner alias object 0 stored found used
    cases observed : residual.demand alias with
    | none => simp [Control.demand,observed] at zero
    | some count => simpa [Control.demand,observed] using zero
  have wholeUse : receipt.demand owner = some 1 := by
    rw [receiptShape]
    simp [Control.demand,used,noTail owner stored]
  have siblingAlias (alias : Nat) (found : code.values[alias]? = some (some (.owner object))) :
      later.demand alias = some 0 :=
    separated owner alias object 0 stored found wholeUse
  have residualSeparation : OwnerDemandSeparation next residual later := by
    intro slot alias wanted uses found other demand
    obtain ⟨count,storeDemand⟩ := storeTotal slot wanted found
    have fullDemand : receipt.demand slot = some ((count+uses)+1) := by
      rw [receiptShape]
      simp [Control.demand,storeDemand,demand,Nat.add_assoc]
    exact separated slot alias wanted (count+uses) found other fullDemand
  have different {control : Jihoo.Quantity.Control} {slot wanted uses : Nat}
      (zero : ∀ alias, code.values[alias]? = some (some (.owner object)) → control.demand alias = some 0)
      (found : code.values[slot]? = some (some (.owner wanted))) (demand : control.demand slot = some (uses+1)) :
      wanted ≠ object := by
    rintro rfl
    rw [zero slot found] at demand
    cases demand
  have noRelease (wanted : Nat) (other : wanted ≠ object) :
      SizedBufferHeap.Event.free wanted ∉ (run duration state).events.filterMap Event.lifecycle? := by
    rw [fullRun]
    change SizedBufferHeap.Event.free wanted ∉ [SizedBufferHeap.Event.free object]
    exact fun member => other (SizedBufferHeap.Event.free.inj (List.mem_singleton.mp member))
  have tailStart : OwnerDemandWorld state.heap.metadata next residual := ⟨tailWorld.live_once,tailWorld.exclusive⟩
  have tailAfter := OwnerDemandWorld.run_without_demanded_free program fuel duration tailStart
    (fun _ wanted _ found demand => noRelease wanted (different noTail found demand))
  have siblingAfter := OwnerDemandWorld.run_without_demanded_free program fuel duration sibling
    (fun _ wanted _ found demand => noRelease wanted (different siblingAlias found demand))
  have frames : readerFrames (run duration state).state.activeStack = readerFrames state.activeStack := by
    rw [fullRun]
    rfl
  refine ⟨object,offset,heap,residual,stored,indexStored,fullRun,?_,tailTyped,context.child tail,
    reachable_run_owner_sizes program fuel duration sizes,slots.same_frames frames.symm,coverage.same_frames frames.symm,
    tailChecked,fullBudget.sequence.2.sequence.1,tailAfter,tailTotal,noTail,residualSeparation,siblingAfter,?_⟩
  · rw [fullRun]
    exact newCell
  · intro slot wanted uses found demand
    have other := different siblingAlias found demand
    refine ⟨noRelease wanted other,fun cell => ?_⟩
    rw [fullRun]
    exact (otherCells wanted cell (.inl other)).trans (congrArg (fun h : SizedBufferHeap.IndexedState => h.cell wanted cell) enterHeap)

namespace Examples

private def dynamicStoreCleanup : Term :=
  let buffer := Term.buffer (.natural 2)
  let bound := Term.decide (.natural 1) (.natural 2)
  let value := IntegerOperand.arithmetic .add (.captured 3)
    (.arithmetic .mul (.literal 2) (.literal 3))
  let cleanup := Term.free (.store (.var 1) (.var 4) value.term (.var 2)) (.integer 0)
  let release := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let body := Term.load (.var 0) (.natural 1) bound release
  let call := Term.app (.strict cleanup (.lam false buffer body)) (.var 0)
  let target := Term.store (.alloc (.natural 2) (.integer 3)) (.natural 1) (.integer 7) bound
  let withTarget := Term.app (.lam false buffer call) target
  let withTemporary := Term.app (.lam false buffer withTarget) (.alloc (.natural 2) (.integer 0))
  let branch := Term.ifLt (.var 1) (.natural 2) withTemporary (.integer 0)
  .app (.lam false .u64 (.app (.lam false .i64 branch) (.integer 40))) (.natural 1)

set_option maxRecDepth 4096 in
/-- Captured values, branch evidence and a nested signed computation drive
the callee Store. The pending sibling still observes its own original cell. -/
theorem computed_callee_dynamic_store_preserves_argument :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,dynamicStoreCleanup⟩ =
      some ⟨.i64,dynamicStoreCleanup⟩ ∧
    let result := run 90 (initial dynamicStoreCleanup)
    observe result = .integer 7 ∧ result.state.heap.metadata.heap.nextObject = 2 ∧
      result.state.heap.metadata.heap.live 0 = false ∧ result.state.heap.metadata.heap.live 1 = false ∧
      decodeInteger (result.state.heap.cell 0 1) = 46 ∧ decodeInteger (result.state.heap.cell 1 1) = 7 := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
