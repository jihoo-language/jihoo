import Jihoo.NativeBindingMachineMutableComputedLoad

/-! Computed Store operands execute under the real indexed-heap frames.
The closed bound relates the observed word to the allocation's size. -/
namespace Jihoo.NativeKernel.Environment.BindingMachine.Mutable
open Jihoo.Quantity NativeQuantity CodeKinds

/-- The machine evaluates the typed operands in order, passing the returned
index to the saved value frame. It writes once and returns the same owner to
the original continuation. Both operand runs are silent. -/
theorem named_store_operand_runs (state : State)
    (evaluating : state.control = .evaluate code)
    (shape : code.term = .store (.var owner) index value evidence)
    (stored : code.values[owner]? = some (some (.owner object)))
    (indexRun : run indexTicks ⟨state.heap,.evaluate (code.child index),[],
      (.index object (code.child value),state.stack) :: state.pending⟩ =
      ⟨⟨state.heap,.returned (.natural offset),[],(.index object (code.child value),state.stack) :: state.pending⟩,
        [],indexTicks⟩)
    (valueRun : run valueTicks ⟨state.heap,.evaluate (code.child value),[],
      (.value object offset,state.stack) :: state.pending⟩ =
      ⟨⟨state.heap,.returned (.integer number),[],(.value object offset,state.stack) :: state.pending⟩,[],valueTicks⟩)
    (written : state.heap.store object offset (encodeInteger number) = some heap) :
    let duration := 3+(indexTicks+(1+(valueTicks+1)))
    run duration state = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
      [.store object offset (encodeInteger number)],duration⟩ := by
  have entry : run 3 state = ⟨⟨state.heap,.evaluate (code.child index),[],
      (.index object (code.child value),state.stack) :: state.pending⟩,[],3⟩ := by
    simp only [run,step,evaluating,shape,Code.child,evaluateAction,stored,executeLegacy,execute,
      returnAction,resumeBuffer,Option.map_none]
    rfl
  have advance : run 1 ⟨state.heap,.returned (.natural offset),[],
      (.index object (code.child value),state.stack) :: state.pending⟩ =
      ⟨⟨state.heap,.evaluate (code.child value),[],(.value object offset,state.stack) :: state.pending⟩,[],1⟩ := rfl
  let returned : State := ⟨state.heap,.returned (.integer number),[],(.value object offset,state.stack) :: state.pending⟩
  have selected := (pending_store_executes returned rfl rfl rfl written).1
  have finish : run 1 returned = ⟨⟨heap,.returned (.owner object),state.stack,state.pending⟩,
      [.store object offset (encodeInteger number)],1⟩ := by
    rw [run,selected]
    rfl
  exact join_runs entry (join_runs indexRun (join_runs advance (join_runs valueRun finish)))

/-- A successful U64 index expression and signed value expression produce
an exact indexed Store. The original source type and quantity projection
select the physical owner and justify the native write, preserving all
metadata, suspended loans, and every old lease's observation. -/
theorem reachable_computed_store_owned_result (program : Term) (fuel : Nat)
    (index : UnsignedOperand) (value : IntegerOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .store (.var owner) index.term value.term evidence)
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computedIndex : index.value meanings = some offset)
    (computedValue : value.value meanings = some number)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let duration := 3+(index.ticks+(1+(value.ticks+1)))
    ∃ object heap,
      code.values[owner]? = some (some (.owner object)) ∧ receipt.demand owner = some 1 ∧
      offset < 2^64 ∧ offset < before.heap.metadata.length object ∧
      before.heap.store object offset (encodeInteger number) = some heap ∧
      run duration before = ⟨⟨heap,.returned (.owner object),before.stack,before.pending⟩,
        [.store object offset (encodeInteger number)],duration⟩ ∧
      heap.metadata = before.heap.metadata ∧
      OwnedResult env heap.metadata before.activeStack object (code.term.subst meanings) type ∧
      decodeInteger (heap.cell object offset) = number ∧
      (∀ queried cell, queried ≠ object ∨ cell ≠ offset → heap.cell queried cell = before.heap.cell queried cell) ∧
      ∀ token cell, heap.read token cell = before.heap.read token cell := by
  let before := (run fuel (initial program)).state
  have closed := typed.closed history
  obtain ⟨closing,localType,sourceTyped,converted⟩ := typed
  rw [shape] at sourceTyped
  obtain ⟨size,ownerTyped,indexTyped,valueTyped,evidenceTyped,principal⟩ := sourceTyped.store_inputs
  have aligned := initial_run_code_aligned program fuel SizedBufferHeap.empty evaluating
  have ownerClosing : LoanClosingTyped env loans false (code.child (.var owner)) meanings ((Term.buffer size).subst meanings) :=
    ⟨closing,.buffer size,ownerTyped,.refl _⟩
  obtain ⟨runtimeOwner,stored,kind⟩ := (context.child _).variable_kind history ownerClosing (aligned.child _) rfl
  have buffer : ValueKind env runtimeOwner (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using kind
  obtain ⟨object,rfl⟩ := buffer_kind_is_owner history.wellFormed.admissible buffer
  obtain ⟨indexReceipt,valueReceipt,indexProjected,_,_⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_named_store_operands (shape ▸ checked)
  have indexClosing : LoanClosingTyped env loans false (code.child (index.term.rename id)) meanings .u64 := by
    rw [Term.rename_id]
    refine ⟨closing,.u64,indexTyped,?_⟩
    simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .u64 .u64 from .refl _)
  have indexChecked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans code.context
      (index.term.rename id) = some indexReceipt := by rwa [Term.rename_id]
  obtain ⟨width,convertedOffset,_,indexRun⟩ := index.checked_run history (CanonicalView.identity code)
    indexClosing context aligned indexChecked computedIndex
  rw [Term.rename_id] at convertedOffset
  have ownerSize : OwnerSize env before.heap.metadata object (.buffer (size.subst meanings)) := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using sizes.typed_variable history ownerTyped stored
  have evidenceClosed : LoanTyping.HasType env [] [] true (.decide left right)
      (.lt (index.term.subst meanings) (size.subst meanings)) := by
    simpa only [decideEvidence,Term.subst,substArgs,Op.binders,liftSub] using evidenceTyped.ghostSubstitution history.wellFormed closing
  have within := evidenceClosed.decide_converted_bound history.wellFormed.admissible convertedOffset (ownerSize.buffer_length history)
  have use := named_store_use (shape ▸ checked) world complete stored
  have inactive : Loans.active code.context.length loans owner = false := by
    apply Bool.eq_false_iff.mpr
    intro active
    have zero := budget owner active
    rw [use] at zero
    cases zero
  have live := (world.live_once owner object 0 stored use).1
  change before.heap.metadata.heap.live object = true at live
  have noReaders := coverage.inactive stored inactive
  have invariant := initial_run_invariant program fuel
  have guard := (invariant.2.free_guard_iff invariant.1).mpr noReaders
  change freeGuard before.heap.metadata object = true at guard
  let heap : SizedBufferHeap.IndexedState := { before.heap with
    cell := HeapLeases.put before.heap.cell object (HeapLeases.put (before.heap.cell object) offset (encodeInteger number)) }
  have written : before.heap.store object offset (encodeInteger number) = some heap := by
    simp [SizedBufferHeap.IndexedState.store,live,guard,within,heap]
  obtain ⟨_,_,_,metadata,newCell,otherCells⟩ := SizedBufferHeap.IndexedState.store_spec invariant.1 written
  have resultType : LoanTyping.Conversion.Conv env (.buffer (size.subst meanings)) type := by
    simpa only [Term.subst,substArgs,Op.binders,liftSub] using
      (principal.substitution meanings history.wellFormed.closed).trans converted
  have owned : OwnedResult env heap.metadata before.activeStack object (code.term.subst meanings) type :=
    ⟨closed,metadata.symm ▸ ownerSize.convert resultType,metadata.symm ▸ live,noReaders⟩
  have valueClosing : LoanClosingTyped env loans false (code.child value.term) meanings .i64 :=
    ⟨closing,.i64,valueTyped,by
      simpa only [Term.subst,substArgs] using (show LoanTyping.Conversion.Conv env .i64 .i64 from .refl _)⟩
  obtain ⟨bounded,valueRun⟩ := value.checked_run history valueClosing context aligned computedValue before.heap []
    ((.value object offset,before.stack) :: before.pending)
  have executed := named_store_operand_runs before evaluating shape stored
    (indexRun before.heap [] ((.index object (code.child value.term),before.stack) :: before.pending)) valueRun written
  refine ⟨object,heap,stored,use,width,within,written,executed,metadata,owned,?_,otherCells,
    SizedBufferHeap.IndexedState.store_keeps_reader invariant.1 written⟩
  rw [newCell]
  exact encode_decode_integer bounded

private theorem begin_store_argument (state : State) (evaluating : state.control = .evaluate code)
    (shape : code.term = .app (.lam false domain body) argument) :
    let argumentCode := code.child argument
    let saved := Frame.argument (.closure false domain body code.context code.origins code.values) argumentCode.origin
    run 3 state = ⟨⟨state.heap,.evaluate argumentCode,saved :: state.stack,state.pending⟩,[],3⟩ := by
  simp only [run,step,evaluating,shape,evaluateAction,Code.child,returnAction,executeLegacy,execute,
    Option.map_none]
  rfl

/-- A checked lambda application evaluates its computed Store argument,
then installs that same physical owner in its actual saved closure. The
original body inherits the exact owned value, dependent type and loan and
quantity receipts. Captured aliases of the argument have no body demand. -/
theorem reachable_computed_store_buffer_call (program : Term) (fuel : Nat)
    (index : UnsignedOperand) (value : IntegerOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .app (.lam false (.buffer count) body) (.store (.var owner) index.term value.term evidence))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computedIndex : index.value meanings = some offset)
    (computedValue : value.value meanings = some number)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+3) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let storeTicks := 3+(index.ticks+(1+(value.ticks+1)))
    let duration := 3+(storeTicks+1)
    let argument := Term.store (.var owner) index.term value.term evidence
    let origin := (code.child argument).origin
    let nextMeanings := consValues (argument.subst meanings) meanings
    ∃ object heap,
      let next := enter false (.buffer count) body code.context code.origins code.values origin (some (.owner object))
      code.values[owner]? = some (some (.owner object)) ∧
      run duration before = ⟨⟨heap,.evaluate next,before.stack,before.pending⟩,
        [.store object offset (encodeInteger number),.legacy (.activate false body origin)],duration⟩ ∧
      heap.metadata = before.heap.metadata ∧ heap.cell object offset = encodeInteger number ∧
      decodeInteger (heap.cell object offset) = number ∧
      (∀ queried cell, queried ≠ object ∨ cell ≠ offset → heap.cell queried cell = before.heap.cell queried cell) ∧
      (∀ token cell, heap.read token cell = before.heap.read token cell) ∧
      LoanClosingTyped env loans false next nextMeanings type ∧ ValueContext env next nextMeanings ∧
      OwnerSizes env heap.metadata next nextMeanings ∧
      LoanSlots next loans before.activeStack ∧ LoanCoverage next loans before.activeStack ∧
      ∃ bodyReceipt,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+2) env loans next.context next.term = some bodyReceipt ∧
        LoanTyping.ResourceQuantity.LoanBudget next.context.length loans bodyReceipt ∧
        OwnerDemandWorld heap.metadata next bodyReceipt ∧ OwnerDemandWorld.Total next bodyReceipt ∧
        bodyReceipt.demand 0 = some 1 ∧
        ∀ alias, code.values[alias]? = some (some (.owner object)) → bodyReceipt.demand (alias+1) = some 0 := by
  let before := (run fuel (initial program)).state
  let argument := Term.store (.var owner) index.term value.term evidence
  let argumentCode := code.child argument
  let domain := Term.buffer count
  let origin := argumentCode.origin
  let frame := Frame.argument (.closure false domain body code.context code.origins code.values) origin
  let stage : State := ⟨before.heap,.evaluate argumentCode,frame :: before.stack,before.pending⟩
  have started : run 3 before = ⟨stage,[],3⟩ := begin_store_argument before evaluating shape
  have reached : (run (fuel+3) (initial program)).state = stage := by
    have observed := congrArg Result.state (run_add fuel 3 (initial program))
    change (run (fuel+3) (initial program)).state = (run 3 before).state at observed
    rw [started] at observed
    exact observed
  have selecting : (run (fuel+3) (initial program)).state.control = .evaluate argumentCode := by rw [reached]
  have sameFrames : readerFrames stage.activeStack = readerFrames before.activeStack := rfl
  obtain ⟨bodyType,argumentSource,bodySource,resultType⟩ := original_buffer_call_inputs history typed shape
  have argumentTyped : LoanClosingTyped env loans false argumentCode meanings (domain.subst meanings) :=
    ⟨typed.1,domain,argumentSource,.refl _⟩
  obtain ⟨argumentReceipt,bodyReceipt,argumentChecked,bodyChecked,shapeReceipt⟩ :=
    LoanTyping.ResourceQuantity.projectRaw_buffer_call history.wellFormed.admissible (shape ▸ checked)
  obtain ⟨argumentWorld,argumentTotal,_,_,_⟩ := (shapeReceipt ▸ world).sequence (shapeReceipt ▸ complete)
  obtain ⟨storeWorld,storeTotal,_,_,_⟩ := argumentWorld.sequence argumentTotal
  have storeStart : OwnerDemandWorld stage.heap.metadata argumentCode argumentReceipt :=
    ⟨storeWorld.live_once,storeWorld.exclusive⟩
  have fullBudget := shapeReceipt ▸ budget
  have startCoverage := (coverage.child argument).same_frames sameFrames.symm
  obtain ⟨object,heap,stored,used,_,_,written,storeRun,metadata,owned,newCell,otherCells,oldReaders⟩ :=
    reachable_computed_store_owned_result program (fuel+3) index value history selecting rfl argumentTyped
      (context.child argument) (reached.symm ▸ sizes.child argument) (reached.symm ▸ startCoverage)
      decideEvidence computedIndex computedValue argumentChecked fullBudget.sequence.1.sequence.1
      (reached.symm ▸ storeStart) storeTotal
  rw [reached] at written storeRun metadata owned otherCells oldReaders
  let returned : State := ⟨heap,.returned (.owner object),frame :: before.stack,before.pending⟩
  let next := enter false domain body code.context code.origins code.values origin (some (.owner object))
  have selected := enter_retained_call_step returned code domain body origin (.owner object) rfl (by rfl)
  dsimp only at selected
  have activated : run 1 returned = ⟨⟨heap,.evaluate next,before.stack,before.pending⟩,
      [.legacy (.activate false body origin)],1⟩ := by
    rw [run,selected]
    rfl
  have entire := join_runs started (join_runs storeRun activated)
  have unborrowed : ¬ ObjectReader object before.activeStack := by
    rintro ⟨saved,member,token,name,description⟩
    exact owned.noReaders ⟨saved,List.mem_cons_of_mem frame member,token,name,description⟩
  have kind : ValueKind env (.owner object) (domain.subst meanings) :=
    ⟨.natural (heap.metadata.length object),owned.size.realization⟩
  obtain ⟨nextContext,nextSizes⟩ := bind_variable_context context (metadata.symm ▸ sizes) owned.typed kind
    (fun _ same => by cases same; exact owned.size)
    (by intro _ impossible; cases impossible) (by intro _ impossible; cases impossible) body origin
  have nextTyped : LoanClosingTyped env loans false next (consValues (argument.subst meanings) meanings) type :=
    ⟨nextContext.closing,bodyType,bodySource,resultType⟩
  have argumentUse : (Control.seq argumentReceipt .pure).demand owner = some 1 := by simp [Control.demand,used]
  obtain ⟨nextWorld,nextTotal,one,aliases⟩ :=
    (shapeReceipt ▸ world).enter_linear_owner (shapeReceipt ▸ complete) stored argumentUse domain body origin
  have bytes := (SizedBufferHeap.IndexedState.store_spec (initial_run_invariant program fuel).1 written).2.2.2.2.1
  exact ⟨object,heap,stored,entire,metadata,bytes,newCell,otherCells,oldReaders,nextTyped,nextContext,nextSizes,
    slots.enter entered false domain body origin (some (.owner object)),
    coverage_enter_unborrowed_owner coverage entered unborrowed domain body origin,
    bodyReceipt,bodyChecked,fullBudget.sequence.2.scope entered,metadata.symm ▸ nextWorld,nextTotal,one,aliases⟩

namespace UnsignedOperand

def rename (indices : Nat → Nat) : UnsignedOperand → UnsignedOperand
  | .literal number => .literal number
  | .captured slot => .captured (indices slot)
  | .add left right => .add (rename indices left) (rename indices right)

theorem rename_value (operand : UnsignedOperand) (indices : Nat → Nat) (meanings : Nat → Term) :
    (operand.rename indices).value meanings = operand.value (meanings ∘ indices) := by
  induction operand with
  | literal number => rfl
  | captured slot => rfl
  | add left right leftValue rightValue => simp only [rename,value,leftValue,rightValue]

end UnsignedOperand

/-- The checked application writes through its computed Store argument,
binds that same owner, reads the same cell with the shifted index and bound
proof, and releases the owner in the actual Load callback. The successor
inherits the original dependent tail type and all remaining loan and owner
receipts. Both indexes are authenticated by the same occurrence tree. -/
theorem reachable_computed_store_load_free (program : Term) (fuel : Nat)
    (index : UnsignedOperand) (value : IntegerOperand)
    (history : LoanTyping.MixedProgram.History definitions familyDeclarations env)
    (evaluating : (run fuel (initial program)).state.control = .evaluate code)
    (shape : code.term = .app (.lam false (.buffer count)
      (.load (.var 0) (index.rename Nat.succ).term (evidence.rename Nat.succ)
        (.lam false first (.lam false again (.free (.var 0) tail)))))
      (.store (.var owner) index.term value.term evidence))
    (typed : LoanClosingTyped env loans false code meanings type) (context : ValueContext env code meanings)
    (sizes : OwnerSizes env (run fuel (initial program)).state.heap.metadata code meanings)
    (slots : LoanSlots code loans (run fuel (initial program)).state.activeStack)
    (coverage : LoanCoverage code loans (run fuel (initial program)).state.activeStack)
    (entered : Loans.Entered code.context.length loans)
    (decideEvidence : evidence.subst meanings = .decide left right)
    (computedIndex : index.value meanings = some offset)
    (computedValue : value.value meanings = some number)
    (checked : LoanTyping.ResourceQuantity.projectRaw (resourceFuel+6) env loans code.context code.term = some receipt)
    (budget : LoanTyping.ResourceQuantity.LoanBudget code.context.length loans receipt)
    (world : OwnerDemandWorld (run fuel (initial program)).state.heap.metadata code receipt)
    (complete : OwnerDemandWorld.Total code receipt) :
    let before := (run fuel (initial program)).state
    let storeTicks := 3+(3+(index.ticks+(1+(value.ticks+1)))+1)
    let loadTicks := (3+((index.rename Nat.succ).ticks+5))+3
    let argument := Term.store (.var owner) index.term value.term evidence
    let origin := (code.child argument).origin
    let callback := Term.free (.var 0) tail
    let loadBody := Term.load (.var 0) (index.rename Nat.succ).term (evidence.rename Nat.succ)
      (.lam false first (.lam false again callback))
    let result := run (storeTicks+loadTicks) before
    ∃ (object : Nat) (written : SizedBufferHeap.IndexedState),
      let entry := enter false (.buffer count) loadBody code.context code.origins code.values origin (some (.owner object))
      let sourceTail := (restoredContinuation entry first again callback origin (.integer number) object (.integer number)).child tail
      let sourceOwner := argument.subst meanings
      let tailMeanings := consValues sourceOwner (consValues (.integer number) (consValues sourceOwner meanings))
      code.values[owner]? = some (some (.owner object)) ∧
      result = ⟨⟨⟨SizedBufferHeap.release before.heap.metadata object,written.cell⟩,
        .evaluate sourceTail,before.stack,before.pending⟩,
        [.store object offset (encodeInteger number),.legacy (.activate false loadBody origin),
          .load object offset (encodeInteger number),.legacy (.activate false (.lam false again callback) (.integer number)),
          .legacy (.activate false callback origin),.legacy (.heap (.free object))],storeTicks+loadTicks⟩ ∧
      result.state.heap.metadata.heap.live object = false ∧ result.state.heap.cell object offset = encodeInteger number ∧
      (∀ queried cell, queried ≠ object ∨ cell ≠ offset → result.state.heap.cell queried cell = before.heap.cell queried cell) ∧
      LoanClosingTyped env loans false sourceTail tailMeanings type ∧ ValueContext env sourceTail tailMeanings ∧
      OwnerSizes env result.state.heap.metadata sourceTail tailMeanings ∧
      LoanSlots sourceTail loans result.state.activeStack ∧ LoanCoverage sourceTail loans result.state.activeStack ∧
      ∃ residual,
        LoanTyping.ResourceQuantity.projectRaw (resourceFuel+1) env loans sourceTail.context sourceTail.term = some residual ∧
        LoanTyping.ResourceQuantity.LoanBudget sourceTail.context.length loans residual ∧
        OwnerDemandWorld result.state.heap.metadata sourceTail residual ∧ OwnerDemandWorld.Total sourceTail residual ∧
        ∀ alias, sourceTail.values[alias]? = some (some (.owner object)) → residual.demand alias = some 0 := by
  let before := (run fuel (initial program)).state
  let storeTicks := 3+(3+(index.ticks+(1+(value.ticks+1)))+1)
  let loadIndex := index.rename Nat.succ
  let loadTicks := (3+(loadIndex.ticks+5))+3
  let argument := Term.store (.var owner) index.term value.term evidence
  let origin := (code.child argument).origin
  let callback := Term.free (.var 0) tail
  let loadBody := Term.load (.var 0) loadIndex.term (evidence.rename Nat.succ) (.lam false first (.lam false again callback))
  let argumentMeaning := argument.subst meanings
  let nextMeanings := consValues argumentMeaning meanings
  obtain ⟨object,heap,stored,storeRun,metadata,bytes,decoded,otherCells,_,nextTyped,nextContext,
    nextSizes,nextSlots,nextCoverage,bodyReceipt,bodyChecked,bodyBudget,bodyWorld,bodyTotal,_,_⟩ :=
    reachable_computed_store_buffer_call (resourceFuel := resourceFuel+3) program fuel index value history evaluating shape
      typed context sizes slots coverage entered decideEvidence computedIndex computedValue checked budget world complete
  let entry := enter false (.buffer count) loadBody code.context code.origins code.values origin (some (.owner object))
  let atBody : State := ⟨heap,.evaluate entry,before.stack,before.pending⟩
  change run storeTicks before = ⟨atBody,[.store object offset (encodeInteger number),
    .legacy (.activate false loadBody origin)],storeTicks⟩ at storeRun
  have reached : (run (fuel+storeTicks) (initial program)).state = atBody := by
    have observed := congrArg Result.state (run_add fuel storeTicks (initial program))
    change (run (fuel+storeTicks) (initial program)).state = (run storeTicks before).state at observed
    rw [storeRun] at observed
    exact observed
  have selecting : (run (fuel+storeTicks) (initial program)).state.control = .evaluate entry := by rw [reached]
  have aligned := initial_run_code_aligned program (fuel+storeTicks) SizedBufferHeap.empty selecting
  have deeper : Loans.Entered entry.context.length loans := by
    intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  have loadComputed : loadIndex.value (nextMeanings ∘ id) = some offset := by
    change (index.rename Nat.succ).value nextMeanings = some offset
    rw [UnsignedOperand.rename_value]
    exact computedIndex
  have loadProof : (evidence.rename Nat.succ).subst (nextMeanings ∘ id) = .decide left right := by
    change (evidence.rename Nat.succ).subst (consValues argumentMeaning meanings) = _
    simpa only [shift_subst_consValues] using decideEvidence
  obtain ⟨loadedObject,selected,_,loadRun,dead,_,tailTyped,tailContext,tailSizes,tailSlots,tailCoverage,
    residual,tailChecked,tailBudget,tailWorld,tailTotal,noAliases⟩ :=
    reachable_computed_load_then_free program (fuel+storeTicks) loadIndex history selecting (CanonicalView.identity entry)
      nextTyped nextContext aligned (reached.symm ▸ nextSizes) (reached.symm ▸ nextSlots)
      (reached.symm ▸ nextCoverage) deeper rfl loadProof loadComputed bodyChecked bodyBudget (reached.symm ▸ bodyWorld) bodyTotal
  have same : object = loadedObject := Value.owner.inj (Option.some.inj (Option.some.inj selected))
  subst loadedObject
  rw [reached] at loadRun dead tailTyped tailContext tailSizes tailSlots tailCoverage tailChecked tailBudget tailWorld tailTotal noAliases
  have sameOrigin : (entry.child (.var 0)).origin = origin := by
    simp only [entry,enter,Code.child,Code.origin,Term.subst,consValues]
  have readDecoded : decodeInteger (atBody.heap.cell object offset) = number := decoded
  have readBytes : atBody.heap.cell object offset = encodeInteger number := bytes
  simp only [liftRenaming_id,Term.rename_id,id_eq,sameOrigin,readDecoded]
    at loadRun tailTyped tailContext tailSizes tailSlots tailCoverage tailChecked tailBudget tailWorld tailTotal noAliases
  rw [readBytes] at loadRun
  have combined := join_runs storeRun loadRun
  have sameMetadata : atBody.heap.metadata = before.heap.metadata := metadata
  rw [sameMetadata] at combined
  have finalState : (run (storeTicks+loadTicks) before).state = (run loadTicks atBody).state := by
    have observed := congrArg Result.state (run_add storeTicks loadTicks before)
    dsimp only at observed
    rw [storeRun] at observed
    exact observed
  refine ⟨object,heap,stored,combined,finalState.symm ▸ dead,?_,?_,tailTyped,tailContext,
    finalState.symm ▸ tailSizes,finalState.symm ▸ tailSlots,finalState.symm ▸ tailCoverage,residual,
    tailChecked,tailBudget,finalState.symm ▸ tailWorld,tailTotal,noAliases⟩
  · rw [combined]
    exact bytes
  · intro queried cell other
    rw [combined]
    exact otherCells queried cell other

namespace Examples

private def computedOwnedStoreLoad : Term :=
  let buffer := Term.buffer (.natural 3)
  let index := fun slot => UnsignedOperand.add (.captured slot) (.add (.literal 1) (.literal 0))
  let value := IntegerOperand.arithmetic .add (.captured 2) (.arithmetic .mul (.literal 2) (.literal 3))
  let written := Term.store (.var 0) (index 3).term value.term (.var 1)
  let continuation := Term.lam false .i64 (.lam false buffer (.free (.var 0) (.var 1)))
  let loaded := Term.load (.var 0) (index 4).term (.var 2) continuation
  let afterAllocation := Term.app (.lam false buffer loaded) written
  let selected := Term.app (.lam false buffer afterAllocation) (.alloc (.natural 3) (.integer 3))
  let branch := Term.ifLt (index 1).term (.natural 3) selected (.integer 0)
  .app (.lam false .u64 (.app (.lam false .i64 branch) (.integer 40))) (.natural 1)

set_option maxRecDepth 4096 in
/-- The same compound index is computed for both Store and Load, and the
actual closure argument returned by Store supplies the owner consumed by Free. -/
theorem computed_store_load_free_same_cell :
    LoanTyping.MixedProgram.checkDeclaration 64 128 .empty ⟨.i64,computedOwnedStoreLoad⟩ =
      some ⟨.i64,computedOwnedStoreLoad⟩ ∧
    let result := run 100 (initial computedOwnedStoreLoad)
    observe result = .integer 46 ∧
      result.events.filterMap (fun event => match event with
        | .store object offset payload | .load object offset payload => some (object,offset,payload)
        | _ => none) = [(0,2,encodeInteger 46),(0,2,encodeInteger 46)] ∧
      result.events.filterMap Event.lifecycle? = [.alloc 0 3 (encodeInteger 3),.free 0] ∧
      result.state.heap.metadata.heap.live 0 = false := by
  refine ⟨?_,?_⟩
  · cbv
  · exact ⟨rfl,rfl,rfl,rfl⟩

end Examples

end Jihoo.NativeKernel.Environment.BindingMachine.Mutable
